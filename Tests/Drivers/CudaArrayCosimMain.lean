import Sparkle.Backend.CudaArray
import Tests.CudaArrayFixtures

/-  Regular-array CUDA backend — detection checks + co-simulation.

    For every fixture:
      1. `analyzeArray` must classify it as expected (topology, rank, shape);
         rejection fixtures must fail with the expected reason.
      2. The emitted `.cu` gets a generated `main` that runs the SAME
         stimulus through
           (a) CSim's sequential `eval_tick` on the host   (JIT semantics),
           (b) CSim's `eval` + `tick` on the host          (relaxed eval),
           (c) the array kernels via the public JIT API,
         for every schedule (auto / single-block / per-cycle step), both
         cycle-by-cycle and as one multi-cycle launch, comparing every top
         output AND every register of every cell.
      3. Execution backends:
           - nvcc present            → `nvcc -c` compile check (sm_80) + link;
           - g++ present             → run on the CPU CUDA emulator
                                       (tools/cuda_emu, fibers for __syncthreads);
           - SPARKLE_CUDA=1 + GPU    → run the nvcc binary on the device.
-/

open Sparkle.Backend.CudaArray
open Sparkle.Backend.CSim
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Test.CudaArray

structure Case where
  name      : String
  design    : Design
  /-- substring the plan description must contain -/
  expect    : String
  /-- (pokes, cycles) phases -/
  phases    : List (List (String × Nat) × Nat)
  blockFits : Bool := true

def u32 (i : Int) : Nat := (((i % 4294967296) + 4294967296) % 4294967296).toNat

def meshCase (n : Nat) (expect : String) (fits : Bool := true) : Case :=
  let w := (List.range n).flatMap fun i => (List.range n).map fun j =>
    (s!"w_{i}_{j}", u32 (Int.ofNat ((i*7 + j*3) % 5) - 2))
  let a1 := (List.range n).map fun i => (s!"ain_{i}", u32 (Int.ofNat (i % 8) - 3))
  let a2 := (List.range n).map fun i => (s!"ain_{i}", (i * 5 + 1) % 9)
  { name := s!"mesh{n}", design := meshDesign n, expect, blockFits := fits
  , phases := [(a1 ++ w, 2 * n + 3), (a2, n + 2)] }

def firCase (rows taps : Nat) (expect : String) : Case :=
  let c := (List.range rows).flatMap fun r => (List.range taps).map fun t =>
    (s!"c_{r}_{t}", (r * 3 + t * 5 + 1) % 7)
  { name := s!"fir{rows}x{taps}", design := firDesign rows taps, expect
  , phases := [ ((List.range rows).map (fun r => (s!"x_{r}", 3 + r)) ++ c, taps + 3)
              , ((List.range rows).map (fun r => (s!"x_{r}", 60000 + r)), taps + 1) ] }

def pixCase (rows cols : Nat) (expect : String) : Case :=
  let px (k : Nat) := (List.range rows).flatMap fun r => (List.range cols).map fun c =>
    (s!"p_{r}_{c}", (r * 37 + c * 11 + k * 101) % 256)
  { name := s!"pix{rows}x{cols}", design := pixDesign rows cols, expect
  , phases := [(("gain", 3) :: px 0, 6), (("gain", 1) :: px 1, 5)] }

/-- Glider + blinker seed, then free-running generations. -/
def lifeCase (n : Nat) (expect : String) : Case :=
  let live : List (Nat × Nat) := [(0,1), (1,2), (2,0), (2,1), (2,2), (6,6), (6,7), (6,8)]
  let seeds := (List.range n).flatMap fun r => (List.range n).map fun c =>
    (s!"s_{r}_{c}", if live.contains (r, c) then 1 else 0)
  { name := s!"life{n}", design := lifeDesign n, expect
  , phases := [(("load", 1) :: seeds, 1), ([("load", 0)], 3 * n)] }

def cases : List Case :=
  [ meshCase 2 "connected 2-D array 2x2"
  , meshCase 16 "connected 2-D array 16x16"
  , meshCase 36 "connected 2-D array 36x36" (fits := false)
  , firCase 1 24 "connected 1-D array 24"
  , firCase 4 8 "connected 2-D array 8x4"
  , pixCase 20 36 "independent 2-D array 36x20"
  , lifeCase 12 "connected 2-D array 12x12" ]

def rejections : List (String × Design × String) :=
  [ ("mealy chain", mealyChainDesign, "Mealy neighbour link")
  , ("irregular link", irregularDesign, "fixed lattice offset")
  , ("heterogeneous", heteroDesign, "heterogeneous top")
  , ("top register", topRegDesign, "top-level register") ]

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-! ### Generated C main -/

def inputSlots (top : Module) : List (String × Nat) := Id.run do
  let mut acc : List (String × Nat) := []
  let mut k := 0
  for p in top.inputs do
    if p.name == "clk" then continue
    acc := acc ++ [(p.name, k)]
    k := k + (if p.ty.bitWidth > 64 then (p.ty.bitWidth + 31) / 32 else 1)
  return acc

def outputSlots (top : Module) : List (String × Nat) := Id.run do
  let mut acc : List (String × Nat) := []
  let mut k := 0
  for p in top.outputs do
    acc := acc ++ [(p.name, k)]
    k := k + (if p.ty.bitWidth > 64 then (p.ty.bitWidth + 31) / 32 else 1)
  return acc

def cosimMain (c : Case) (plan : ArrayPlan) : String := Id.run do
  let top := plan.top
  let topC := sanitizeName top.name
  let cellC := sanitizeName plan.cell.name
  let tst := s!"struct {topC}"
  let inSlots := inputSlots top
  let outSlots := outputSlots top
  let regs := plan.cell.body.filterMap fun s => match s with
    | .register o .. => some (sanitizeName o) | _ => none
  -- register-state table: offset + size of every cell register
  let regEntries := plan.cellField.toList.flatMap fun f => regs.map fun r =>
    s!"  \{ offsetof({tst}, {f}) + offsetof(struct {cellC}, {r}), sizeof((({tst}*)0)->{f}.{r}), \"{f}.{r}\" },"
  let mut phaseFns : List String := []
  let mut k := 0
  for (pokes, _) in c.phases do
    let refL := pokes.map fun (nm, v) => s!"  r->{sanitizeName nm} = {v}ull;"
    let gpuL := pokes.map fun (nm, v) =>
      s!"  jit_cuda_set_input(h, 0, {(inSlots.lookup nm).getD 9999}, {v}ull);"
    phaseFns := phaseFns ++
      [s!"static void poke_ref_{k}({tst}* r) \{"] ++ refL ++ ["}"] ++
      [s!"static void poke_gpu_{k}(void* h) \{"] ++ gpuL ++ ["}"]
    k := k + 1
  let outCmp := outSlots.map fun (nm, slot) =>
    s!"  if ((unsigned long long)r->{sanitizeName nm} != jit_cuda_get_output(h, 0, {slot})) \{ if (bad++ < 3 && loud) printf(\"  [%s c=%ld] output {nm}: gpu=%llu ref=%llu\\n\", tag, c, jit_cuda_get_output(h, 0, {slot}), (unsigned long long)r->{sanitizeName nm}); }"
  let phaseArr (pre : String) := String.intercalate ", " ((List.range c.phases.length).map fun i => s!"{pre}_{i}")
  let cycArr := String.intercalate ", " (c.phases.map fun (_, n) => toString n)
  let modes := if plan.topology == .connected then "{0, 1, 2}" else "{0}"
  let nModes := if plan.topology == .connected then 3 else 1
  return String.intercalate "\n" <|
    [ ""
    , "// ── Generated co-simulation main ─────────────────────────────────"
    , "#include <ctime>"
    , "#include <cstdlib>"
    , "typedef struct { size_t off; size_t size; const char* name; } RegEnt;"
    , s!"static const RegEnt reg_tab[] = \{" ] ++ regEntries ++
    [ "  { 0, 0, 0 } };"
    ] ++ phaseFns ++
    [ s!"typedef void (*PokeRef)({tst}*); typedef void (*PokeGpu)(void*);"
    , s!"static const PokeRef poke_ref[] = \{ {phaseArr "poke_ref"} };"
    , s!"static const PokeGpu poke_gpu[] = \{ {phaseArr "poke_gpu"} };"
    , s!"static const long phase_cycles[] = \{ {cycArr} };"
    , s!"static const int n_phases = {c.phases.length};"
    , s!"static int cmp_all(void* h, const {tst}* r, const char* tag, long c, int loud) \{"
    , "  int bad = 0;" ] ++ outCmp ++
    [ s!"  const {tst}* g = ((CudaHandle*)h)->h_staging;"
    , "  for (const RegEnt* e = reg_tab; e->name; ++e)"
    , "    if (memcmp((const char*)g + e->off, (const char*)r + e->off, e->size)) {"
    , "      if (bad++ < 3 && loud) printf(\"  [%s c=%ld] register %s differs\\n\", tag, c, e->name); }"
    , "  return bad;"
    , "}"
    , s!"static {tst}* fresh_ref(void) \{ return ({tst}*)calloc(1, sizeof({tst})); }"
    , "/* returns: 0 pass, 1 fail, 2 skipped (mode not applicable) */"
    , "static int run_case(int mode, int* etBad) {"
    , "  char tag[32]; snprintf(tag, sizeof tag, \"mode%d\", mode);"
    , s!"  {tst}* ref = fresh_ref(); {tst}* ref2 = fresh_ref();"
    , "  void* h = jit_cuda_alloc(1);"
    , "  int bad = 0; long c = 0;"
    , "  for (int p = 0; p < n_phases; ++p) {"
    , "    poke_ref[p](ref); poke_ref[p](ref2); poke_gpu[p](h);"
    , "    for (long k = 0; k < phase_cycles[p]; ++k, ++c) {"
    , s!"      sparkle_{topC}_eval_tick(ref);"
    , s!"      sparkle_{topC}_eval(ref2); sparkle_{topC}_tick(ref2);"
    , "      int rc = jit_array_run_mode(h, 1, mode);"
    , "      if (rc == -1) { jit_cuda_free(h); free(ref); free(ref2); return 2; }"
    , "      if (rc != 0) { printf(\"  [%s] jit_array_run_mode rc=%d\\n\", tag, rc); return 1; }"
    , "      bad += cmp_all(h, ref2, tag, c, 1);"
    , "      *etBad += cmp_all(h, ref, tag, c, 0);"
    , "    }"
    , "  }"
    , "  /* one launch per phase: the in-kernel cycle loop */"
    , s!"  {tst}* ref3 = fresh_ref(); void* h2 = jit_cuda_alloc(1);"
    , "  for (int p = 0; p < n_phases; ++p) {"
    , "    poke_ref[p](ref3); poke_gpu[p](h2);"
    , s!"    for (long k = 0; k < phase_cycles[p]; ++k) \{ sparkle_{topC}_eval(ref3); sparkle_{topC}_tick(ref3); }"
    , "    int rc = jit_array_run_mode(h2, phase_cycles[p], mode);"
    , "    if (rc != 0) { printf(\"  [%s] one-launch rc=%d\\n\", tag, rc); return 1; }"
    , "    bad += cmp_all(h2, ref3, \"one-launch\", -1, 1);"
    , "  }"
    , "  jit_cuda_free(h); jit_cuda_free(h2); free(ref); free(ref2); free(ref3);"
    , "  return bad ? 1 : 0;"
    , "}"
    , "static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }"
    , "int main() {"
    , "  printf(\"topology: %s\\n\", jit_array_topology());"
    , s!"  const int modes[] = {modes};"
    , "  int fail = 0;"
    , s!"  for (int i = 0; i < {nModes}; ++i) \{"
    , "    int etBad = 0;"
    , "    int r = run_case(modes[i], &etBad);"
    , s!"    if (modes[i] == 1 && (r == 2) != {if c.blockFits then 0 else 1}) \{ printf(\"  mode1: unexpected block-fit decision\\n\"); fail = 1; }"
    , "    printf(\"  mode %d: %s  (vs eval+tick golden)%s\\n\", modes[i],"
    , "           r == 0 ? \"PASS\" : r == 2 ? \"SKIP (does not fit one block)\" : \"FAIL\","
    , "           r == 2 ? \"\" : etBad ? \"   [CSim eval_tick golden DIFFERS]\" : \"   [= eval_tick golden too]\");"
    , "    if (r == 1) fail = 1;"
    , "  }"
    , "  if (getenv(\"SPARKLE_PERF\")) {"
    , "    const long N = 20000;"
    , "    void* h = jit_cuda_alloc(1); poke_gpu[0](h);"
    , "    jit_array_run(h, 10);"
    , "    double t0 = now(); jit_array_run(h, N); double t1 = now();"
    , s!"    {tst}* r = fresh_ref(); poke_ref[0](r);"
    , s!"    double t2 = now(); for (long k = 0; k < N; ++k) sparkle_{topC}_eval_tick(r); double t3 = now();"
    , "    printf(\"  [perf] GPU %.3e cyc/s   CSim CPU %.3e cyc/s   (%.2fx)\\n\", N / (t1 - t0), N / (t3 - t2), (t3 - t2) / (t1 - t0));"
    , "    jit_cuda_free(h); free(r);"
    , "  }"
    , "  printf(fail ? \"COSIM FAIL\\n\" : \"COSIM PASS\\n\");"
    , "  return fail;"
    , "}"
    , "" ]

/-! ### Emulator rewrite: `k<<<cfg>>>(args)` → `SPARKLE_EMU_LAUNCH(k, cfg)(args)` -/

def emuRewrite (cu : String) : String := Id.run do
  let parts := cu.splitOn "<<<"
  let mut acc := parts.head!
  for part in parts.tail do
    let rev := acc.toList.reverse
    let nameRev := rev.takeWhile fun ch => ch.isAlphanum || ch == '_'
    let name := String.ofList nameRev.reverse
    let base := String.ofList (rev.drop nameRev.length).reverse
    match part.splitOn ">>>" with
    | cfg :: rest =>
      acc := base ++ s!"SPARKLE_EMU_LAUNCH({name}, {cfg})" ++ String.intercalate ">>>" rest
    | [] => acc := acc ++ "<<<" ++ part
  return acc

def which (cmd : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  return r.exitCode == 0

def runCmd (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd, args, env }
  return (r.exitCode, r.stdout ++ r.stderr)

def main : IO UInt32 := do
  let dir := ".lake/build/gen/cuda_array"
  IO.FS.createDirAll dir
  let mut fail := false
  -- 1. rejections
  for (nm, d, reason) in rejections do
    match analyzeArray d with
    | .ok p => IO.println s!"[reject] {nm}: UNEXPECTEDLY ACCEPTED ({describePlan p})"; fail := true
    | .error e =>
      if hasSub e reason then IO.println s!"[reject] {nm}: ok — {e}"
      else IO.println s!"[reject] {nm}: wrong reason — {e}"; fail := fail || !hasSub e reason
  let haveNvcc ← which "nvcc"
  let haveGxx ← which "g++"
  let gpu := (← IO.getEnv "SPARKLE_CUDA") == some "1"
  let arch := (← IO.getEnv "CUDA_ARCH").getD "sm_80"
  let ccbin := if ← which "g++-12" then #["-ccbin", "g++-12"] else #[]
  let only := (← IO.getEnv "CASES")
  for c in cases do
    if let some sel := only then
      if !(sel.splitOn ",").contains c.name then continue
    IO.println s!"\n=== {c.name}"
    let plan ← match analyzeArray c.design with
      | .ok p => pure p
      | .error e => IO.println s!"  analyze FAILED: {e}"; fail := true; continue
    let desc := describePlan plan
    IO.println s!"  {desc}"
    if !hasSub desc c.expect then
      IO.println s!"  expected '{c.expect}'"; fail := true
    let cu ← match toCudaArrayDesign c.design with
      | .ok s => pure s
      | .error e => IO.println s!"  emit FAILED: {e}"; fail := true; continue
    let src := cu ++ cosimMain c plan
    let cuPath := s!"{dir}/{c.name}.cu"
    IO.FS.writeFile cuPath src
    IO.println s!"  emitted {cuPath} ({src.length} chars)"
    -- 2. nvcc: compile + link (device code for {arch})
    if haveNvcc then
      let bin := s!"{dir}/{c.name}_gpu"
      let (rc, out) ← runCmd "nvcc" (ccbin ++ #["-O2", "-std=c++17", s!"-arch={arch}",
        "-Xptxas", "-w", "-o", bin, cuPath])
      if rc != 0 then
        IO.println s!"  nvcc: FAILED\n{out}"; fail := true
      else
        IO.println s!"  nvcc {arch}: compiled + linked OK"
        if gpu then
          let (rr, o) ← runCmd bin #[] #[("SPARKLE_PERF", some "1")]
          IO.print (o.replace "\n" "\n  [gpu] ")
          IO.println ""
          if rr != 0 then fail := true
    -- 3. CPU emulator run
    if haveGxx then
      let emuPath := s!"{dir}/{c.name}_emu.cpp"
      IO.FS.writeFile emuPath (emuRewrite src)
      let bin := s!"{dir}/{c.name}_emu"
      let (rc, out) ← runCmd "g++" #["-std=c++17", "-O1", "-w", "-Itools/cuda_emu", "-o", bin, emuPath]
      if rc != 0 then
        IO.println s!"  g++ (emu): FAILED\n{out.take 3000}"; fail := true
      else
        let (rr, o) ← runCmd bin #[]
        for l in o.splitOn "\n" do
          if !l.isEmpty then IO.println s!"  [emu] {l}"
        if rr != 0 then fail := true
  IO.println (if fail then "\nSOME CHECKS FAILED" else "\nALL PASS")
  return (if fail then 1 else 0)
