/-
  CUDA regular-array backend — topology-aware parallelisation of replicated
  cells.  Design: docs/CudaArraySim-design.md.

  `toCudaIntraDesign` gives every top-level `.inst` a GPU thread and moves
  data between instances through generic `offsetof` copy tables.  Many
  accelerators are more regular than that: an image filter replicates one
  pixel cell N×M times with no coupling at all; a systolic array or a
  cellular automaton replicates one PE on a 1-D or 2-D lattice where every
  cell talks only to neighbours at FIXED offsets.  This backend DETECTS that
  structure and exploits it:

    * `analyzeArray` embeds the instance-connection graph into ℤᵏ:
      connection types (consumer input ← producer output) that relate the
      same instance pairs are one *direction*; a spanning set of directions
      becomes the lattice basis (BFS with free generators), the remaining
      directions (diagonals, reverse links) must be constant integer
      offsets in that frame, every component must be a full box, and every
      direction must be *translation-invariant* (all interior cells have
      the link, boundary cells get it from the top level instead).
      Independent copies of the lattice become one more axis; fully
      independent cells take their geometry from `name_<row>_<col>`
      instance names when those form a full box.

    * the kernels index neighbours ARITHMETICALLY from the thread's
      (x, y, z) coordinate — `kernel<<<dim3 grid, dim3 block>>>` maps
      straight onto the lattice — instead of walking copy tables:

        independent  one launch runs every cycle; no barrier at all; each
                     thread keeps its cell in local memory.
        connected    ping-pong exchange buffer holding only the
                     neighbour-visible (Moore) outputs, ONE barrier per
                     simulated cycle:
                       gather(cur) → eval_tick → eval → publish(nxt) → sync
                     — single-block kernel with `__syncthreads` and the
                     exchange buffer in shared memory when the array fits a
                     block, otherwise one `step_kernel<<<grid, block>>>`
                     launch per cycle (the launch boundary is the barrier).

  Soundness is the CudaIntra argument (eval is register-pure/idempotent,
  cross-cell links tap Moore outputs) plus: the value published after
  cycle c's latch is a function of the registers only, so it equals what
  CSim's cycle-(c+1) eval would expose on that port.

  v1 restrictions (all detected; each error names the offender):
    - the top holds instances of ONE module plus const/ref assigns;
    - in a connected array every neighbour link taps a Moore output that
      is not itself a register field;
    - instance connections are wire/port refs or constants.
-/
import Sparkle.Backend.CudaIntra
import Std.Data.HashMap

namespace Sparkle.Backend.CudaArray

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CSim
open Sparkle.Backend.CudaSim

/-! ### Small helpers -/

/-- C storage size of a CSim field (uint8/16/32/64 by width; wide values are
    `uint32_t` word arrays). -/
def cBytes : HWType → Except String Nat
  | .bit => pure 1
  | .bitVector w =>
    pure <| if w ≤ 8 then 1 else if w ≤ 16 then 2 else if w ≤ 32 then 4
    else if w ≤ 64 then 8 else 4 * ((w + 31) / 32)
  | .bitVectorDim w =>
    throw s!"CudaArray requires concrete widths, found {w}; specialize retained parameters first"
  | .array n t => return n * (← cBytes t)

/-- A ≤ 64-bit integer field (plain C assignment semantics). -/
def isScalarTy : HWType → Bool
  | .bit => true
  | .bitVector w => w ≤ 64
  | _ => false

/-- Field name CSim gives an instance inside its parent struct (must match
    `CSim.emitStmt`'s `.inst` lowering). -/
def instField (modName instName : String) : String :=
  let c := sanitizeName modName
  let r := sanitizeName instName
  if r == c then r ++ "_inst" else r

private def maskedULL (v : Int) (width : Nat) : String :=
  let w := min width 64
  let m : Int := Int.ofNat (2 ^ w)
  let x := ((v % m) + m) % m
  s!"{x.toNat}ULL"

private def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

private def pairLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

private def vecSub (a b : Array Int) : Array Int := (a.zip b).map fun (x, y) => x - y

private def showVec (v : Array Int) : String :=
  "(" ++ String.intercalate "," (v.toList.map toString) ++ ")"

/-! ### Plan -/

/-- A neighbour link: consumer input `port` ← producer output `srcPort`,
    producer at `consumer − off`. -/
structure NbrPort where
  port    : String
  srcPort : String
  /-- consumer − producer, always 3 entries (x, y, z). -/
  off     : Array Int
  /-- number of cells that actually have the link (interior cells). -/
  links   : Nat
  deriving Repr, Inhabited

/-- Where a cell input or a top output gets its value from, outside the
    lattice. -/
inductive ExtSrc where
  | topPort (port : String) (ty : HWType)
  | imm (value : Int) (width : Nat)
  deriving Repr, Inhabited

/-- One per-cell input driven from the top level (top input or constant);
    applied once per launch — top inputs are constant within a run. -/
structure ExtEnt where
  cell : Nat          -- linear cell index
  port : String       -- cell input port
  ty   : HWType       -- cell input type
  src  : ExtSrc
  deriving Repr, Inhabited

inductive OutSrc where
  | cell (idx : Nat) (port : String) (ty : HWType)
  | ext (src : ExtSrc)
  deriving Repr, Inhabited

structure OutEnt where
  port : String
  ty   : HWType
  src  : OutSrc
  deriving Repr, Inhabited

inductive Topology where
  | independent
  | connected
  deriving BEq, Repr, Inhabited

/-- The result of topology detection. -/
structure ArrayPlan where
  top       : Module
  cell      : Module
  /-- Field name of each cell inside the top struct, by linear index. -/
  cellField : Array String
  /-- Instance name by linear index (for reports). -/
  cellInst  : Array String
  /-- Lattice coordinate (x, y, z) by linear index. -/
  coords    : Array (Array Nat)
  /-- Extents [X, Y, Z]; linear index = x + X·(y + Y·z). -/
  dims      : Array Nat
  /-- Number of non-trivial axes (0 for a single cell). -/
  rank      : Nat
  topology  : Topology
  nbrs      : List NbrPort
  ext       : Array ExtEnt    -- sorted by cell
  outs      : List OutEnt
  /-- How the geometry was obtained (lattice / components / names / linear). -/
  geometry  : String

def ArrayPlan.nCells (p : ArrayPlan) : Nat := p.cellField.size

/-! ### Top-level name resolution (hash-map based: 10⁴-cell arrays) -/

private inductive Src where
  | cell (idx : Nat) (port : String)
  | topIn (port : String)
  | imm (v : Int) (w : Nat)

private structure TopCtx where
  top      : Module
  inputs   : Std.HashMap String HWType
  assigns  : Std.HashMap String Expr
  /-- wire → (body-order cell index, cell output port). -/
  drivers  : Std.HashMap String (Nat × String)
  wireTy   : Std.HashMap String HWType

/-- Chase `name` through top const/ref assigns.  Returns the source and the
    smallest C byte size of any intermediate top wire (a narrower wire would
    truncate the value on the way). -/
private def resolveName (ctx : TopCtx) : Nat → String → Nat → Except String (Src × Nat)
  | 0, n, _ => throw s!"reference chain too deep at '{n}' — loop in top-level assigns?"
  | fuel + 1, n, minB => do
    if ctx.inputs.contains n then return (.topIn n, minB)
    let wb ← match ctx.wireTy[n]? with
      | some ty => cBytes ty
      | none => pure minB
    let minB := min minB wb
    if let some (i, port) := ctx.drivers[n]? then return (.cell i port, minB)
    match ctx.assigns[n]? with
    | some (.ref n') => resolveName ctx fuel n' minB
    | some (.const v w) => return (.imm v w, minB)
    | some _ =>
      throw s!"top-level combinational logic drives '{n}' — the array backend supports only const/ref assigns at the top; move the logic into the cell module"
    | none => throw s!"'{n}' is undriven at the top level"

private def resolveExpr (ctx : TopCtx) (fuel : Nat) : Expr → Except String (Src × Nat)
  | .const v w => pure (.imm v w, 1000000)
  | .ref n => resolveName ctx fuel n 1000000
  | e => throw s!"instance connection must be a wire/port reference or a constant — got '{e.toString}' (materialise it inside the cell module)"

/-! ### Lattice embedding -/

/-- BFS over the instance graph with the given directions as FREE generators
    (direction k ↦ unit vector eₖ).  `none` if some cycle is inconsistent
    (the directions are not independent).  Returns coordinates, component
    ids (numbered in order of first instance), and the component count. -/
def embed (n : Nat) (gens : Array (Array (Nat × Nat))) :
    Option (Array (Array Int) × Array Nat × Nat) := Id.run do
  let r := gens.size
  let mut adj : Array (List (Nat × Nat × Int)) := Array.replicate n []
  for k in [0:r] do
    for (s, t) in gens[k]! do
      adj := adj.modify s ((t, k, (1 : Int)) :: ·)
      adj := adj.modify t ((s, k, (-1 : Int)) :: ·)
  let mut coord : Array (Option (Array Int)) := Array.replicate n none
  let mut comp : Array Nat := Array.replicate n 0
  let mut nComp := 0
  for v0 in [0:n] do
    if coord[v0]!.isSome then continue
    coord := coord.set! v0 (some (Array.replicate r 0))
    comp := comp.set! v0 nComp
    let mut queue : Array Nat := #[v0]
    let mut head := 0
    while head < queue.size do
      let v := queue[head]!
      head := head + 1
      let cv := (coord[v]!).getD #[]
      for (u, k, sg) in adj[v]! do
        let cu := cv.modify k (· + sg)
        match coord[u]! with
        | some c => if c != cu then return none
        | none =>
          coord := coord.set! u (some cu)
          comp := comp.set! u nComp
          queue := queue.push u
    nComp := nComp + 1
  return some (coord.map (·.getD #[]), comp, nComp)

/-- Geometry from instance names `prefix_<a>_<b>[_<c>]` (row-major: the LAST
    number is x).  Used only for fully independent cells, and only when the
    numbers form a full box. -/
private def nameGeometry (names : Array String) : Option (Array (Array Nat) × Array Nat) := Id.run do
  let parse (s : String) : Option (String × List Nat) :=
    let parts := s.splitOn "_"
    let nums := (parts.reverse.takeWhile fun p => !p.isEmpty && p.all Char.isDigit).reverse
    if nums.length < 2 || nums.length > 3 then none
    else
      let prefix_ := String.intercalate "_" (parts.take (parts.length - nums.length))
      some (prefix_, nums.map String.toNat!)
  let mut out : Array (Array Nat) := #[]
  let mut pre : Option (String × Nat) := none
  for s in names do
    match parse s with
    | none => return none
    | some (p, ns) =>
      match pre with
      | none => pre := some (p, ns.length)
      | some (p0, k0) => if p0 != p || k0 != ns.length then return none
      out := out.push (ns.reverse.toArray)   -- x = last number
  let k := (pre.map (·.2)).getD 0
  let mins := (List.range k).toArray.map fun a => (out.map (·[a]!)).foldl min (out[0]!)[a]!
  let coords := out.map fun c => (List.range k).toArray.map fun a => c[a]! - mins[a]!
  let dims := (List.range k).toArray.map fun a => (coords.map (·[a]!)).foldl max 0 + 1
  if dims.foldl (· * ·) 1 != names.size then return none
  let lin := coords.map fun c => (List.range k).foldr (fun a acc => acc * dims[a]! + c[a]!) 0
  if (dedup lin.toList).length != names.size then return none
  let pad := fun (a : Array Nat) (v : Nat) => a ++ Array.replicate (3 - a.size) v
  return some (coords.map (pad · 0), pad dims 1)

/-! ### Analysis -/

/-- Detect the replicated-cell topology of `d`'s top module. -/
def analyzeArray (d : Design) : Except String ArrayPlan := do
  if d.modules.any moduleHasSymbolicWidth then
    throw "CudaArray requires concrete widths; specialize retained parameters before CUDA lowering"
  let some top := d.findModule d.topModule
    | throw s!"top module '{d.topModule}' not found in design"
  -- 1. Top body: instances of one module + const/ref assigns.
  let mut insts : Array (String × String × List (String × Expr)) := #[]
  for s in top.body do
    match s with
    | .inst mn iname conns => insts := insts.push (mn, iname, conns)
    | .register out .. =>
      throw s!"top-level register '{out}' — the array backend requires the top to contain only assigns and instances; move it into the cell module"
    | .memory nm .. =>
      throw s!"top-level memory '{nm}' — the array backend requires the top to contain only assigns and instances"
    | .assign .. => pure ()
  if insts.isEmpty then
    throw s!"top module '{top.name}' has no instances — nothing to parallelise (use toCudaSim for a flat module)"
  let kinds := dedup (insts.toList.map (·.1))
  if kinds.length != 1 then
    throw s!"heterogeneous top: instances of {kinds} — the array backend needs ONE replicated cell module (use toCudaIntraDesign for mixed tops)"
  let cellName := kinds.head!
  let some cell := d.findModule cellName
    | throw s!"cell module '{cellName}' not found in design"
  let n := insts.size
  let cellOuts := cell.outputs.map (·.name)
  let cellRegs := cell.body.filterMap fun s => match s with
    | .register o .. => some o | _ => none
  -- 2. Resolution context.
  let mut drivers : Std.HashMap String (Nat × String) := {}
  for i in [0:n] do
    for (port, e) in insts[i]!.2.2 do
      if cellOuts.contains port then
        match e with
        | .ref w => drivers := drivers.insert w (i, port)
        | _ => pure ()
  let mut assigns : Std.HashMap String Expr := {}
  for s in top.body do
    match s with
    | .assign l r => assigns := assigns.insert l r
    | _ => pure ()
  let ctx : TopCtx :=
    { top, drivers, assigns
    , inputs := top.inputs.foldl (fun m p => m.insert p.name p.ty) {}
    , wireTy := (top.wires ++ top.outputs).foldl (fun m p => m.insert p.name p.ty) {} }
  let fuel := top.body.length + 8
  let portTy (ps : List Port) (nm : String) : Option HWType := (ps.find? (·.name == nm)).map (·.ty)
  -- 3. Classify every cell input connection.
  let mut edges : Array (String × String × Nat × Nat) := #[]   -- (port, srcPort, src, dst)
  let mut extRaw : Array (Nat × String × HWType × ExtSrc) := #[]
  for i in [0:n] do
    let (_, iname, conns) := insts[i]!
    for (port, e) in conns do
      if cellOuts.contains port then continue
      let some pty := portTy cell.inputs port
        | throw s!"instance '{iname}': '{port}' is not an input of module '{cellName}'"
      let pb ← cBytes pty
      match ← resolveExpr ctx fuel e with
      | (.cell j q, minB) =>
        if j == i then
          throw s!"instance '{iname}': input '{port}' is fed by its own output '{q}' through the top level — fold the loop into the cell module"
        let some qty := portTy cell.outputs q | throw s!"internal: '{q}' is not an output"
        let qb ← cBytes qty
        if !(isScalarTy pty && isScalarTy qty) && (pty != qty || minB < pb) then
          throw s!"wide link '{iname}.{port}' ← '{insts[j]!.2.1}.{q}' changes type through the top level — not supported"
        if minB < min pb qb then
          throw s!"link '{iname}.{port}' ← '{insts[j]!.2.1}.{q}' passes through a narrower top wire ({minB} bytes) — not supported"
        edges := edges.push (port, q, j, i)
      | (.topIn tp, minB) =>
        let tty := (ctx.inputs[tp]?).getD (.bit)
        let tb ← cBytes tty
        if !(isScalarTy pty && isScalarTy tty) && (pty != tty || minB < pb) then
          throw s!"wide input '{iname}.{port}' ← top input '{tp}' changes type — not supported"
        if minB < min pb tb then
          throw s!"input '{iname}.{port}' ← top input '{tp}' passes through a narrower top wire — not supported"
        extRaw := extRaw.push (i, port, pty, .topPort tp tty)
      | (.imm v w, _) =>
        if pb > 8 && v != 0 then
          throw s!"non-zero constant into wide (> 64-bit) input '{iname}.{port}' is unsupported"
        extRaw := extRaw.push (i, port, pty, .imm v w)
  -- 4. Connection types → directions (same instance-pair set, possibly reversed).
  let typeKeys := dedup (edges.toList.map fun (p, q, _, _) => (p, q))
  let consumerPorts := typeKeys.map (·.1)
  if (dedup consumerPorts).length != consumerPorts.length then
    throw s!"a cell input is fed by different neighbour outputs on different cells ({typeKeys}) — irregular structure"
  let typePairs : Array (Array (Nat × Nat)) := typeKeys.toArray.map fun (p, q) =>
    (edges.filter (fun (p', q', _, _) => p' == p && q' == q) |>.map fun (_, _, s, t) => (s, t)).qsort pairLt
  let mut dirSets : Array (Array (Nat × Nat)) := #[]
  let mut typeDir : Array (Nat × Int) := #[]
  for P in typePairs do
    match dirSets.findIdx? (· == P) with
    | some k => typeDir := typeDir.push (k, 1)
    | none =>
      let R := (P.map fun (s, t) => (t, s)).qsort pairLt
      match dirSets.findIdx? (· == R) with
      | some k => typeDir := typeDir.push (k, -1)
      | none =>
        dirSets := dirSets.push P
        typeDir := typeDir.push (dirSets.size - 1, 1)
  -- 5. Basis: greedily add the directions that are independent AND connect
  --    more of the graph (most links first — axes before diagonals).
  let order := (Array.range dirSets.size).qsort fun a b =>
    dirSets[a]!.size > dirSets[b]!.size || (dirSets[a]!.size == dirSets[b]!.size && a < b)
  let mut basis : Array Nat := #[]
  let mut comps := n
  for k in order do
    let trial := basis.push k
    match embed n (trial.map (dirSets[·]!)) with
    | some (_, _, nc) =>
      if nc < comps then
        basis := trial
        comps := nc
    | none => pure ()
  let some (coordB, compOf, nComp) := embed n (basis.map (dirSets[·]!))
    | throw "internal: basis embedding failed"
  let r := basis.size
  -- 6. Every direction must be a constant offset in the basis frame.
  let mut dirVec : Array (Array Int) := #[]
  for k in [0:dirSets.size] do
    match basis.findIdx? (· == k) with
    | some pos => dirVec := dirVec.push ((Array.replicate r (0 : Int)).set! pos 1)
    | none =>
      let P := dirSets[k]!
      let (s0, t0) := P[0]!
      let v := vecSub coordB[t0]! coordB[s0]!
      for (s, t) in P do
        let (pp, qq) := typeKeys[(typeDir.findIdx? (·.1 == k)).getD 0]!
        if compOf[s]! != compOf[t]! then
          throw s!"'{pp}' ← '{qq}' links ({P.size} of them) do not form a fixed lattice offset — no consistent embedding of the instance graph; irregular structure (use toCudaIntraDesign)"
        if vecSub coordB[t]! coordB[s]! != v then
          throw s!"link '{insts[t]!.2.1}.{pp}' ← '{insts[s]!.2.1}.{qq}' has offset {showVec (vecSub coordB[t]! coordB[s]!)} but other '{pp}' links have {showVec v} — not translation-invariant (use toCudaIntraDesign)"
      dirVec := dirVec.push v
  -- 7. Components: each must be a full box of the same shape.
  let mut members : Array (Array Nat) := Array.replicate nComp #[]
  for i in [0:n] do
    members := members.modify compOf[i]! (·.push i)
  let mut local_ : Array (Array Nat) := Array.replicate n #[]
  let mut ext0 : Option (Array Nat) := none
  for c in [0:nComp] do
    let ms := members[c]!
    let mins := (Array.range r).map fun a => (ms.map (coordB[·]![a]!)).foldl min (coordB[ms[0]!]!)[a]!
    let lc := ms.map fun i => (Array.range r).map fun a => (coordB[i]![a]! - mins[a]!).toNat
    let ex := (Array.range r).map fun a => (lc.map (·[a]!)).foldl max 0 + 1
    if ex.foldl (· * ·) 1 != ms.size then
      throw s!"instances {ms.toList.take 4 |>.map (insts[·]!.2.1)}… do not fill a box (extents {ex.toList}, {ms.size} cells) — irregular structure"
    let lin := lc.map fun cc => (Array.range r).foldr (fun a acc => acc * ex[a]! + cc[a]!) 0
    if (dedup lin.toList).length != ms.size then
      throw s!"two instances map to the same lattice point (a neighbour output fans out to several cells) — irregular structure"
    match ext0 with
    | none => ext0 := some ex
    | some e0 =>
      if e0 != ex then
        throw s!"independent sub-arrays have different shapes ({e0.toList} vs {ex.toList}) — irregular structure"
    for j in [0:ms.size] do
      local_ := local_.set! ms[j]! lc[j]!
  let boxExt := ext0.getD #[]
  -- 8. Final frame: lattice axes (+ one axis over identical components).
  let (coords0, dims0, geometry) : Array (Array Nat) × Array Nat × String :=
    if r == 0 then
      (Array.range n |>.map fun i => #[i], #[n], "linear (independent cells)")
    else if nComp > 1 then
      (Array.range n |>.map fun i => local_[i]!.push compOf[i]!, boxExt.push nComp,
       s!"lattice ({r}-D) × {nComp} independent copies")
    else (local_, boxExt, s!"lattice ({r}-D)")
  let (coords0, dims0, geometry) :=
    if r == 0 then
      match nameGeometry (insts.map (·.2.1)) with
      | some (cs, ds) => (cs, ds, "instance names (independent cells)")
      | none => (coords0, dims0, geometry)
    else (coords0, dims0, geometry)
  -- Orientation: flip lattice axes so the first instance sits at the origin
  -- (purely cosmetic — offsets are flipped with the coordinates).
  let flips : Array Bool := (Array.range r).map fun a =>
    dims0[a]! > 1 && coords0[0]![a]! + 1 == dims0[a]!
  let coords0 := if r == 0 then coords0 else coords0.map fun c =>
    (Array.range c.size).map fun a =>
      if a < r && flips[a]! then dims0[a]! - 1 - c[a]! else c[a]!
  if dims0.size > 3 then
    throw s!"{dims0.size}-dimensional structure (extents {dims0.toList}) — CUDA grids have 3 axes; use toCudaIntraDesign"
  let pad := fun (a : Array Nat) (v : Nat) => a ++ Array.replicate (3 - a.size) v
  let coords := coords0.map (pad · 0)
  let dims := pad dims0 1
  let rank := (dims.filter (· > 1)).size
  let linOf (c : Array Nat) : Nat := c[0]! + dims[0]! * (c[1]! + dims[1]! * c[2]!)
  -- body index → linear index, and back
  let bodyLin := coords.map linOf
  let mut linBody : Array Nat := Array.replicate n 0
  for i in [0:n] do
    linBody := linBody.set! bodyLin[i]! i
  -- 9. Neighbour ports with their final-frame offsets; completeness check.
  let inBox (c : Array Int) : Bool :=
    (List.range 3).all fun a => 0 ≤ c[a]! && c[a]! < Int.ofNat dims[a]!
  let icoord (i : Nat) : Array Int := coords[i]!.map Int.ofNat
  let mut nbrs : List NbrPort := []
  for t in [0:typeKeys.length] do
    let (p, q) := typeKeys[t]!
    let (k, sg) := typeDir[t]!
    let vf := (Array.range r).map fun a => if flips[a]! then -(dirVec[k]![a]!) else dirVec[k]![a]!
    let v3 := (vf ++ (if r > 0 && nComp > 1 then #[0] else #[])).map (· * sg)
    let off := v3 ++ Array.replicate (3 - v3.size) 0
    let P := typePairs[t]!
    for (s, dst) in P do
      if vecSub (icoord dst) (icoord s) != off then
        throw s!"internal: link '{insts[dst]!.2.1}.{p}' does not match its lattice offset {showVec off}"
    let interior := (List.range n).countP fun i => inBox (vecSub (icoord i) off)
    if interior != P.size then
      throw s!"'{p}' ← '{q}' links only {P.size} of the {interior} interior cells at offset {showVec off} — the pattern is not translation-invariant (irregular boundary); use toCudaIntraDesign"
    nbrs := nbrs ++ [{ port := p, srcPort := q, off, links := P.size }]
  let connected := !nbrs.isEmpty
  -- 10. Connected arrays: neighbour-visible outputs must be Moore.
  if connected then
    for q in dedup (nbrs.map (·.srcPort)) do
      let deps ← Sparkle.Backend.CudaIntra.combDeps cell q
      if !deps.isEmpty then
        throw s!"Mealy neighbour link: output '{q}' of '{cellName}' combinationally depends on input(s) {deps} — register it (connected arrays need Moore links; v2: K-round relaxation)"
      if cellRegs.contains q then
        throw s!"neighbour output '{q}' of '{cellName}' is a register field itself — CSim's sequential eval_tick exposes it post-latch; add an `assign {q}_o := {q}` output"
  -- 11. External (top-driven) cell inputs, by linear index.
  let ext := (extRaw.map fun (i, port, ty, src) =>
      ({ cell := bodyLin[i]!, port, ty, src } : ExtEnt)).qsort fun a b => a.cell < b.cell
  -- 12. Top outputs.
  let mut outs : List OutEnt := []
  for op in top.outputs do
    match resolveName ctx fuel op.name 1000000 with
    | .error e =>
      if (e.splitOn "undriven").length > 1 then continue else throw s!"top output '{op.name}': {e}"
    | .ok (.cell j q, minB) =>
      let some qty := portTy cell.outputs q | throw s!"internal: '{q}' not an output"
      let ob ← cBytes op.ty
      if !(isScalarTy op.ty && isScalarTy qty) && op.ty != qty then
        throw s!"top output '{op.name}' ← '{insts[j]!.2.1}.{q}' changes a wide type — not supported"
      if minB < min ob (← cBytes qty) then
        throw s!"top output '{op.name}' passes through a narrower top wire — not supported"
      outs := outs ++ [{ port := op.name, ty := op.ty, src := .cell bodyLin[j]! q qty }]
    | .ok (.topIn tp, _) =>
      outs := outs ++ [{ port := op.name, ty := op.ty, src := .ext (.topPort tp ((ctx.inputs[tp]?).getD .bit)) }]
    | .ok (.imm v w, _) =>
      outs := outs ++ [{ port := op.name, ty := op.ty, src := .ext (.imm v w) }]
  return { top, cell
         , cellField := linBody.map fun i => instField cellName insts[i]!.2.1
         , cellInst := linBody.map fun i => insts[i]!.2.1
         , coords := linBody.map (coords[·]!)
         , dims, rank
         , topology := if connected then .connected else .independent
         , nbrs, ext, outs, geometry }

/-- One-line human-readable summary (also embedded in the `.cu` and
    returned by `jit_array_topology()`). -/
def describePlan (p : ArrayPlan) : String :=
  let d := p.dims
  let shape := String.intercalate "x" ((d.toList.take (max p.rank 1)).map toString)
  let kind := match p.topology with
    | .independent => "independent"
    | .connected => "connected"
  let axis (a : Nat) : String := match a with | 0 => "x" | 1 => "y" | _ => "z"
  let nb := p.nbrs.map fun nb =>
    let rel := String.intercalate "," <| (List.range 3).filterMap fun a =>
      let o : Int := nb.off[a]!
      if o == 0 then none
      else if o > 0 then some s!"{axis a}-{o}" else some s!"{axis a}+{-o}"
    s!"{nb.port}<-{nb.srcPort}@({rel})"
  s!"{kind} {p.rank}-D array {shape} of {p.nCells} x {p.cell.name} [geometry: {p.geometry}]" ++
    (if nb.isEmpty then "" else "; links: " ++ String.intercalate " " nb)

/-! ### Emission -/

private def moveEntry (dst src : String) (db sb : Nat) (isImm : Bool) (imm : String) : String :=
  s!"  \{ {dst}, {src}, {db}u, {sb}u, {if isImm then 1 else 0}u, {imm} },"

/-- Tables, exchange record, and the three kernel families. -/
def emitArraySection (p : ArrayPlan) : Except String String := do
  let topC := sanitizeName p.top.name
  let cellC := sanitizeName p.cell.name
  let pre := s!"{topC}_arr"
  let st := s!"struct {cellC}"
  let tst := s!"struct {topC}"
  let n := p.nCells
  let (dx, dy, dz) := (p.dims[0]!, p.dims[1]!, p.dims[2]!)
  -- ext table (CSR by linear cell index)
  let mut extLines : Array String := #[]
  let mut begins : Array Nat := Array.replicate (n + 1) 0
  for e in p.ext do
    let db ← cBytes e.ty
    let dstC := s!"offsetof({st}, {sanitizeName e.port})"
    match e.src with
    | .topPort tp tty =>
      extLines := extLines.push (moveEntry dstC s!"offsetof({tst}, {sanitizeName tp})" db (← cBytes tty) false "0ULL")
    | .imm v w =>
      extLines := extLines.push (moveEntry dstC "0" db 8 true (maskedULL v w))
    begins := begins.modify (e.cell + 1) (· + 1)
  for i in [0:n] do
    begins := begins.set! (i + 1) (begins[i + 1]! + begins[i]!)
  -- outputs table
  let mut outLines : Array String := #[]
  for o in p.outs do
    let db ← cBytes o.ty
    let dstC := s!"offsetof({tst}, {sanitizeName o.port})"
    match o.src with
    | .cell idx q qty =>
      outLines := outLines.push
        s!"  \{ {dstC}, offsetof({st}, {sanitizeName q}), {db}u, {← cBytes qty}u, 0u, {idx}u, 0ULL },"
    | .ext (.topPort tp tty) =>
      outLines := outLines.push
        s!"  \{ {dstC}, offsetof({tst}, {sanitizeName tp}), {db}u, {← cBytes tty}u, 1u, 0u, 0ULL },"
    | .ext (.imm v w) =>
      outLines := outLines.push s!"  \{ {dstC}, 0, {db}u, 8u, 2u, 0u, {maskedULL v w} },"
  let offLines := p.cellField.toList.map fun f => s!"  offsetof({tst}, {f}),"
  let beginLines := begins.toList.map fun b => s!"{b}u"
  let desc := (describePlan p).replace "\"" "'"
  let header : List String :=
    [ "// ── Regular-array backend (topology-aware, docs/CudaArraySim-design.md) ──"
    , s!"// {desc}"
    , "#ifndef SPARKLE_ARR_COMMON"
    , "#define SPARKLE_ARR_COMMON"
    , "#ifndef SPARKLE_ARR_LOCAL_MAX"
    , "#define SPARKLE_ARR_LOCAL_MAX 4096   /* cells up to this size live in thread-local memory */"
    , "#endif"
    , "typedef struct { size_t dst; size_t src; unsigned dstBytes; unsigned srcBytes; unsigned isImm; unsigned long long imm; } SparkleArrExt;"
    , "typedef struct { size_t dst; size_t src; unsigned dstBytes; unsigned srcBytes; unsigned kind; unsigned cell; unsigned long long imm; } SparkleArrOut;"
    , "/* C unsigned-conversion copy: zero-extend / truncate scalars, memcpy wide (same size, checked at generation). */"
    , "static __host__ __device__ __forceinline__ void sparkle_arr_move(char* dst, const char* src, unsigned db, unsigned sb) {"
    , "  if (db > 8 || sb > 8) { memcpy(dst, src, db); return; }"
    , "  unsigned long long v = 0; memcpy(&v, src, sb); memcpy(dst, &v, db);"
    , "}"
    , "#endif"
    , ""
    , s!"enum \{ {pre}_X = {dx}, {pre}_Y = {dy}, {pre}_Z = {dz}, {pre}_N = {n}, {pre}_nOut = {p.outs.length} };"
    , s!"static const char {pre}_desc[] = \"{desc}\";"
    , s!"static __device__ const size_t {pre}_off[{n}] = \{" ]
    ++ offLines ++
    [ "};"
    , s!"static __device__ const unsigned {pre}_ext_begin[{n + 1}] = \{ {String.intercalate ", " beginLines} };"
    , s!"static __device__ const SparkleArrExt {pre}_ext[{max extLines.size 1}] = \{" ]
    ++ (if extLines.isEmpty then ["  { 0, 0, 0u, 0u, 0u, 0ULL },"] else extLines.toList) ++
    [ "};"
    , s!"static __device__ const SparkleArrOut {pre}_outs[{max outLines.size 1}] = \{" ]
    ++ (if outLines.isEmpty then ["  { 0, 0, 0u, 0u, 0u, 0u, 0ULL },"] else outLines.toList) ++
    [ "};"
    , ""
    , s!"static __host__ __device__ __forceinline__ unsigned {pre}_idx(int x, int y, int z) \{"
    , s!"  return (unsigned)x + {pre}_X * ((unsigned)y + {pre}_Y * (unsigned)z);"
    , "}"
    , s!"static __device__ __forceinline__ {st}* {pre}_cell({tst}* top, unsigned idx) \{"
    , s!"  return ({st}*)((char*)top + {pre}_off[idx]);"
    , "}"
    , "/* Top-driven cell inputs (top inputs / constants): constant within a run. */"
    , s!"static __device__ void {pre}_load_ext({st}* c, const {tst}* top, unsigned idx) \{"
    , s!"  for (unsigned i = {pre}_ext_begin[idx]; i < {pre}_ext_begin[idx + 1]; ++i) \{"
    , s!"    const SparkleArrExt* e = &{pre}_ext[i];"
    , "    char* dst = (char*)c + e->dst;"
    , "    if (e->isImm) { if (e->dstBytes > 8) memset(dst, 0, e->dstBytes); else memcpy(dst, &e->imm, e->dstBytes); }"
    , "    else sparkle_arr_move(dst, (const char*)top + e->src, e->dstBytes, e->srcBytes);"
    , "  }"
    , "}"
    , "/* Top output ports ← cell output fields (after the last eval_tick, as CSim observes them). */"
    , s!"__global__ void {pre}_outputs_kernel({tst}* top) \{"
    , "  const unsigned i = blockIdx.x * blockDim.x + threadIdx.x;"
    , s!"  if (i >= (unsigned){pre}_nOut) return;"
    , s!"  const SparkleArrOut* o = &{pre}_outs[i];"
    , "  char* dst = (char*)top + o->dst;"
    , s!"  if (o->kind == 0) sparkle_arr_move(dst, (const char*){pre}_cell(top, o->cell) + o->src, o->dstBytes, o->srcBytes);"
    , "  else if (o->kind == 1) sparkle_arr_move(dst, (const char*)top + o->src, o->dstBytes, o->srcBytes);"
    , "  else if (o->dstBytes > 8) memset(dst, 0, o->dstBytes);"
    , "  else memcpy(dst, &o->imm, o->dstBytes);"
    , "}"
    , "" ]
  let gridCoords : List String :=
    [ "  const int x = (int)(blockIdx.x * blockDim.x + threadIdx.x);"
    , "  const int y = (int)(blockIdx.y * blockDim.y + threadIdx.y);"
    , "  const int z = (int)(blockIdx.z * blockDim.z + threadIdx.z);"
    , s!"  if (x >= {pre}_X || y >= {pre}_Y || z >= {pre}_Z) return;"
    , s!"  const unsigned idx = {pre}_idx(x, y, z);" ]
  let body : List String ← match p.topology with
  | .independent => pure <|
    [ "/* INDEPENDENT cells: no cross-cell data, so one launch runs every cycle with"
    , "   no barrier; each thread keeps its cell in local memory. */"
    , "template <bool Local>"
    , s!"static __device__ void {pre}_indep_body({tst}* top, long cycles, unsigned idx) \{"
    , s!"  {st}* g = {pre}_cell(top, idx);"
    , "  if constexpr (Local) {"
    , s!"    {st} me; memcpy(&me, g, sizeof me);"
    , s!"    {pre}_load_ext(&me, top, idx);"
    , s!"    for (long k = 0; k < cycles; ++k) sparkle_{cellC}_eval_tick(&me);"
    , "    memcpy(g, &me, sizeof me);"
    , "  } else {"
    , s!"    {pre}_load_ext(g, top, idx);"
    , s!"    for (long k = 0; k < cycles; ++k) sparkle_{cellC}_eval_tick(g);"
    , "  }"
    , "}"
    , s!"__global__ void {pre}_indep_kernel({tst}* top, long cycles) \{" ]
    ++ gridCoords ++
    [ s!"  {pre}_indep_body<(sizeof({st}) <= SPARKLE_ARR_LOCAL_MAX)>(top, cycles, idx);"
    , "}"
    , "" ]
  | .connected => do
    let srcPorts := dedup (p.nbrs.map (·.srcPort))
    let mut xchFields : List String := []
    let mut pubLines : List String := []
    for q in srcPorts do
      let some qp := p.cell.outputs.find? (·.name == q) | throw s!"internal: '{q}'"
      let qn := sanitizeName q
      xchFields := xchFields ++ [s!"  {emitFieldDecl qp.ty qn};"]
      pubLines := pubLines ++
        [if isScalarTy qp.ty then s!"  x->{qn} = c->{qn};"
         else s!"  memcpy(x->{qn}, c->{qn}, sizeof(x->{qn}));"]
    let axisVar := #["x", "y", "z"]
    let axisDim := #[s!"{pre}_X", s!"{pre}_Y", s!"{pre}_Z"]
    let mut gatherLines : List String := []
    for nb in p.nbrs do
      let some pp := p.cell.inputs.find? (·.name == nb.port) | throw s!"internal: '{nb.port}'"
      let conds := (List.range 3).filterMap fun a =>
        let o : Int := nb.off[a]!
        if o > 0 then some s!"{axisVar[a]!} >= {o}"
        else if o < 0 then some s!"{axisVar[a]!} + {-o} < {axisDim[a]!}"
        else none
      let srcIdx := (List.range 3).map fun a =>
        let o : Int := nb.off[a]!
        if o > 0 then s!"{axisVar[a]!} - {o}" else if o < 0 then s!"{axisVar[a]!} + {-o}" else axisVar[a]!
      let cond := if conds.isEmpty then "1" else String.intercalate " && " conds
      let src := s!"xb[{pre}_idx({String.intercalate ", " srcIdx})].{sanitizeName nb.srcPort}"
      let pn := sanitizeName nb.port
      gatherLines := gatherLines ++
        [if isScalarTy pp.ty then s!"  if ({cond}) c->{pn} = {src};"
         else s!"  if ({cond}) memcpy(c->{pn}, {src}, sizeof(c->{pn}));"]
    pure <|
    [ "/* CONNECTED lattice: neighbour-visible (Moore) outputs travel through a"
    , "   ping-pong exchange buffer; one barrier per simulated cycle. */"
    , s!"struct {pre}_xch \{" ]
    ++ xchFields ++
    [ "};"
    , s!"static __device__ __forceinline__ void {pre}_publish(struct {pre}_xch* x, const {st}* c) \{" ]
    ++ pubLines ++
    [ "}"
    , "/* Neighbour inputs by index arithmetic; boundary cells keep their top-driven value. */"
    , s!"static __device__ __forceinline__ void {pre}_gather({st}* c, const struct {pre}_xch* xb, int x, int y, int z) \{"
    , "  (void)x; (void)y; (void)z;" ]
    ++ gatherLines ++
    [ "}"
    , ""
    , "/* Single block: dim3 block = lattice extents, exchange buffer in shared memory. */"
    , s!"static __device__ void {pre}_block_loop({st}* c, {tst}* top, long cycles,"
    , s!"    struct {pre}_xch* b0, struct {pre}_xch* b1, int x, int y, int z, unsigned idx) \{"
    , s!"  {pre}_load_ext(c, top, idx);"
    , s!"  sparkle_{cellC}_eval(c);                 /* Moore outputs of cycle 0 */"
    , s!"  {pre}_publish(&b0[idx], c);"
    , "  __syncthreads();"
    , s!"  struct {pre}_xch* cur = b0; struct {pre}_xch* nxt = b1;"
    , "  for (long k = 0; k < cycles; ++k) {"
    , s!"    {pre}_gather(c, cur, x, y, z);"
    , s!"    sparkle_{cellC}_eval_tick(c);           /* next state with fresh inputs, latch */"
    , s!"    if (k + 1 < cycles) \{ sparkle_{cellC}_eval(c); {pre}_publish(&nxt[idx], c); }"
    , "    __syncthreads();"
    , s!"    struct {pre}_xch* t = cur; cur = nxt; nxt = t;"
    , "  }"
    , "}"
    , "template <bool Local>"
    , s!"static __device__ void {pre}_block_body({tst}* top, long cycles, struct {pre}_xch* b0, struct {pre}_xch* b1) \{"
    , "  const int x = (int)threadIdx.x, y = (int)threadIdx.y, z = (int)threadIdx.z;"
    , s!"  const unsigned idx = {pre}_idx(x, y, z);"
    , s!"  {st}* g = {pre}_cell(top, idx);"
    , "  if constexpr (Local) {"
    , s!"    {st} me; memcpy(&me, g, sizeof me);"
    , s!"    {pre}_block_loop(&me, top, cycles, b0, b1, x, y, z, idx);"
    , "    memcpy(g, &me, sizeof me);"
    , "  } else {"
    , s!"    {pre}_block_loop(g, top, cycles, b0, b1, x, y, z, idx);"
    , "  }"
    , "}"
    , s!"__global__ void {pre}_block_kernel({tst}* top, long cycles, struct {pre}_xch* gx) \{"
    , "  extern __shared__ unsigned long long sparkle_dyn_smem[];"
    , s!"  struct {pre}_xch* b0 = gx ? gx : (struct {pre}_xch*)sparkle_dyn_smem;"
    , s!"  {pre}_block_body<(sizeof({st}) <= SPARKLE_ARR_LOCAL_MAX)>(top, cycles, b0, b0 + {pre}_N);"
    , "}"
    , ""
    , "/* Any size: one launch per cycle — the kernel boundary is the barrier. */"
    , s!"__global__ void {pre}_prologue_kernel({tst}* top, struct {pre}_xch* x0) \{" ]
    ++ gridCoords ++
    [ s!"  {st}* c = {pre}_cell(top, idx);"
    , s!"  {pre}_load_ext(c, top, idx);"
    , s!"  sparkle_{cellC}_eval(c);"
    , s!"  {pre}_publish(&x0[idx], c);"
    , "}"
    , s!"__global__ void {pre}_step_kernel({tst}* top, const struct {pre}_xch* cur, struct {pre}_xch* nxt, int publishNext) \{" ]
    ++ gridCoords ++
    [ s!"  {st}* c = {pre}_cell(top, idx);"
    , s!"  {pre}_gather(c, cur, x, y, z);"
    , s!"  sparkle_{cellC}_eval_tick(c);"
    , s!"  if (publishNext) \{ sparkle_{cellC}_eval(c); {pre}_publish(&nxt[idx], c); }"
    , "}"
    , "" ]
  return String.intercalate "\n" (header ++ body)

/-- Host entry points.  The handle is the batch backend's `CudaHandle`
    (`jit_cuda_alloc(1)`, instance 0), so `jit_cuda_set_input` /
    `jit_cuda_get_output` work unchanged. -/
def emitArrayHost (p : ArrayPlan) : String :=
  let topC := sanitizeName p.top.name
  let pre := s!"{topC}_arr"
  let tst := s!"struct {topC}"
  let blk : String := match p.rank with
    | 0 | 1 => if p.dims[1]! == 1 && p.dims[2]! == 1 then "256, 1, 1" else "16, 16, 1"
    | 2 => "16, 16, 1"
    | _ => "8, 8, 4"
  let common : List String :=
    [ "extern \"C\" {"
    , ""
    , s!"const char* jit_array_topology(void) \{ return {pre}_desc; }"
    , ""
    , "/* Run instance 0 of a jit_cuda_alloc handle for numCycles cycles with the"
    , "   topology-aware schedule.  mode: 0 = auto, 1 = single-block kernel"
    , "   (__syncthreads), 2 = one step_kernel launch per cycle.  Returns 0 on"
    , "   success, -1 if the requested mode cannot run this array, -2 on a CUDA error. */"
    , "int jit_array_run_mode(void* handle, long numCycles, int mode) {"
    , "  CudaHandle* h = (CudaHandle*)handle;"
    , s!"  {tst}* d_top = h->d_states;"
    , "  if (numCycles <= 0) return 0;"
    , s!"  cudaMemcpy(d_top, h->h_staging, sizeof({tst}), cudaMemcpyHostToDevice);"
    , s!"  const dim3 block({blk});"
    , s!"  const dim3 grid(({pre}_X + block.x - 1) / block.x, ({pre}_Y + block.y - 1) / block.y, ({pre}_Z + block.z - 1) / block.z);"
    , "  (void)grid; (void)mode;"
    , "  int rc = 0;" ]
  let run : List String := match p.topology with
    | .independent =>
      [ s!"  {pre}_indep_kernel<<<grid, block>>>(d_top, numCycles);" ]
    | .connected =>
      [ s!"  const size_t xb = sizeof(struct {pre}_xch) * (size_t){pre}_N;"
      , s!"  const int fitsBlock = {pre}_N <= 1024 && {pre}_Z <= 64 && 2 * xb <= 48 * 1024;"
      , "  if (mode == 1 && !fitsBlock) { rc = -1; goto copy_back; }"
      , "  if (fitsBlock && mode != 2) {"
      , s!"    {pre}_block_kernel<<<1, dim3({pre}_X, {pre}_Y, {pre}_Z), 2 * xb>>>(d_top, numCycles, (struct {pre}_xch*)0);"
      , "    if (cudaGetLastError() == cudaSuccess) goto outputs;"
      , "    if (mode == 1) { rc = -2; goto copy_back; }   /* e.g. too many registers for one block */"
      , "  }"
      , "  {"
      , s!"    struct {pre}_xch* xbuf = 0;"
      , "    if (cudaMalloc((void**)&xbuf, 2 * xb) != cudaSuccess) { rc = -2; goto copy_back; }"
      , s!"    struct {pre}_xch* x0 = xbuf; struct {pre}_xch* x1 = xbuf + {pre}_N;"
      , s!"    {pre}_prologue_kernel<<<grid, block>>>(d_top, x0);"
      , "    for (long k = 0; k < numCycles; ++k) {"
      , s!"      {pre}_step_kernel<<<grid, block>>>(d_top, (k & 1) ? x1 : x0, (k & 1) ? x0 : x1, (int)(k + 1 < numCycles));"
      , "    }"
      , "    cudaDeviceSynchronize();"
      , "    cudaFree(xbuf);"
      , "  }"
      , "outputs:" ]
  let tail : List String :=
    [ s!"  if ({pre}_nOut > 0) {pre}_outputs_kernel<<<({pre}_nOut + 255) / 256, 256>>>(d_top);"
    , "  if (cudaDeviceSynchronize() != cudaSuccess || cudaGetLastError() != cudaSuccess) rc = -2;" ]
    ++ (match p.topology with | .connected => ["copy_back:"] | .independent => []) ++
    [ s!"  cudaMemcpy(h->h_staging, d_top, sizeof({tst}), cudaMemcpyDeviceToHost);"
    , "  return rc;"
    , "}"
    , ""
    , "void jit_array_run(void* handle, long numCycles) { (void)jit_array_run_mode(handle, numCycles, 0); }"
    , ""
    , "} // extern \"C\""
    , "" ]
  String.intercalate "\n" (common ++ run ++ tail)

/-- Generate the regular-array `.cu` for a whole `Design`: CSim device code
    (all modules, host+device qualified), the batch kernel + batch host API
    (for `CudaHandle` / poke / peek), the array tables and kernels, and
    `jit_array_run[_mode]` / `jit_array_topology`.  No `-rdc` needed. -/
def toCudaArrayDesign (d : Design) : Except String String := do
  let plan ← analyzeArray d
  let sec ← emitArraySection plan
  let some top := d.findModule d.topModule | throw "internal: top vanished"
  let topC := sanitizeName top.name
  let preamble := String.intercalate "\n"
    [ "// AUTO-GENERATED by Sparkle HDL — CUDA Regular-Array (topology-aware) Backend"
    , s!"// Module: {top.name} — {(describePlan plan).replace "\n" " "}"
    , "//"
    , "// Compile with:"
    , s!"//   nvcc -O3 -std=c++17 -shared -Xcompiler -fPIC -o lib{topC}.so {topC}.cu"
    , ""
    , "#include <cstdint>"
    , "#include <cstring>"
    , "#include <cstddef>"
    , "#include <cstdio>"
    , "#include <cuda_runtime.h>"
    , ""
    , "// ── CSim device code (struct + __host__ __device__ module functions) ─" ]
  return String.intercalate "\n"
    [ preamble
    , emitCudaDeviceCodeD d
    , "// ── Batch kernel ─────────────────────────────────────────────────"
    , emitCudaBatchKernel top
    , emitCudaJITHostAPI top
    , sec
    , emitArrayHost plan ]

/-- Specialize retained dimensions first, then detect + emit. -/
def toCudaArrayDesignWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings) : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  toCudaArrayDesign concrete

/-- String form: an analysis error becomes a `#error` so it is loud at nvcc
    time. -/
def toCudaArrayDesign! (d : Design) : String :=
  match toCudaArrayDesign d with
  | .ok s => s
  | .error e => s!"#error \"Sparkle CudaArray: {e.replace "\"" "'"}\"\n"

/-- Pick the best CUDA lowering automatically: the regular-array backend when
    the top is a detectable lattice / independent array, otherwise the
    generic per-instance intra backend, otherwise the batch backend.
    Returns the `.cu` and which backend produced it. -/
def toCudaAuto (d : Design) : String × String :=
  match toCudaArrayDesign d with
  | .ok s => (s, "array")
  | .error _ =>
    match Sparkle.Backend.CudaIntra.toCudaIntraDesign d with
    | .ok s => (s, "intra")
    | .error _ => (toCudaSimDesign d, "batch")

end Sparkle.Backend.CudaArray
