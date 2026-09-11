import Sparkle.IR.AST
import Sparkle.IR.Type

/-! Fixtures for `Sparkle.Backend.CudaArray` (docs/CudaArraySim-design.md).

Each positive fixture is a hierarchical design whose top instantiates ONE
cell module many times — the shapes the topology detector must recognise:

| fixture            | structure                                    | expected        |
|--------------------|----------------------------------------------|-----------------|
| `meshDesign n`     | weight-stationary systolic PE mesh            | connected 2-D   |
| `firDesign rows k` | `rows` independent k-tap systolic FIR chains  | 1-D, or 1-D × rows |
| `pixDesign r c`    | per-pixel IIR filter, no coupling             | independent 2-D (names) |
| `lifeDesign n`     | Game of Life, 8 neighbours incl. diagonals    | connected 2-D   |

plus rejection fixtures (Mealy link, irregular link, heterogeneous top,
top-level register). -/

namespace Sparkle.Test.CudaArray

open Sparkle.IR.AST
open Sparkle.IR.Type

private def bv (w : Nat) : HWType := .bitVector w

/-- Systolic PE (same as the intra fixture): a flows right, psum flows down. -/
def peModule : Module := {
  name := "PE", isPrimitive := false
  inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"a_in", bv 32⟩, ⟨"p_in", bv 32⟩, ⟨"w", bv 32⟩]
  outputs := [⟨"a_out", bv 32⟩, ⟨"p_out", bv 32⟩]
  wires := [⟨"a_reg", bv 32⟩, ⟨"p_reg", bv 32⟩, ⟨"mul", bv 32⟩]
  body := [
    .assign "mul" (.op .mul [.ref "a_in", .ref "w"]),
    .register "a_reg" "clk" ("rst", .synchronous) (.ref "a_in") 0,
    .register "p_reg" "clk" ("rst", .synchronous) (.op .add [.ref "p_in", .ref "mul"]) 0,
    .assign "a_out" (.ref "a_reg"),
    .assign "p_out" (.ref "p_reg") ] }

/-- n×n mesh; activations from the left edge, partial sums down, bottom row
    observed on `result_j`.  `cellName` lets a rejection fixture swap one cell. -/
def meshTop (n : Nat) (odd : Option (Nat × Nat × String) := none)
    (longLink : Bool := false) : Module := Id.run do
  let mut inputs : List Port := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  let mut outputs : List Port := []
  let mut wires : List Port := [⟨"zero32", bv 32⟩]
  let mut body : List Stmt := [.assign "zero32" (.const 0 32)]
  for i in [0:n] do
    inputs := inputs ++ [⟨s!"ain_{i}", bv 32⟩]
  for i in [0:n] do
    for j in [0:n] do
      inputs := inputs ++ [⟨s!"w_{i}_{j}", bv 32⟩]
      wires := wires ++ [⟨s!"aout_{i}_{j}", bv 32⟩, ⟨s!"pout_{i}_{j}", bv 32⟩]
  for i in [0:n] do
    for j in [0:n] do
      let aSrc := if j == 0 then s!"ain_{i}" else s!"aout_{i}_{j-1}"
      let pSrc :=
        if longLink && i == n - 1 && j == n - 1 then "pout_0_0"
        else if i == 0 then "zero32" else s!"pout_{i-1}_{j}"
      let modName := match odd with
        | some (oi, oj, m) => if oi == i && oj == j then m else "PE"
        | none => "PE"
      body := body ++ [.inst modName s!"pe_{i}_{j}"
        [ ("clk", .ref "clk"), ("rst", .ref "rst")
        , ("a_in", .ref aSrc), ("p_in", .ref pSrc), ("w", .ref s!"w_{i}_{j}")
        , ("a_out", .ref s!"aout_{i}_{j}"), ("p_out", .ref s!"pout_{i}_{j}") ]]
  for j in [0:n] do
    outputs := outputs ++ [⟨s!"result_{j}", bv 32⟩]
    body := body ++ [.assign s!"result_{j}" (.ref s!"pout_{n-1}_{j}")]
  return { name := s!"Mesh{n}x{n}", inputs, outputs, wires, body, isPrimitive := false }

def meshDesign (n : Nat) : Design :=
  { topModule := s!"Mesh{n}x{n}", modules := [peModule, meshTop n] }

/-- Systolic FIR tap: x is delayed one cycle per tap, the accumulator adds
    x·coef.  Both outputs are registered (Moore) and flow to the SAME
    neighbour — the detector must merge the two links into one direction. -/
def tapModule : Module := {
  name := "Tap", isPrimitive := false
  inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"x_in", bv 16⟩, ⟨"acc_in", bv 32⟩, ⟨"coef", bv 16⟩]
  outputs := [⟨"x_out", bv 16⟩, ⟨"acc_out", bv 32⟩]
  wires := [⟨"x_reg", bv 16⟩, ⟨"acc_reg", bv 32⟩, ⟨"prod", bv 32⟩]
  body := [
    .assign "prod" (.op .mul [.concat [.const 0 16, .ref "x_in"], .concat [.const 0 16, .ref "coef"]]),
    .register "x_reg" "clk" ("rst", .synchronous) (.ref "x_in") 0,
    .register "acc_reg" "clk" ("rst", .synchronous) (.op .add [.ref "acc_in", .ref "prod"]) 0,
    .assign "x_out" (.ref "x_reg"),
    .assign "acc_out" (.ref "acc_reg") ] }

/-- `rows` independent `taps`-long FIR chains (rows = 1: a plain 1-D chain). -/
def firTop (rows taps : Nat) : Module := Id.run do
  let mut inputs : List Port := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  let mut outputs : List Port := []
  let mut wires : List Port := [⟨"zero", bv 32⟩]
  let mut body : List Stmt := [.assign "zero" (.const 0 32)]
  for r in [0:rows] do
    inputs := inputs ++ [⟨s!"x_{r}", bv 16⟩]
    for t in [0:taps] do
      inputs := inputs ++ [⟨s!"c_{r}_{t}", bv 16⟩]
      wires := wires ++ [⟨s!"xo_{r}_{t}", bv 16⟩, ⟨s!"ao_{r}_{t}", bv 32⟩]
  for r in [0:rows] do
    for t in [0:taps] do
      body := body ++ [.inst "Tap" s!"tap_{r}_{t}"
        [ ("clk", .ref "clk"), ("rst", .ref "rst")
        , ("x_in", .ref (if t == 0 then s!"x_{r}" else s!"xo_{r}_{t-1}"))
        , ("acc_in", .ref (if t == 0 then "zero" else s!"ao_{r}_{t-1}"))
        , ("coef", .ref s!"c_{r}_{t}")
        , ("x_out", .ref s!"xo_{r}_{t}"), ("acc_out", .ref s!"ao_{r}_{t}") ]]
    outputs := outputs ++ [⟨s!"y_{r}", bv 32⟩]
    body := body ++ [.assign s!"y_{r}" (.ref s!"ao_{r}_{taps-1}")]
  return { name := s!"Fir{rows}x{taps}", inputs, outputs, wires, body, isPrimitive := false }

def firDesign (rows taps : Nat) : Design :=
  { topModule := s!"Fir{rows}x{taps}", modules := [tapModule, firTop rows taps] }

/-- Per-pixel temporal IIR filter with a threshold flag.  `thr` is a MEALY
    output (depends on the `pix` input) — fine, pixels are independent. -/
def pixModule : Module := {
  name := "PixIIR", isPrimitive := false
  inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"pix", bv 8⟩, ⟨"gain", bv 8⟩]
  outputs := [⟨"out", bv 8⟩, ⟨"thr", .bit⟩]
  wires := [⟨"y", bv 16⟩, ⟨"inc", bv 16⟩, ⟨"ynext", bv 16⟩, ⟨"hi", bv 8⟩]
  body := [
    .assign "inc" (.op .mul [.concat [.const 0 8, .ref "pix"], .concat [.const 0 8, .ref "gain"]]),
    .assign "ynext" (.op .add [.op .sub [.ref "y", .op .shr [.ref "y", .const 3 16]],
                               .op .shr [.ref "inc", .const 2 16]]),
    .register "y" "clk" ("rst", .synchronous) (.ref "ynext") 0,
    .assign "hi" (.slice (.ref "y") 15 8),
    .assign "out" (.ref "hi"),
    .assign "thr" (.op .gt_u [.ref "pix", .ref "hi"]) ] }

def pixTop (rows cols : Nat) : Module := Id.run do
  let mut inputs : List Port := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"gain", bv 8⟩]
  let mut outputs : List Port := []
  let mut body : List Stmt := []
  for r in [0:rows] do
    for c in [0:cols] do
      inputs := inputs ++ [⟨s!"p_{r}_{c}", bv 8⟩]
      outputs := outputs ++ [⟨s!"o_{r}_{c}", bv 8⟩, ⟨s!"t_{r}_{c}", .bit⟩]
      body := body ++ [.inst "PixIIR" s!"px_{r}_{c}"
        [ ("clk", .ref "clk"), ("rst", .ref "rst"), ("pix", .ref s!"p_{r}_{c}")
        , ("gain", .ref "gain"), ("out", .ref s!"o_{r}_{c}"), ("thr", .ref s!"t_{r}_{c}") ]]
  return { name := s!"Pix{rows}x{cols}", inputs, outputs, wires := [], body, isPrimitive := false }

def pixDesign (rows cols : Nat) : Design :=
  { topModule := s!"Pix{rows}x{cols}", modules := [pixModule, pixTop rows cols] }

/-- Conway's Game of Life cell: 8 neighbour inputs (including diagonals),
    synchronous `load` of a seed pattern. -/
def lifeModule : Module :=
  let w4 (n : String) : Expr := .concat [.const 0 3, .ref n]
  let sum := (List.range 8).foldl (fun acc i => Expr.op .add [acc, w4 s!"n{i}"]) (.const 0 4)
  { name := "Life", isPrimitive := false
    inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"load", .bit⟩, ⟨"seed", .bit⟩] ++
      (List.range 8).map fun i => ⟨s!"n{i}", .bit⟩
    outputs := [⟨"alive_o", .bit⟩]
    wires := [⟨"alive", .bit⟩, ⟨"cnt", bv 4⟩, ⟨"rule", .bit⟩]
    body := [
      .assign "cnt" sum,
      .assign "rule" (.op .or [.op .eq [.ref "cnt", .const 3 4],
                               .op .and [.ref "alive", .op .eq [.ref "cnt", .const 2 4]]]),
      .register "alive" "clk" ("rst", .synchronous) (.op .mux [.ref "load", .ref "seed", .ref "rule"]) 0,
      .assign "alive_o" (.ref "alive") ] }

/-- Neighbour order n0..n7 = NW, N, NE, W, E, SW, S, SE. -/
def lifeOffsets : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

def lifeTop (n : Nat) : Module := Id.run do
  let mut inputs : List Port := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"load", .bit⟩]
  let mut outputs : List Port := []
  let mut wires : List Port := [⟨"dead", .bit⟩]
  let mut body : List Stmt := [.assign "dead" (.const 0 1)]
  for r in [0:n] do
    for c in [0:n] do
      inputs := inputs ++ [⟨s!"s_{r}_{c}", .bit⟩]
      outputs := outputs ++ [⟨s!"a_{r}_{c}", .bit⟩]
  for r in [0:n] do
    for c in [0:n] do
      let nb := (List.range 8).map fun i =>
        let (dr, dc) := lifeOffsets[i]!
        let rr : Int := Int.ofNat r + dr
        let cc : Int := Int.ofNat c + dc
        let src := if rr < 0 || cc < 0 || rr ≥ Int.ofNat n || cc ≥ Int.ofNat n then "dead"
          else s!"a_{rr.toNat}_{cc.toNat}"
        (s!"n{i}", Expr.ref src)
      body := body ++ [.inst "Life" s!"life_{r}_{c}"
        ([ ("clk", .ref "clk"), ("rst", .ref "rst"), ("load", .ref "load")
         , ("seed", .ref s!"s_{r}_{c}") ] ++ nb ++ [("alive_o", .ref s!"a_{r}_{c}")])]
  return { name := s!"Life{n}x{n}", inputs, outputs, wires, body, isPrimitive := false }

def lifeDesign (n : Nat) : Design :=
  { topModule := s!"Life{n}x{n}", modules := [lifeModule, lifeTop n] }

/-! Rejection fixtures -/

/-- Combinational pass-through (Mealy output). -/
def combPassModule : Module := {
  name := "CombPass", isPrimitive := false
  inputs := [⟨"x", bv 32⟩], outputs := [⟨"y", bv 32⟩], wires := []
  body := [.assign "y" (.op .add [.ref "x", .const 1 32])] }

def mealyChainDesign : Design :=
  { topModule := "MealyChain"
  , modules := [combPassModule,
      { name := "MealyChain", isPrimitive := false
        inputs := [⟨"xin", bv 32⟩], outputs := [⟨"yout", bv 32⟩]
        wires := [⟨"w0", bv 32⟩, ⟨"w1", bv 32⟩]
        body := [
          .inst "CombPass" "c_0" [("x", .ref "xin"), ("y", .ref "w0")],
          .inst "CombPass" "c_1" [("x", .ref "w0"), ("y", .ref "w1")],
          .inst "CombPass" "c_2" [("x", .ref "w1"), ("y", .ref "yout")] ] }] }

/-- 3×3 mesh where the bottom-right PE's psum comes from pe_0_0 (not its
    upper neighbour) — not translation-invariant. -/
def irregularDesign : Design :=
  { topModule := "Mesh3x3", modules := [peModule, meshTop 3 none (longLink := true)] }

/-- 3×3 mesh with one cell of a different module. -/
def heteroDesign : Design :=
  { topModule := "Mesh3x3"
  , modules := [peModule, { peModule with name := "PE2" }, meshTop 3 (some (1, 1, "PE2"))] }

/-- A top-level register next to the cells. -/
def topRegDesign : Design :=
  let t := meshTop 2
  { topModule := t.name
  , modules := [peModule, { t with
      wires := t.wires ++ [⟨"cnt", bv 8⟩]
      body := t.body ++ [.register "cnt" "clk" ("rst", .synchronous) (.op .add [.ref "cnt", .const 1 8]) 0] }] }

end Sparkle.Test.CudaArray
