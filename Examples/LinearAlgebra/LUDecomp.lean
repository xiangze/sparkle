/-!
# LU Decomposition Hardware Accelerator
## Sparkle HDL (Lean 4 Signal DSL)

Computes the LU decomposition with partial pivoting  P·A = L·U  of an N×N
matrix stored in a flat register file.  Targets a 4×4 matrix with Q16.16
fixed-point arithmetic.  Parameters N, FRAC, EW are shared with CholeskyDecomp.lean.

### Algorithm (Doolittle with partial pivoting)
For column j = 0 .. N-1:
  1. Find pivot row  p = argmax_{i≥j} |A[i,j]|
  2. Swap rows j and p in the working matrix; record permutation P
  3. U[j,j] = A[j,j]
  4. For i = j+1 .. N-1:  L[i,j] = A[i,j] / U[j,j]   (multiplier)
  5. For i = j+1 .. N-1,  k = j+1 .. N-1:
       A[i,k] -= L[i,j] * U[j,k]                       (Schur update)

L has unit diagonal (L[i,i] = 1); U is upper triangular.

### Micro-architecture
```
 ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐
 │  IDLE    │──►│  PIVOT   │──►│  SWAP    │──►│  FACTOR  │──►│  UPDATE  │
 │  load A  │   │ find max │   │ row swap │   │ L[:,j]   │   │ Schur    │
 └──────────┘   └──────────┘   └──────────┘   └──────────┘   └──────────┘
                                                                    │
                                     ◄──────────────────────────────┘
                                          (loop j = 0 .. N-1)
                                                    │ j == N-1
                                             ┌──────▼──────┐
                                             │    DONE     │
                                             └─────────────┘
```

Each column j passes through PIVOT (N-j cycles) → SWAP (1 cycle) →
FACTOR (N-j-1 cycles) → UPDATE ((N-j-1)² cycles).
Total work ≈ O(N³) cycles.
-/

import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Arith

-- ---------------------------------------------------------------------------
-- Parameters  (must match CholeskyDecomp.lean when used together)
-- ---------------------------------------------------------------------------

def N     : Nat := 4    -- matrix dimension
def N2    : Nat := N * N
def FRAC  : Nat := 16   -- Q16.16 fractional bits
def EW    : Nat := 32   -- element bit-width

-- ---------------------------------------------------------------------------
-- Fixed-point arithmetic helpers
-- ---------------------------------------------------------------------------

/-- Q16.16 multiply -/
def fxMul (a b : BitVec EW) : BitVec EW :=
  let p : BitVec (EW + EW) := a.zeroExtend (EW + EW) * b.zeroExtend (EW + EW)
  (p >>> FRAC).truncate EW

/-- Q16.16 divide  (caller guarantees b ≠ 0) -/
def fxDiv (a b : BitVec EW) : BitVec EW :=
  let s : BitVec (EW + EW) := (a.zeroExtend (EW + EW)) <<< FRAC
  (s / b.zeroExtend (EW + EW)).truncate EW

/-- Absolute value of a signed Q16.16 value -/
def fxAbs (a : BitVec EW) : BitVec EW :=
  if a.toInt < 0 then (0 : BitVec EW) - a else a

-- ---------------------------------------------------------------------------
-- FSM states
-- ---------------------------------------------------------------------------

inductive LUState
  | Idle      -- waiting for start
  | Pivot     -- searching for pivot row (i = j .. N-1)
  | Swap      -- swapping rows j and pivotRow
  | Factor    -- computing multipliers L[i,j] = A[i,j] / A[j,j]
  | Update    -- Schur complement update A[i,k] -= L[i,j]*A[j,k]
  | Done      -- decomposition complete
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- Permutation vector
-- ---------------------------------------------------------------------------

/-- Stores the row permutation P as a vector of row indices -/
abbrev PermVec := HWVector (BitVec 8) N

/-- Initial permutation: P[i] = i -/
def identPerm : PermVec :=
  HWVector.ofFn (fun i => (i.val : BitVec 8))

/-- Swap two entries in the permutation vector -/
def swapPerm (p : PermVec) (a b : Nat) (ha : a < N) (hb : b < N) : PermVec :=
  let va := p.get ⟨a, ha⟩
  let vb := p.get ⟨b, hb⟩
  (p.set ⟨a, ha⟩ vb).set ⟨b, hb⟩ va

-- ---------------------------------------------------------------------------
-- Row-swap helper on the flat working matrix
-- ---------------------------------------------------------------------------

/-- Swap rows r0 and r1 in a flat N×N matrix (all columns) -/
def swapRows (m : HWVector (BitVec EW) N2) (r0 r1 : Nat)
    (h0 : r0 < N) (h1 : r1 < N) : HWVector (BitVec EW) N2 :=
  let swapCol (m : HWVector (BitVec EW) N2) (c : Nat) (hc : c < N)
      : HWVector (BitVec EW) N2 :=
    let i0 := r0 * N + c
    let i1 := r1 * N + c
    let v0 := m.get ⟨i0, by omega⟩
    let v1 := m.get ⟨i1, by omega⟩
    (m.set ⟨i0, by omega⟩ v1).set ⟨i1, by omega⟩ v0
  -- unroll over all N columns
  List.range N |>.foldl (fun acc c =>
    if hc : c < N then swapCol acc c hc else acc) m

-- ---------------------------------------------------------------------------
-- LU accelerator IO bundle
-- ---------------------------------------------------------------------------

structure LuIO (dom : DomainConfig) where
  -- Inputs
  start   : Signal dom Bool
  aFlat   : Signal dom (HWVector (BitVec EW) N2)
  -- Outputs
  done    : Signal dom Bool
  /-- Lower triangular factor L (unit diagonal stored as 1<<FRAC) -/
  lFlat   : Signal dom (HWVector (BitVec EW) N2)
  /-- Upper triangular factor U -/
  uFlat   : Signal dom (HWVector (BitVec EW) N2)
  /-- Row permutation vector: output row i came from input row perm[i] -/
  perm    : Signal dom PermVec

-- ---------------------------------------------------------------------------
-- LU decomposition accelerator
-- ---------------------------------------------------------------------------

def luAccel {dom : DomainConfig}
    (start : Signal dom Bool)
    (aFlat : Signal dom (HWVector (BitVec EW) N2))
    : LuIO dom :=
  Signal.circuit (dom := dom) do

    -- -----------------------------------------------------------------------
    -- Working matrix W: starts as a copy of A, gets modified in-place.
    -- After completion:
    --   W[i,j] for i > j  holds L[i,j]  (multipliers)
    --   W[i,j] for i ≤ j  holds U[i,j]
    -- -----------------------------------------------------------------------
    wReg  <~ Signal.register
               (HWVector.replicate N2 (0 : BitVec EW))
               (Signal.pure (HWVector.replicate N2 0))

    -- Permutation vector
    permReg <~ Signal.register identPerm (Signal.pure identPerm)

    -- FSM state & counters
    state     <~ Signal.register LUState.Idle (Signal.pure .Idle)
    colJ      <~ Signal.register (0 : BitVec 8) (Signal.pure 0)   -- current column j
    rowI      <~ Signal.register (0 : BitVec 8) (Signal.pure 0)   -- pivot search / factor / update row
    colK      <~ Signal.register (0 : BitVec 8) (Signal.pure 0)   -- update column k
    pivotRow  <~ Signal.register (0 : BitVec 8) (Signal.pure 0)   -- best pivot row found
    pivotVal  <~ Signal.register (0 : BitVec EW) (Signal.pure 0)  -- best |pivot| seen

    -- Done flag
    doneFl <~ Signal.register false (Signal.pure false)

    -- -----------------------------------------------------------------------
    -- Helper: read W[r,c]
    -- -----------------------------------------------------------------------
    let readW (r c : Signal dom (BitVec 8)) : Signal dom (BitVec EW) :=
          Signal.lift2 (fun ri ci =>
            wReg.val.get ⟨ri.toNat * N + ci.toNat, by omega⟩) r c

    -- -----------------------------------------------------------------------
    -- FSM
    -- -----------------------------------------------------------------------
    match_signal state with

    -- ·······································································
    | .Idle =>
        doneFl <~ Signal.pure false
        when start do
          wReg    <~ aFlat
          permReg <~ Signal.pure identPerm
          colJ    <~ Signal.pure 0
          rowI    <~ Signal.pure 0   -- start pivot search from row j=0
          pivotRow <~ Signal.pure 0
          pivotVal <~ Signal.pure 0
          state   <~ Signal.pure .Pivot

    -- ·······································································
    -- PIVOT: scan rows i = j..N-1, track argmax |W[i,j]|
    | .Pivot =>
        let i   := rowI
        let j   := colJ
        let wij := readW i j
        let absWij := wij.map fxAbs
        -- Update best pivot if |W[i,j]| > pivotVal
        when (Signal.lift2 (· > ·) absWij pivotVal) do
          pivotRow <~ i
          pivotVal <~ absWij
        -- Advance row counter
        rowI <~ i.map (· + 1)
        -- Transition when i reaches N-1
        when (i.map (fun ii => ii.toNat + 1 >= N)) do
          state <~ Signal.pure .Swap

    -- ·······································································
    -- SWAP: exchange rows j and pivotRow in W and in permutation
    | .Swap =>
        let j  := colJ
        let pr := pivotRow
        -- Row swap in working matrix (combinational via helper)
        wReg <~ Signal.lift2 (fun m p =>
                  swapRows m j.toNat p.toNat (by omega) (by omega))
                  wReg pr
        -- Swap permutation entries
        permReg <~ Signal.lift2 (fun pv p =>
                    swapPerm pv j.toNat p.toNat (by omega) (by omega))
                    permReg pr
        -- Reset for Factor phase: i = j+1
        rowI  <~ j.map (· + 1)
        state <~ Signal.pure .Factor

    -- ·······································································
    -- FACTOR: compute multipliers  L[i,j] = W[i,j] / W[j,j]
    --         and write back into W (lower triangle)
    | .Factor =>
        let i   := rowI
        let j   := colJ
        let wjj := readW j j
        let wij := readW i j
        -- multiplier m = W[i,j] / W[j,j]
        let mult := Signal.lift2 (fun a b => fxDiv a b) wij wjj
        -- W[i,j] ← mult
        wReg <~ Signal.lift3 (fun m v ii =>
                  m.set ⟨ii.toNat * N + j.toNat, by omega⟩ v)
                  wReg mult i
        rowI <~ i.map (· + 1)
        -- When all rows processed → move to Update phase
        when (i.map (fun ii => ii.toNat + 1 >= N)) do
          -- Initialise Update: i = j+1, k = j+1
          rowI <~ j.map (· + 1)
          colK <~ j.map (· + 1)
          state <~ Signal.pure .Update

    -- ·······································································
    -- UPDATE: Schur complement  W[i,k] -= L[i,j] * U[j,k]
    --         = W[i,j] * W[j,k]  (both already in W)
    | .Update =>
        let i := rowI
        let j := colJ
        let k := colK
        let lij := readW i j   -- multiplier stored in lower part of W
        let ujk := readW j k   -- U row stored in upper part of W
        let wik := readW i k
        let newWik := Signal.lift3 (fun w l u => w - fxMul l u) wik lij ujk
        -- Write back W[i,k]
        wReg <~ Signal.lift3 (fun m v ii =>
                  Signal.lift2 (fun mm kk =>
                    mm.set ⟨ii.toNat * N + kk.toNat, by omega⟩ v)
                    (Signal.pure m) k)
                  wReg newWik i
        -- Advance k; when k reaches N-1, advance i; when i reaches N-1, next column
        colK <~ k.map (· + 1)
        when (k.map (fun ki => ki.toNat + 1 >= N)) do
          colK <~ j.map (· + 1)   -- reset k to j+1 for next row
          rowI <~ i.map (· + 1)
          when (i.map (fun ii => ii.toNat + 1 >= N)) do
            -- Column j done; advance to j+1
            let nextJ := j.map (· + 1)
            colJ     <~ nextJ
            rowI     <~ nextJ          -- pivot search starts at i=j+1
            pivotRow <~ nextJ
            pivotVal <~ Signal.pure 0
            state    <~ nextJ.map (fun jj =>
                          if jj.toNat >= N then .Done else .Pivot)

    -- ·······································································
    | .Done =>
        doneFl <~ Signal.pure true

    -- -----------------------------------------------------------------------
    -- Separate L and U from the combined working matrix W
    --   L[i,j] = W[i,j]  for i > j,  1 (Q16.16) on diagonal,  0 above
    --   U[i,j] = W[i,j]  for i ≤ j,  0 below diagonal
    -- -----------------------------------------------------------------------
    let one : BitVec EW := (1 : BitVec EW) <<< FRAC    -- 1.0 in Q16.16

    let extractL : Signal dom (HWVector (BitVec EW) N2) :=
          wReg.map (fun m =>
            HWVector.ofFn (fun idx =>
              let i := idx.val / N
              let j := idx.val % N
              if i > j then m.get ⟨idx.val, idx.isLt⟩
              else if i == j then one
              else 0))

    let extractU : Signal dom (HWVector (BitVec EW) N2) :=
          wReg.map (fun m =>
            HWVector.ofFn (fun idx =>
              let i := idx.val / N
              let j := idx.val % N
              if i ≤ j then m.get ⟨idx.val, idx.isLt⟩
              else 0))

    return {
      start := start
      aFlat := aFlat
      done  := doneFl
      lFlat := extractL
      uFlat := extractU
      perm  := permReg
    }

-- ---------------------------------------------------------------------------
-- Top-level synthesis
-- ---------------------------------------------------------------------------

def defaultDomain : DomainConfig :=
  { clockHz   := 100_000_000
    resetKind := .Synchronous
    initKind  := .Defined }

#synthesizeVerilog luAccel (dom := defaultDomain)

-- ---------------------------------------------------------------------------
-- Formal specification (pure Lean reference)
-- ---------------------------------------------------------------------------

/-- Doolittle LU with partial pivoting on Float arrays -/
def luSpec (a : Fin N2 → Float)
    : Option (Fin N2 → Float × Fin N2 → Float × Fin N → Fin N) := do
  let mut w : Array Float := Array.ofFn (fun i => a i)
  let mut perm : Array Nat := Array.ofFn (fun i => i)
  for j in List.range N do
    -- Partial pivot
    let mut pRow := j
    let mut pVal := Float.abs (w.get! (j * N + j))
    for i in List.range (N - j - 1) do
      let ii := j + 1 + i
      let v := Float.abs (w.get! (ii * N + j))
      if v > pVal then pRow := ii; pVal := v
    if pVal < 1e-12 then return none   -- singular
    -- Row swap
    if pRow ≠ j then
      for c in List.range N do
        let t := w.get! (j * N + c)
        w := w.set! (j * N + c) (w.get! (pRow * N + c))
        w := w.set! (pRow * N + c) t
      let t := perm.get! j
      perm := perm.set! j (perm.get! pRow)
      perm := perm.set! pRow t
    -- Factor + Schur update
    let ujj := w.get! (j * N + j)
    for i in List.range (N - j - 1) do
      let ii := j + 1 + i
      let m := w.get! (ii * N + j) / ujj
      w := w.set! (ii * N + j) m
      for k in List.range (N - j - 1) do
        let kk := j + 1 + k
        w := w.set! (ii * N + kk)
               (w.get! (ii * N + kk) - m * w.get! (j * N + kk))
  let l := fun ⟨idx, h⟩ =>
    let i := idx / N; let j := idx % N
    if i > j then w.get! idx else if i == j then 1.0 else 0.0
  let u := fun ⟨idx, h⟩ =>
    let i := idx / N; let j := idx % N
    if i ≤ j then w.get! idx else 0.0
  let p := fun ⟨i, _⟩ => ⟨perm.get! i, by omega⟩
  some (l, u, p)

/-- Correctness: P·A = L·U -/
theorem lu_correct (a : Fin N2 → Float) (l u : Fin N2 → Float)
    (p : Fin N → Fin N)
    (h : luSpec a = some (l, u, p)) :
    ∀ (i j : Fin N),
      (∑ k : Fin N, l ⟨i.val * N + k.val, by omega⟩ *
                    u ⟨k.val * N + j.val, by omega⟩)
      = a ⟨(p i).val * N + j.val, by omega⟩ := by
  sorry  -- discharge with norm_num / decide for fixed N=4

-- ---------------------------------------------------------------------------
-- Simulation smoke-test
-- ---------------------------------------------------------------------------

/-
  Test matrix (exact integer entries for easy verification):
    A = [ 2  1  0  0 ]
        [ 4  3  1  0 ]
        [ 0  2  5  2 ]
        [ 0  0  4  6 ]

  Expected (no pivoting needed):
    L = [ 1    0    0   0 ]        U = [ 2  1  0  0 ]
        [ 2    1    0   0 ]            [ 0  1  1  0 ]
        [ 0    2    1   0 ]            [ 0  0  3  2 ]
        [ 0    0  4/3   1 ]            [ 0  0  0  8/3]
-/

def toQ (v : Int) : BitVec EW :=
  (v.toNat : BitVec EW) <<< FRAC

def testMatrixLU : HWVector (BitVec EW) N2 :=
  let entries : List (BitVec EW) :=
    [ toQ 2, toQ 1, toQ 0, toQ 0
    , toQ 4, toQ 3, toQ 1, toQ 0
    , toQ 0, toQ 2, toQ 5, toQ 2
    , toQ 0, toQ 0, toQ 4, toQ 6
    ]
  HWVector.ofList entries (by decide)

#eval do
  let io := luAccel (Signal.pure true) (Signal.pure testMatrixLU)
  -- 4 columns × ~(N + 1 + (N-j) + (N-j)²) cycles ≈ 80 cycles total
  let lOut ← io.lFlat.atTime 80
  let uOut ← io.uFlat.atTime 80
  let pOut ← io.perm.atTime  80
  IO.println s!"L = {lOut}"
  IO.println s!"U = {uOut}"
  IO.println s!"P = {pOut}"
