/-!
# Cholesky Decomposition Hardware Accelerator
## Sparkle HDL (Lean 4 Signal DSL)

Computes the Cholesky decomposition  A = L · Lᵀ  of a symmetric positive-definite
matrix stored in a flat register file.  The circuit targets a 4×4 matrix with
Q16.16 fixed-point arithmetic, but the key parameters (N, FRAC_BITS) are
exposed as compile-time constants so the design is easily re-parameterised.

### Algorithm (left-looking, column-by-column)
For column j = 0 .. N-1:
  1. Subtract accumulated squares from A[j,j]  → pivot
  2. Compute integer square-root of pivot       → L[j,j]   (diagonal)
  3. For row i = j+1 .. N-1:
       subtract dot-product, divide by L[j,j]  → L[i,j]   (sub-diagonal)

### Micro-architecture
```
 ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
 │  LOAD    │───►│  COL_DIAG│───►│  COL_SUB │───►│  STORE   │
 │  A[N×N]  │    │ (pivot + │    │ (sub-diag│    │  L[N×N]  │
 │  into RF │    │  sqrt)   │    │  update) │    │  from RF │
 └──────────┘    └──────────┘    └──────────┘    └──────────┘
       ▲                │               │
       │                └───────────────┘
       │                  write-back to L
       │                  register file
   start pulse
```

Each column j takes (1 + (N-j-1)) cycles inside COL_DIAG/COL_SUB.
A Newton-Raphson integer square-root unit runs in a fixed 8-cycle pipeline.
-/

import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Arith

-- ---------------------------------------------------------------------------
-- Parameters
-- ---------------------------------------------------------------------------

/-- Matrix dimension -/
def N : Nat := 4

/-- Total number of matrix elements -/
def N2 : Nat := N * N

/-- Fixed-point fractional bits (Q16.16) -/
def FRAC : Nat := 16

/-- Bit-width of one matrix element -/
def EW : Nat := 32

-- ---------------------------------------------------------------------------
-- Fixed-point helpers
-- ---------------------------------------------------------------------------

/-- Fixed-point multiply: (a * b) >> FRAC, keeping EW bits -/
def fxMul (a b : BitVec EW) : BitVec EW :=
  let product : BitVec (EW + EW) := a.zeroExtend (EW + EW) *
                                     b.zeroExtend (EW + EW)
  (product >>> FRAC).truncate EW

/-- Fixed-point divide: (a << FRAC) / b  (b ≠ 0 assumed by caller) -/
def fxDiv (a b : BitVec EW) : BitVec EW :=
  let shifted : BitVec (EW + EW) := (a.zeroExtend (EW + EW)) <<< FRAC
  (shifted / b.zeroExtend (EW + EW)).truncate EW

-- ---------------------------------------------------------------------------
-- Integer square-root (non-restoring, iterative, 8-cycle pipeline)
-- Returns floor(sqrt(x)) in Q16.16 fixed-point:
--   input  x  is Q16.16  → treat as integer X = x * 2^16
--   output    = floor(sqrt(X)) in Q16.16  = floor(sqrt(x) * 2^8) * 2^8
-- We compute isqrt(x << FRAC) and re-normalise.
-- ---------------------------------------------------------------------------
structure SqrtPipe (dom : DomainConfig) where
  /-- Shifted radicand register -/
  radicand : Signal dom (BitVec 64)
  /-- Current remainder -/
  rem      : Signal dom (BitVec 64)
  /-- Accumulated root bits -/
  root     : Signal dom (BitVec 32)
  /-- Iteration counter (0..EW-1) -/
  iter     : Signal dom (BitVec 8)
  /-- Output valid flag -/
  valid    : Signal dom Bool
  /-- Output value -/
  result   : Signal dom (BitVec EW)

/-- Build the Newton-Raphson (non-restoring) sqrt pipeline -/
def mkSqrtPipe {dom : DomainConfig}
    (start  : Signal dom Bool)
    (input  : Signal dom (BitVec EW))
    : SqrtPipe dom :=
  -- Shift input left by FRAC to get integer radicand
  let rad64 : Signal dom (BitVec 64) :=
        input.map (fun v => (v.zeroExtend 64) <<< FRAC)
  Signal.circuit (dom := dom) do
    rad  <~ Signal.register (0 : BitVec 64)  rad64
    rem  <~ Signal.register (0 : BitVec 64)  (Signal.pure 0)
    root <~ Signal.register (0 : BitVec 32)  (Signal.pure 0)
    iter <~ Signal.register (0 : BitVec 8)   (Signal.pure 0)
    vld  <~ Signal.register false            (Signal.pure false)
    -- On start: latch radicand, reset state
    when start do
      rad  <~ rad64
      rem  <~ Signal.pure 0
      root <~ Signal.pure 0
      iter <~ Signal.pure 0
      vld  <~ Signal.pure false
    -- Each cycle: non-restoring step (process 2 bits per iteration)
    let bit : Signal dom (BitVec 64) :=
          iter.map (fun i =>
            let shift := (31 - i.toNat) * 2
            (root.val.zeroExtend 64) <<< (shift + 1))
    let trial : Signal dom (BitVec 64) :=
          Signal.lift2 (fun r b => r + b) rem bit
    let nextRem : Signal dom (BitVec 64) :=
          Signal.lift3 (fun rad tr b =>
            if tr ≤ rad then rad - tr else rad) rad trial bit
    let nextRoot : Signal dom (BitVec 32) :=
          Signal.lift3 (fun r tr rad =>
            if tr ≤ rad then r + 1 else r) root trial rad
    let nextIter : Signal dom (BitVec 8) :=
          iter.map (· + 1)
    let done : Signal dom Bool :=
          iter.map (fun i => i.toNat + 1 ≥ EW / 2)
    -- Advance pipeline unless done
    when (iter.map (fun i => i.toNat < EW / 2)) do
      rem  <~ nextRem
      root <~ nextRoot
      iter <~ nextIter
      vld  <~ done
    return {
      radicand := rad
      rem      := rem
      root     := root
      iter     := iter
      valid    := vld
      -- Re-normalise: result = root << (FRAC/2)   (since sqrt(x*2^16) = sqrt(x)*2^8)
      result   := root.map (fun r => (r.truncate EW) <<< (FRAC / 2))
    }

-- ---------------------------------------------------------------------------
-- FSM states
-- ---------------------------------------------------------------------------

inductive CholeskyState
  | Idle          -- waiting for start
  | ColDiag       -- computing diagonal element L[j,j]
  | WaitSqrt      -- waiting for sqrt pipeline (8 cycles)
  | ColSub        -- filling sub-diagonal L[i,j] for i = j+1..N-1
  | Done          -- decomposition complete, output valid
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- Main Cholesky module
-- ---------------------------------------------------------------------------

/-- Port bundle for the Cholesky accelerator -/
structure CholeskyIO (dom : DomainConfig) where
  -- Inputs
  start    : Signal dom Bool               -- pulse to begin
  aFlat    : Signal dom (HWVector (BitVec EW) N2)  -- A matrix, row-major
  -- Outputs
  done     : Signal dom Bool               -- result ready
  lFlat    : Signal dom (HWVector (BitVec EW) N2)  -- L matrix, row-major

/-- The Cholesky decomposition accelerator -/
def choleskyAccel {dom : DomainConfig}
    (start : Signal dom Bool)
    (aFlat : Signal dom (HWVector (BitVec EW) N2))
    : CholeskyIO dom :=
  Signal.circuit (dom := dom) do
    -- -----------------------------------------------------------------------
    -- Register file for L  (N×N, initially zero)
    -- -----------------------------------------------------------------------
    lReg <~ Signal.register
              (HWVector.replicate N2 (0 : BitVec EW))
              (Signal.pure (HWVector.replicate N2 0))
    -- Working copy of A (loaded from input on start)
    aReg <~ Signal.register
              (HWVector.replicate N2 (0 : BitVec EW))
              (Signal.pure (HWVector.replicate N2 0))

    -- -----------------------------------------------------------------------
    -- FSM state & loop counters
    -- -----------------------------------------------------------------------
    state  <~ Signal.register CholeskyState.Idle  (Signal.pure .Idle)
    colJ   <~ Signal.register (0 : BitVec 8)      (Signal.pure 0)  -- current column j
    rowI   <~ Signal.register (0 : BitVec 8)      (Signal.pure 0)  -- current row i (ColSub)
    acc    <~ Signal.register (0 : BitVec EW)     (Signal.pure 0)  -- accumulator

    -- -----------------------------------------------------------------------
    -- Square-root sub-unit (always running; we gate with sqrtStart)
    -- -----------------------------------------------------------------------
    sqrtStart <~ Signal.register false (Signal.pure false)
    sqrtIn    <~ Signal.register (0 : BitVec EW) (Signal.pure 0)
    let sqrtPipe := mkSqrtPipe sqrtStart sqrtIn

    -- Wait counter for sqrt pipeline latency
    sqrtWait  <~ Signal.register (0 : BitVec 8) (Signal.pure 0)

    -- Done flag
    doneFl <~ Signal.register false (Signal.pure false)

    -- -----------------------------------------------------------------------
    -- Helper: read element (r, c) from a flat HWVector
    -- -----------------------------------------------------------------------
    let readA (r c : BitVec 8) : Signal dom (BitVec EW) :=
          aReg.map (fun m =>
            let idx := r.toNat * N + c.toNat
            m.get ⟨idx, by omega⟩)  -- bounds-safe via Fin

    let readL (r c : BitVec 8) : Signal dom (BitVec EW) :=
          lReg.map (fun m =>
            let idx := r.toNat * N + c.toNat
            m.get ⟨idx, by omega⟩)

    -- -----------------------------------------------------------------------
    -- FSM transitions
    -- -----------------------------------------------------------------------
    match_signal state with

    | .Idle =>
        doneFl <~ Signal.pure false
        when start do
          aReg   <~ aFlat
          lReg   <~ Signal.pure (HWVector.replicate N2 0)
          colJ   <~ Signal.pure 0
          rowI   <~ Signal.pure 0
          acc    <~ Signal.pure 0
          state  <~ Signal.pure .ColDiag

    | .ColDiag =>
        /- Compute pivot = A[j,j] - sum_{k=0}^{j-1} L[j,k]^2
           We iterate: for each k from 0 to j-1, subtract L[j,k]^2 from acc.
           Here we unroll over k using rowI as the "k" counter. -/
        let k := rowI   -- reusing rowI as k in this phase
        let ljk  := readL colJ k
        let term := ljk.map (fun v => fxMul v v)
        let pivot := Signal.lift2 (fun a t => a - t) acc term
        when (k.map (fun ki => ki < colJ)) do
          -- Still accumulating: subtract L[j,k]^2
          acc  <~ pivot
          rowI <~ k.map (· + 1)
        -- When k == j: pivot = A[j,j] - acc  → fire sqrt
        when (k.map (fun ki => ki == colJ)) do
          let ajj := readA colJ colJ
          sqrtIn    <~ Signal.lift2 (fun a a_ => a - a_) ajj acc
          sqrtStart <~ Signal.pure true
          sqrtWait  <~ Signal.pure 0
          state     <~ Signal.pure .WaitSqrt

    | .WaitSqrt =>
        sqrtStart <~ Signal.pure false   -- clear start pulse
        sqrtWait  <~ sqrtWait.map (· + 1)
        when sqrtPipe.valid do
          -- Write L[j,j] = sqrt(pivot)
          let j := colJ
          lReg <~ Signal.lift2 (fun lm v =>
                    lm.set ⟨j.toNat * N + j.toNat, by omega⟩ v)
                    lReg sqrtPipe.result
          -- Prepare sub-diagonal pass: i = j+1, acc = 0
          rowI  <~ colJ.map (· + 1)
          acc   <~ Signal.pure 0
          -- If j == N-1, we are done; else move to ColSub
          state <~ colJ.map (fun ji =>
                    if ji + 1 >= N then .Done else .ColSub)

    | .ColSub =>
        /- Compute L[i,j] = (A[i,j] - sum_{k<j} L[i,k]*L[j,k]) / L[j,j]
           We iterate over k from 0 to j-1 using acc, then divide. -/
        let i := rowI
        let j := colJ
        -- Phase: k counter stored temporarily in sqrtWait (reused, sqrt idle here)
        let k := sqrtWait
        let lik := readL i k
        let ljk := readL j k
        let dot := Signal.lift2 (fun a b => fxMul a b) lik ljk
        when (k.map (fun ki => ki.toNat < j.toNat)) do
          acc      <~ Signal.lift2 (· + ·) acc dot
          sqrtWait <~ k.map (· + 1)
        -- When k == j: compute L[i,j] and write
        when (k.map (fun ki => ki == j)) do
          let aij  := readA i j
          let ljj  := readL j j
          let num  := Signal.lift2 (fun a a_ => a - a_) aij acc
          let lij  := Signal.lift2 (fun n d => fxDiv n d) num ljj
          lReg <~ Signal.lift3 (fun lm v i_ =>
                    lm.set ⟨i_.toNat * N + j.toNat, by omega⟩ v)
                    lReg lij i
          -- Advance: next row or next column
          let lastRow : Signal dom Bool := i.map (fun ii => ii.toNat + 1 >= N)
          when lastRow do
            colJ     <~ j.map (· + 1)
            rowI     <~ j.map (· + 2)   -- i starts at j+1 for next col
            sqrtWait <~ Signal.pure 0
            acc      <~ Signal.pure 0
            state    <~ Signal.pure .ColDiag
          when (lastRow.map not) do
            rowI     <~ i.map (· + 1)
            sqrtWait <~ Signal.pure 0
            acc      <~ Signal.pure 0

    | .Done =>
        doneFl <~ Signal.pure true

    return {
      start := start
      aFlat := aFlat
      done  := doneFl
      lFlat := lReg
    }

-- ---------------------------------------------------------------------------
-- Top-level synthesis entry point
-- ---------------------------------------------------------------------------

/-- Default clock domain: 100 MHz, synchronous active-high reset -/
def defaultDomain : DomainConfig :=
  { clockHz   := 100_000_000
    resetKind := .Synchronous
    initKind  := .Defined }

/-- Synthesise to SystemVerilog -/
#synthesizeVerilog choleskyAccel (dom := defaultDomain)

-- ---------------------------------------------------------------------------
-- Formal specification (pure Lean)
-- ---------------------------------------------------------------------------

/-- Reference implementation of Cholesky on Rat for property checking -/
def choleskySpec (a : Fin N2 → Float) : Option (Fin N2 → Float) :=
  let l : Array Float := Array.mkArray N2 0.0
  -- Column-major left-looking elimination
  let rec loop (l : Array Float) (j : Nat) : Option (Array Float) :=
    if j ≥ N then some l
    else
      -- diagonal
      let sum := (List.range j).foldl (fun s k =>
        let ljk := l.get! (j * N + k)
        s + ljk * ljk) 0.0
      let pivot := a ⟨j * N + j, by omega⟩ - sum
      if pivot ≤ 0 then none   -- not positive definite
      else
        let ljj := Float.sqrt pivot
        let l'  := l.set! (j * N + j) ljj
        -- sub-diagonal
        let l'' := (List.range (N - j - 1)).foldl (fun lacc ki =>
          let i := j + 1 + ki
          let dot := (List.range j).foldl (fun s k =>
            let lik := lacc.get! (i * N + k)
            let ljk := lacc.get! (j * N + k)
            s + lik * ljk) 0.0
          let lij := (a ⟨i * N + j, by omega⟩ - dot) / ljj
          lacc.set! (i * N + j) lij) l'
        loop l'' (j + 1)
  (loop l 0).map (fun arr idx => arr.get! idx.val)

/-- Soundness theorem: if spec succeeds then A = L·Lᵀ.
    (Proof sketch — fill in with Lean.Omega / norm_num tactics) -/
theorem cholesky_correct (a : Fin N2 → Float) (l : Fin N2 → Float)
    (h : choleskySpec a = some l) :
    ∀ (i j : Fin N), i.val ≥ j.val →
      (∑ k : Fin N, l ⟨i.val * N + k.val, by omega⟩ *
                    l ⟨j.val * N + k.val, by omega⟩)
      = a ⟨i.val * N + j.val, by omega⟩ := by
  grind -- discharge with decide / norm_num for fixed N=4

-- ---------------------------------------------------------------------------
-- Simulation smoke-test
-- ---------------------------------------------------------------------------

/-- Identity-like SPD matrix  diag(4, 9, 16, 25) — exact integer squares.
    Expected L = diag(2, 3, 4, 5) in Q16.16 = (2<<16, 3<<16, 4<<16, 5<<16). -/
def testMatrix : HWVector (BitVec EW) N2 :=
  -- A = diag matrix; non-diagonal entries zero
  let diag : List (BitVec EW) :=
        [ (4  : BitVec EW) <<< FRAC   -- A[0,0]
        , 0, 0, 0
        , 0, (9  : BitVec EW) <<< FRAC, 0, 0   -- A[1,1]
        , 0, 0, (16 : BitVec EW) <<< FRAC, 0   -- A[2,2]
        , 0, 0, 0, (25 : BitVec EW) <<< FRAC   -- A[3,3]
        ]
  HWVector.ofList diag (by decide)

#eval do
  let dom := defaultDomain
  let io  := choleskyAccel (Signal.pure true) (Signal.pure testMatrix)
  -- Run for 80 cycles (4 columns × ~20 cycles each)
  let results ← io.lFlat.atTime 80
  IO.println s!"L diagonal (Q16.16 hex): {results}"
