/-
  SystolicConv2d.lean — Systolic Array based 2D Convolution in Sparkle HDL

  This module rewrites the SDIP (Stable Diffusion Inference Processor)
  conv2d systolic array from Chisel/Scala into Lean 4 / Sparkle Signal DSL.

  Original: https://github.com/xiangze/SDIP/blob/main/src/main/scala/sdip/SDIP_conv2d.scala
  Target:   https://github.com/Verilean/sparkle

  Architecture:
    - Weight-stationary systolic array for 2D convolution
    - Configurable kernel size (e.g., 3×3), data width, array dimensions
    - Each PE (Processing Element) holds a weight and performs MAC
    - Input activations flow horizontally, partial sums flow vertically
    - Line buffer for sliding window over input feature map

  Chisel → Sparkle mapping:
    Chisel                          Sparkle Signal DSL
    ─────────────────────────────   ────────────────────────────────
    Module / class PE               def pe : Signal dom α
    RegInit(0.U)                    Signal.register 0#N
    io.out := reg                   (pure functional return)
    Wire / when / otherwise         Signal.mux / hw_cond
    Vec(n, UInt)                    HWVector (BitVec w) n
    Mem(size, UInt)                 Signal.memory
    for (i <- 0 until n)           Lean List/Vector recursion
    ShiftRegister(x, n)            chained Signal.register
-/

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain

open Sparkle.Core.Signal
open Sparkle.Core.Domain

-- ============================================================
-- Configuration (corresponds to SDIP's config parameters)
-- ============================================================

structure Conv2dConfig where
  dataWidth    : Nat := 8      -- activation/weight bit width
  accumWidth   : Nat := 32     -- accumulator bit width
  kernelSize   : Nat := 3      -- convolution kernel dimension (3 = 3×3)
  arrayRows    : Nat := 3      -- systolic array rows (= kernelSize)
  arrayCols    : Nat := 3      -- systolic array cols (= kernelSize)
  imgWidth     : Nat := 16     -- input image width
  imgHeight    : Nat := 16     -- input image height

-- ============================================================
-- Processing Element (PE)
-- ============================================================
-- Each PE in the weight-stationary systolic array:
--   - Stores one weight value (loaded during configuration phase)
--   - Receives activation from the left, passes it right
--   - Receives partial sum from above, adds (weight × activation), passes down
--
-- Chisel equivalent:
--   class PE extends Module {
--     val io = IO(new Bundle {
--       val in_act   = Input(UInt(8.W))
--       val in_psum  = Input(SInt(32.W))
--       val in_weight = Input(UInt(8.W))
--       val load_weight = Input(Bool())
--       val out_act  = Output(UInt(8.W))
--       val out_psum = Output(SInt(32.W))
--     })
--     val weight_reg = RegInit(0.U(8.W))
--     when(io.load_weight) { weight_reg := io.in_weight }
--     val product = (io.in_act * weight_reg).asSInt
--     io.out_psum := RegNext(io.in_psum + product)
--     io.out_act  := RegNext(io.in_act)
--   }

/-- A single Processing Element for the weight-stationary systolic array.
    Returns (output_activation, output_partial_sum) as registered outputs. -/
def systolicPE {dom : DomainConfig}
    (inAct     : Signal dom (BitVec 8))    -- activation input (from left)
    (inPsum    : Signal dom (BitVec 32))   -- partial sum input (from above)
    (inWeight  : Signal dom (BitVec 8))    -- weight to load
    (loadWeight : Signal dom Bool)          -- weight load enable
    : Signal dom (BitVec 8 × BitVec 32) :=
  -- Weight register: holds the stationary weight
  let weightReg := Signal.loop fun wReg =>
    Signal.mux loadWeight inWeight wReg
  -- Multiply: activation × weight (zero-extended to 32 bits)
  let product := (fun a w =>
    let a32 : BitVec 32 := BitVec.zeroExtend 32 a
    let w32 : BitVec 32 := BitVec.zeroExtend 32 w
    a32 * w32
  ) <$> inAct <*> weightReg
  -- Accumulate: partial_sum_in + product
  let outPsum := Signal.register (0#32) ((· + ·) <$> inPsum <*> product)
  -- Pass activation through (1-cycle delay for synchronization)
  let outAct := Signal.register (0#8) inAct
  -- Return tuple of (activation_out, psum_out)
  (fun a p => (a, p)) <$> outAct <*> outPsum

-- ============================================================
-- Systolic Array Row
-- ============================================================
-- Chain `cols` PEs horizontally. Activation flows left→right,
-- partial sums are per-PE (independent columns at this level).
--
-- Chisel equivalent:
--   val pes = VecInit(Seq.fill(cols)(Module(new PE)))
--   pes(0).io.in_act := row_input
--   for (i <- 1 until cols) { pes(i).io.in_act := pes(i-1).io.out_act }

/-- One row of the systolic array: chains `n` PEs with activation flowing left→right.
    Takes partial sums from above (one per column), returns updated partial sums. -/
def systolicRow {dom : DomainConfig} (n : Nat)
    (actInput : Signal dom (BitVec 8))          -- activation entering from left
    (psumsIn  : List (Signal dom (BitVec 32)))  -- partial sums from row above (length = n)
    (weights  : List (Signal dom (BitVec 8)))   -- weights for this row (length = n)
    (loadW    : Signal dom Bool)                 -- weight load enable
    : List (Signal dom (BitVec 32)) × Signal dom (BitVec 8) :=
  -- Fold over columns, threading activation through
  let init : Signal dom (BitVec 8) × List (Signal dom (BitVec 32)) :=
    (actInput, [])
  let result := (List.zip psumsIn weights).foldl
    (fun (acc : Signal dom (BitVec 8) × List (Signal dom (BitVec 32)))
         (pair : Signal dom (BitVec 32) × Signal dom (BitVec 8)) =>
      let (curAct, accPsums) := acc
      let (psumIn, w) := pair
      let peOut := systolicPE curAct psumIn w loadW
      let nextAct := (fun p => p.1) <$> peOut
      let nextPsum := (fun p => p.2) <$> peOut
      (nextAct, accPsums ++ [nextPsum])
    ) init
  (result.2, result.1)

-- ============================================================
-- Full Systolic Array (rows × cols)
-- ============================================================
-- Stacks rows vertically. Partial sums flow top→bottom.
-- Each row receives activation with appropriate skew (delay).
--
-- Chisel equivalent:
--   val rows = VecInit(Seq.tabulate(kernelSize) { r =>
--     val row = Module(new SystolicRow(kernelSize))
--     row.io.act_in := ShiftRegister(act_input(r), r)  // skew
--     row
--   })
--   // Connect partial sums vertically
--   for (r <- 1 until kernelSize) {
--     rows(r).io.psums_in := rows(r-1).io.psums_out
--   }

/-- Delay a signal by `n` clock cycles using a chain of registers. -/
def delayN {dom : DomainConfig} (n : Nat) (init : BitVec 8)
    (sig : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  match n with
  | 0     => sig
  | n + 1 => delayN n init (Signal.register init sig)

/-- Full systolic array: `rows` × `cols` PEs.
    `actInputs` are the activation streams for each row (from line buffer).
    `allWeights` is a 2D list of weight signals (rows × cols).
    Returns the final partial sums from the bottom row (one per column). -/
def systolicArray {dom : DomainConfig}
    (numRows numCols : Nat)
    (actInputs : List (Signal dom (BitVec 8)))    -- one per row
    (allWeights : List (List (Signal dom (BitVec 8))))  -- rows × cols
    (loadW : Signal dom Bool)
    : List (Signal dom (BitVec 32)) :=
  -- Apply skew to activation inputs (row i gets delay of i cycles)
  let skewedActs := actInputs.enum.map fun (i, act) =>
    delayN i (0#8) act
  -- Initial partial sums (top of array) = all zeros
  let zeroPsums : List (Signal dom (BitVec 32)) :=
    List.replicate numCols (Signal.pure (0#32))
  -- Stack rows, threading partial sums downward
  let finalState := (List.zip skewedActs allWeights).foldl
    (fun (psums : List (Signal dom (BitVec 32)))
         (pair : Signal dom (BitVec 8) × List (Signal dom (BitVec 8))) =>
      let (act, rowWeights) := pair
      let (newPsums, _) := systolicRow numCols act psums rowWeights loadW
      newPsums
    ) zeroPsums
  finalState

-- ============================================================
-- Line Buffer (Sliding Window Generator)
-- ============================================================
-- Buffers input pixels to produce multiple rows simultaneously
-- for feeding the systolic array. Uses Signal.memory for SRAM.
--
-- Chisel equivalent:
--   val lineBuffers = Seq.fill(kernelSize - 1)(SyncReadMem(imgWidth, UInt(8.W)))
--   // shift data through line buffers

/-- Line buffer: takes a stream of pixels and produces `kernelSize` rows
    of the sliding window. Uses a shift-register chain approach.
    Returns a list of `kernelSize` signals, each representing one row
    of the convolution window. -/
def lineBuffer {dom : DomainConfig}
    (kernelSize : Nat) (imgWidth : Nat)
    (pixelIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    : List (Signal dom (BitVec 8)) :=
  -- Build chain of line delays (each delays by imgWidth cycles)
  -- Row 0 = most recent, Row (kernelSize-1) = oldest
  let rec buildRows (n : Nat) (current : Signal dom (BitVec 8))
      : List (Signal dom (BitVec 8)) :=
    match n with
    | 0     => []
    | n + 1 =>
      -- Delay by imgWidth cycles using a shift register chain
      let delayed := (List.range imgWidth).foldl
        (fun acc _ => Signal.register (0#8) acc) current
      current :: buildRows n delayed
  buildRows kernelSize pixelIn

-- ============================================================
-- Conv2D Top Module (FSM Controller + Systolic Array)
-- ============================================================
-- Corresponds to SDIP's SDIP_conv2d module.
-- Uses Signal.loop for the FSM controlling data flow.
--
-- State machine:
--   IDLE (0) → LOAD_WEIGHTS (1) → COMPUTE (2) → DONE (3) → IDLE
--
-- Chisel equivalent:
--   class SDIP_conv2d extends Module {
--     val sIdle :: sLoadW :: sCompute :: sDone :: Nil = Enum(4)
--     val state = RegInit(sIdle)
--     switch(state) { ... }
--   }

-- State declaration using Sparkle's declare_signal_state macro
-- (conceptual — actual macro usage depends on Sparkle version)

/-- Conv2D top module: integrates line buffer, systolic array, and FSM controller.

    Architecture:
    ```
    pixel_in → [Line Buffer] → row0, row1, row2
                                  ↓     ↓     ↓     (skewed activation inputs)
                               [PE00] [PE01] [PE02]  ← weight row 0
                                  ↓     ↓     ↓
                               [PE10] [PE11] [PE12]  ← weight row 1
                                  ↓     ↓     ↓
                               [PE20] [PE21] [PE22]  ← weight row 2
                                  ↓     ↓     ↓
                               psum0  psum1  psum2  → accumulate → output
    ```
-/
def conv2dSystolic {dom : DomainConfig}
    (cfg : Conv2dConfig)
    (pixelIn   : Signal dom (BitVec 8))     -- streaming pixel input
    (weightIn  : Signal dom (BitVec 8))     -- weight data input (serial load)
    (start     : Signal dom Bool)            -- start signal
    (validIn   : Signal dom Bool)            -- input valid
    : Signal dom (BitVec 32 × Bool) :=      -- (result, valid_out)

  -- FSM using Signal.loop
  -- State encoding: 0=IDLE, 1=LOAD_WEIGHTS, 2=COMPUTE, 3=DONE
  Signal.loop fun stateBundle =>
    let fsmReg   := (fun s => (s : BitVec 4 × BitVec 32 × Bool).1) <$> stateBundle
    let cycleReg := (fun s => (s : BitVec 4 × BitVec 32 × Bool).2.1) <$> stateBundle
    let doneReg  := (fun s => (s : BitVec 4 × BitVec 32 × Bool).2.2) <$> stateBundle

    -- State transition logic
    let isIdle     := fsmReg == (Signal.pure (0#4))
    let isLoadW    := fsmReg == (Signal.pure (1#4))
    let isCompute  := fsmReg == (Signal.pure (2#4))

    -- Cycle counter
    let totalWeights := cfg.kernelSize * cfg.kernelSize
    let totalPixels  := cfg.imgWidth * cfg.imgHeight
    let counterNext := (· + 1#32) <$> cycleReg

    -- Weight load complete when counter reaches kernelSize²
    let loadDone := (fun c =>
      c.toNat >= totalWeights
    ) <$> cycleReg

    -- Compute complete when all pixels processed
    let computeDone := (fun c =>
      c.toNat >= totalPixels
    ) <$> cycleReg

    -- FSM next state (using hw_cond pattern)
    let fsmNext := Signal.mux (start &&& isIdle) (Signal.pure (1#4))
      (Signal.mux (loadDone &&& isLoadW) (Signal.pure (2#4))
        (Signal.mux (computeDone &&& isCompute) (Signal.pure (3#4))
          (Signal.mux (fsmReg == Signal.pure (3#4)) (Signal.pure (0#4))
            fsmReg)))

    -- Counter: reset on state transition, increment otherwise
    let cycleNext := Signal.mux
      (Signal.mux (start &&& isIdle) (Signal.pure true)
        (Signal.mux (loadDone &&& isLoadW) (Signal.pure true)
          (Signal.pure false)))
      (Signal.pure (0#32))
      counterNext

    -- Instantiate line buffer
    let windowRows := lineBuffer cfg.kernelSize cfg.imgWidth pixelIn validIn

    -- Create weight signals (in a real design, these would be loaded
    -- from weightIn serial stream into weight registers)
    -- For simplicity, use static weight signals here
    let weightSignals : List (List (Signal dom (BitVec 8))) :=
      (List.range cfg.kernelSize).map fun _r =>
        (List.range cfg.kernelSize).map fun _c =>
          weightIn  -- In full impl: indexed weight register file

    -- Instantiate systolic array
    let psums := systolicArray cfg.arrayRows cfg.arrayCols
      windowRows weightSignals isLoadW

    -- Sum all column partial sums for final output
    let finalSum := psums.foldl
      (fun acc p => (· + ·) <$> acc <*> p)
      (Signal.pure (0#32))

    -- Output valid when in COMPUTE state
    let outValid := (fun s => s == 2#4) <$> fsmReg

    -- Return: (next_state_bundle, output)
    let nextState := (fun f c d => (f, c, d)) <$> fsmNext <*> cycleNext <*> outValid
    let output := (fun s v => (s, v)) <$> finalSum <*> outValid

    -- The loop returns the next state; the output is derived
    nextState

-- ============================================================
-- Alternative: Standalone Systolic PE with Formal Verification
-- ============================================================
-- Sparkle's key advantage: prove properties about the PE!

/-- Pure specification of a MAC operation (for verification). -/
def macSpec (activation weight : BitVec 8) (partialSum : BitVec 32) : BitVec 32 :=
  let a32 : BitVec 32 := BitVec.zeroExtend 32 activation
  let w32 : BitVec 32 := BitVec.zeroExtend 32 weight
  partialSum + a32 * w32

/-- Proof: MAC with zero activation produces unchanged partial sum. -/
theorem mac_zero_act (w : BitVec 8) (psum : BitVec 32) :
    macSpec (0#8) w psum = psum := by
  simp [macSpec, BitVec.zeroExtend]
  ring

/-- Proof: MAC is commutative in activation and weight
    (for the multiplication component). -/
theorem mac_mul_comm (a w : BitVec 8) (psum : BitVec 32) :
    macSpec a w psum = psum + BitVec.zeroExtend 32 w * BitVec.zeroExtend 32 a := by
  simp [macSpec, BitVec.zeroExtend, mul_comm]

-- ============================================================
-- Verilog Generation
-- ============================================================
-- Uncomment to generate SystemVerilog:
-- #synthesizeVerilog (systolicPE
--     (Signal.pure 0#8)
--     (Signal.pure 0#32)
--     (Signal.pure 0#8)
--     (Signal.pure false))

-- ============================================================
-- Simulation Example
-- ============================================================

/-- Simple test: verify PE output for known inputs. -/
def testPE : IO Unit := do
  -- Create test signals
  let actSignal : Signal defaultDomain (BitVec 8) := ⟨fun t => (t % 256).toBitVec 8⟩
  let psumZero  : Signal defaultDomain (BitVec 32) := Signal.pure (0#32)
  let weight    : Signal defaultDomain (BitVec 8) := Signal.pure (3#8)
  let loadW     : Signal defaultDomain Bool := ⟨fun t => t == 0⟩

  let peOut := systolicPE actSignal psumZero weight loadW

  -- Sample first 5 cycles
  for t in List.range 5 do
    let (outAct, outPsum) := peOut.atTime t
    IO.println s!"t={t}: act_out={outAct}, psum_out={outPsum}"

-- #eval testPE

/-!
## Chisel → Sparkle Translation Guide

### Key Correspondences

| Chisel (Scala)              | Sparkle (Lean 4)                              |
|-----------------------------|-----------------------------------------------|
| `class PE extends Module`   | `def pe ... : Signal dom α`                   |
| `val reg = RegInit(0.U)`    | `Signal.register (0#N) input`                 |
| `val mem = SyncReadMem(..)`| `Signal.memory wAddr wData wEn rAddr`         |
| `io.out := expr`           | pure functional return value                   |
| `when(cond) { ... }`       | `Signal.mux cond thenSig elseSig`             |
| `switch(state) { ... }`    | `hw_cond` macro or nested `Signal.mux`        |
| `Wire(UInt(8.W))`          | intermediate `let` binding                    |
| `Vec(n, UInt(8.W))`        | `HWVector (BitVec 8) n`                       |
| `ShiftRegister(x, n)`      | `delayN n init sig`                           |
| `for (i <- 0 until n)`     | `List.range n |>.map ...` or `foldl`          |
| `Cat(a, b)`                | `BitVec.append a b`                           |
| `a +& b` (width expand)    | explicit `BitVec.zeroExtend` then add          |
| `Module(new Sub)`          | function application `subModule args`         |
| `val state = RegInit(s0)`  | `Signal.loop fun st => ...`                   |
| `Enum(n)`                  | `BitVec` encoding: `0#4`, `1#4`, etc.         |

### Advantages of Sparkle over Chisel for this design

1. **No latches by construction**: Lean's exhaustive pattern matching prevents
   forgotten `default` cases that create latches in Chisel/Verilog.

2. **No combinational loops**: `Signal` monad enforces DAG structure;
   feedback only through `Signal.register` or `Signal.loop`.

3. **Formal proofs**: We proved `mac_zero_act` and `mac_mul_comm` above —
   impossible natively in Chisel (would require separate Chiseltest + formal tool).

4. **DRC built-in**: Sparkle warns if module outputs aren't registered,
   which is critical for systolic arrays where timing closure is essential.

5. **Readable Verilog**: Unlike Chisel → FIRRTL → Verilog (which produces
   unreadable names), Sparkle generates 1:1 structural SystemVerilog.
-/
