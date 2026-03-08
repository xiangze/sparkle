/-
  SDIP_conv2d.lean — Chisel SDIP_conv2d の Sparkle Signal DSL への忠実な移植

  Original: https://github.com/xiangze/SDIP/blob/main/src/main/scala/sdip/SDIP_conv2d.scala
  Target:   https://github.com/Verilean/sparkle (Lean 4 Signal DSL)

  アーキテクチャ:
    画像行バッファ → スキューバッファ → シストリックアレー → デスキューバッファ → 出力
                                           ↑
                                      カーネル重みロード
-/

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain

open Sparkle.Core.Signal
open Sparkle.Core.Domain

-- ============================================================
-- パラメータ定義
-- ============================================================
-- Chisel: object DATA { val W = 8 }
-- Chisel: object CONV { val KERNEL_SIZE = 3; val IMG_WIDTH = 8; val ACC_W = DATA.W * 2 + 4 }

namespace SDIP

def DATA_W : Nat := 8
def KERNEL_SIZE : Nat := 3
def IMG_WIDTH : Nat := 8
def ACC_W : Nat := DATA_W * 2 + 4  -- = 20 (オーバーフロー防止)

-- ============================================================
-- Processing Element (PE) - 積和演算ユニット
-- ============================================================
--
--  Weight Stationary アーキテクチャ:
--    - 重み(weight)は事前にロードし、PE内に保持
--    - 入力データ(data_in)は水平方向(左→右)に伝搬
--    - 部分和(psum)は垂直方向(上→下)に伝搬
--
--       psum_in (from above)
--          │
--    data_in ──→ [PE] ──→ data_out
--          │
--       psum_out (to below)
--
-- Chisel 原文:
--   class PE extends Module {
--     val weight_reg = RegInit(0.S(DATA.W.W))
--     val data_reg   = RegInit(0.S(DATA.W.W))
--     val psum_reg   = RegInit(0.S(CONV.ACC_W.W))
--     when(io.weight_load) { weight_reg := io.weight_in }
--     data_reg := io.data_in
--     psum_reg := io.psum_in + (io.data_in * weight_reg)
--     io.data_out := data_reg
--     io.psum_out := psum_reg
--   }
--
-- Sparkle 移植:
--   Signal.loop で weight_reg のフィードバックを表現。
--   data_reg, psum_reg は Signal.register でパイプラインレジスタ。
--   Chisel の SInt は Sparkle では BitVec + 符号拡張で対応。

/-- PE の出力型: (data_out, psum_out) -/
structure PEOutput where
  dataOut : BitVec DATA_W
  psumOut : BitVec ACC_W
deriving Inhabited

/-- Processing Element: 重みステーショナリ方式の積和演算ユニット。
    重みを内部レジスタに保持し、data は左→右へ、psum は上→下へ伝搬する。

    Chisel との対応:
      RegInit(0.S)        → Signal.register (0#N)
      when(load) { := }   → Signal.mux load newVal oldVal
      io.data_in * weight → signedMul <$> dataIn <*> weightReg
-/
def pe {dom : DomainConfig}
    (weightLoad : Signal dom Bool)
    (weightIn   : Signal dom (BitVec DATA_W))
    (dataIn     : Signal dom (BitVec DATA_W))
    (psumIn     : Signal dom (BitVec ACC_W))
    : Signal dom PEOutput :=

  -- weight_reg: フィードバックループ。weight_load 時のみ更新。
  -- Chisel: val weight_reg = RegInit(0.S(DATA.W.W))
  --         when(io.weight_load) { weight_reg := io.weight_in }
  let weightReg := Signal.loop fun wPrev =>
    let wNext := Signal.mux weightLoad weightIn wPrev
    Signal.register (0 : BitVec DATA_W) wNext

  -- psum_reg := psum_in + (data_in * weight_reg)
  -- 符号付き乗算: DATA_W ビット × DATA_W ビット → ACC_W ビットに符号拡張して加算
  let product : Signal dom (BitVec ACC_W) :=
    (fun d w =>
      let dExt : BitVec ACC_W := BitVec.signExtend ACC_W d
      let wExt : BitVec ACC_W := BitVec.signExtend ACC_W w
      dExt * wExt
    ) <$> dataIn <*> weightReg

  let psumNext : Signal dom (BitVec ACC_W) :=
    (· + ·) <$> psumIn <*> product

  -- data_reg := io.data_in  (1サイクル遅延で水平伝搬)
  let dataReg := Signal.register (0 : BitVec DATA_W) dataIn

  -- psum_reg := psum_in + (data_in * weight_reg)  (1サイクル遅延で垂直伝搬)
  let psumReg := Signal.register (0 : BitVec ACC_W) psumNext

  -- 出力: io.data_out := data_reg, io.psum_out := psum_reg
  (fun d p => { dataOut := d, psumOut := p : PEOutput }) <$> dataReg <*> psumReg


-- ============================================================
-- シストリックアレー (K × K の PE グリッド)
-- ============================================================
--
--  構造 (3×3 カーネルの例):
--
--  入力データ(スキュー済み)
--   row0 ──→ [PE(0,0)] ──→ [PE(0,1)] ──→ [PE(0,2)]
--   row1 ──→ [PE(1,0)] ──→ [PE(1,1)] ──→ [PE(1,2)]
--   row2 ──→ [PE(2,0)] ──→ [PE(2,1)] ──→ [PE(2,2)]
--                │              │              │
--              psum           psum           psum
--                ↓              ↓              ↓
--            出力列0         出力列1         出力列2
--
-- Chisel 原文:
--   val pe = Seq.fill(K, K)(Module(new PE))
--   for (r <- 0 until K) {
--     for (c <- 0 until K) {
--       pe(r)(c).io.weight_load := io.weight_load
--       pe(r)(c).io.weight_in   := io.weights(r * K + c)
--       if (c == 0) pe(r)(c).io.data_in := io.data_in(r)
--       else        pe(r)(c).io.data_in := pe(r)(c-1).io.data_out
--       if (r == 0) pe(r)(c).io.psum_in := 0.S
--       else        pe(r)(c).io.psum_in := pe(r-1)(c).io.psum_out
--     }
--   }

/-- 1行分の PE チェーン: activation を左→右へ伝搬。
    `psumIns` は上の行からの部分和 (列数分)。
    戻り値: (各列の psum_out リスト) -/
def systolicRowChain {dom : DomainConfig} (K : Nat)
    (weightLoad : Signal dom Bool)
    (rowWeights : List (Signal dom (BitVec DATA_W)))  -- この行の重み K 個
    (dataIn     : Signal dom (BitVec DATA_W))          -- この行の左端入力
    (psumIns    : List (Signal dom (BitVec ACC_W)))    -- 上からの部分和 K 個
    : List (Signal dom (BitVec ACC_W)) :=
  -- foldl で列を左→右に接続
  let init : Signal dom (BitVec DATA_W) × List (Signal dom (BitVec ACC_W)) :=
    (dataIn, [])
  let result := (List.zip (List.zip rowWeights psumIns) (List.range K)).foldl
    (fun (acc : Signal dom (BitVec DATA_W) × List (Signal dom (BitVec ACC_W)))
         (item : (Signal dom (BitVec DATA_W) × Signal dom (BitVec ACC_W)) × Nat) =>
      let (curData, accPsums) := acc
      let ((w, psIn), _) := item
      let peResult := pe weightLoad w curData psIn
      let nextData := (fun o => o.dataOut) <$> peResult
      let nextPsum := (fun o => o.psumOut) <$> peResult
      (nextData, accPsums ++ [nextPsum])
    ) init
  result.2

/-- K × K シストリックアレー全体。
    `dataIns`  : 各行への入力データ (スキュー済み前提, K 個)
    `weights`  : フラット配列 K*K 個の重み
    戻り値    : 最下段 K 列の部分和出力 -/
def systolicArray {dom : DomainConfig} (K : Nat)
    (weightLoad : Signal dom Bool)
    (weights    : List (Signal dom (BitVec DATA_W)))    -- K*K 個フラット
    (dataIns    : List (Signal dom (BitVec DATA_W)))    -- K 個 (各行入力)
    : List (Signal dom (BitVec ACC_W)) :=
  -- 初期部分和 = 全列ゼロ (Chisel: if (r == 0) psum_in := 0.S)
  let zeroPsums : List (Signal dom (BitVec ACC_W)) :=
    List.replicate K (Signal.pure (0 : BitVec ACC_W))
  -- 行を上→下に接続
  (List.range K).foldl
    (fun (prevPsums : List (Signal dom (BitVec ACC_W))) (r : Nat) =>
      -- この行の重み: weights[r*K .. r*K+K-1]
      let rowW := (List.range K).map fun c => weights.getD (r * K + c) (Signal.pure (0 : BitVec DATA_W))
      -- この行の入力データ
      let rowData := dataIns.getD r (Signal.pure (0 : BitVec DATA_W))
      systolicRowChain K weightLoad rowW rowData prevPsums
    ) zeroPsums


-- ============================================================
-- 入力スキューバッファ
-- ============================================================
--
--  row 0: data[n]     (遅延なし)
--  row 1: data[n-1]   (1サイクル遅延)
--  row 2: data[n-2]   (2サイクル遅延)
--
-- Chisel 原文:
--   for (r <- 0 until K) {
--     var signal = io.in(r)
--     for (d <- 0 until r) { signal = RegNext(signal, 0.S) }
--     io.out(r) := signal
--   }

/-- 信号を n サイクル遅延させる (ShiftRegister 相当)。
    Chisel の `RegNext` チェーンに対応。 -/
def delayN {dom : DomainConfig} {w : Nat}
    (n : Nat) (sig : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  match n with
  | 0     => sig
  | n + 1 => delayN n (Signal.register (0 : BitVec w) sig)

/-- 入力スキューバッファ: 行 r に r サイクルの遅延を付加。 -/
def inputSkewBuffer {dom : DomainConfig} (K : Nat)
    (inputs : List (Signal dom (BitVec DATA_W)))
    : List (Signal dom (BitVec DATA_W)) :=
  inputs.enum.map fun (r, sig) => delayN r sig


-- ============================================================
-- 出力デスキューバッファ
-- ============================================================
--
--  col 0: 遅延 (K-1) サイクル追加
--  col 1: 遅延 (K-2) サイクル追加
--  ...
--  col K-1: 遅延なし
--
-- Chisel 原文:
--   for (c <- 0 until K) {
--     val delay = K - 1 - c
--     var signal = io.in(c)
--     for (d <- 0 until delay) { signal = RegNext(signal, 0.S) }
--     io.out(c) := signal
--   }

/-- 出力デスキューバッファ: 列 c に (K-1-c) サイクルの遅延を付加。 -/
def outputDeskewBuffer {dom : DomainConfig} (K : Nat)
    (inputs : List (Signal dom (BitVec ACC_W)))
    : List (Signal dom (BitVec ACC_W)) :=
  inputs.enum.map fun (c, sig) =>
    let delay := K - 1 - c
    delayN delay sig


-- ============================================================
-- ラインバッファ
-- ============================================================
--
--  Chisel 原文: Queue ベースのラインバッファチェーン
--    val line_buffers = Seq.fill(K-1)(Module(new Queue(DataType(DATA.W), CONV.IMG_WIDTH)))
--    line_data(0) := io.in
--    for (i <- 0 until K-1) { ... chain ... }
--    line_data(i+1) := line_buffers(i).io.deq.bits
--
--  Sparkle 移植:
--    Chisel Queue (FIFO) は、一定幅のラインバッファとして機能。
--    IMG_WIDTH サイクル分の遅延と等価なので、
--    Signal.register の IMG_WIDTH 段チェーンで近似する。
--    (完全な FIFO が必要な場合は Sparkle の SyncFIFO IP を使用)

/-- IMG_WIDTH サイクル分の遅延を作るラインバッファ (1行分)。
    Chisel `Queue(DataType(DATA.W), IMG_WIDTH)` に対応。 -/
def lineDelay {dom : DomainConfig}
    (width : Nat) (sig : Signal dom (BitVec DATA_W)) : Signal dom (BitVec DATA_W) :=
  delayN width sig

/-- K 行分のラインバッファ。1ピクセル/サイクルのストリーム入力から
    K 行分の並列出力を生成する。
    line(0) = 現在の行、line(1) = 1行前、...、line(K-1) = (K-1)行前 -/
def lineBuffers {dom : DomainConfig} (K : Nat) (imgWidth : Nat)
    (pixelIn : Signal dom (BitVec DATA_W))
    : List (Signal dom (BitVec DATA_W)) :=
  -- line_data(0) := io.in
  -- line_data(i+1) := lineDelay(IMG_WIDTH, line_data(i))
  let rec build (n : Nat) (current : Signal dom (BitVec DATA_W))
      : List (Signal dom (BitVec DATA_W)) :=
    match n with
    | 0     => []
    | n + 1 =>
      let delayed := lineDelay imgWidth current
      current :: build n delayed
  build K pixelIn


-- ============================================================
-- Valid パイプラインシフトレジスタ
-- ============================================================
--
-- Chisel 原文:
--   val pipeline_depth = (K-1) + K + (K-1)   // = 3K - 2
--   val valid_sr = RegInit(0.U(pipeline_depth.W))
--   valid_sr := Cat(valid_sr(pipeline_depth-2, 0), io.valid_in)
--   io.valid_out := valid_sr(pipeline_depth-1)
--
-- Sparkle 移植:
--   Bool 信号を pipeline_depth 段の register チェーンに通す。

/-- Valid 信号のパイプライン遅延。n 段のシフトレジスタ。 -/
def validPipeline {dom : DomainConfig}
    (depth : Nat) (validIn : Signal dom Bool) : Signal dom Bool :=
  match depth with
  | 0     => validIn
  | n + 1 => validPipeline n (Signal.register false validIn)


-- ============================================================
-- トップモジュール: SDIP_conv2d
-- ============================================================
--
--  全体のデータフロー:
--
--   画像行バッファ → スキューバッファ → シストリックアレー → デスキューバッファ → 出力
--                                         ↑
--                                    カーネル重みロード
--
-- Chisel 原文:
--   class SDIP_conv2d extends Module { ... }

structure Conv2dOutput where
  result   : BitVec ACC_W    -- 畳み込み結果
  validOut : Bool             -- 出力有効
  ready    : Bool             -- 演算可能
deriving Inhabited

/-- SDIP_conv2d トップモジュール。

    入力:
      pixelIn    : 1ピクセル/サイクルのラスタスキャン入力 (SInt DATA_W)
      kernel     : K*K 個のカーネル重み (フラット配列)
      weightLoad : 重みロード指示
      validIn    : 入力データ有効

    出力:
      Conv2dOutput { result, validOut, ready }

    データフロー:
      pixelIn → [lineBuffers] → K行並列
                                  ↓
                            [inputSkewBuffer] → 行ごとにスキュー
                                  ↓
                            [systolicArray K×K] ← kernel (weightLoad時)
                                  ↓
                            [outputDeskewBuffer] → 列ごとにデスキュー
                                  ↓
                              reduce (+) → accumulated result
-/
def sdipConv2d {dom : DomainConfig}
    (pixelIn    : Signal dom (BitVec DATA_W))
    (kernel     : List (Signal dom (BitVec DATA_W)))  -- K*K 個
    (weightLoad : Signal dom Bool)
    (validIn    : Signal dom Bool)
    : Signal dom Conv2dOutput :=

  let K := KERNEL_SIZE

  -- -------------------------------------------------------
  -- 1. ラインバッファ: 1ピクセルストリームから K 行分を同時出力
  -- -------------------------------------------------------
  -- Chisel: val line_buffers = Seq.fill(K-1)(Module(new Queue(...)))
  --         line_data(0) := io.in
  --         line_data(i+1) := line_buffers(i).io.deq.bits
  let lineData := lineBuffers K IMG_WIDTH pixelIn

  -- -------------------------------------------------------
  -- 2. スキューバッファ
  -- -------------------------------------------------------
  -- Chisel: val skew = Module(new InputSkewBuffer(K))
  --         skew.io.in := line_data
  let skewed := inputSkewBuffer K lineData

  -- -------------------------------------------------------
  -- 3. シストリックアレー
  -- -------------------------------------------------------
  -- Chisel: val array = Module(new SystolicArray(K))
  --         array.io.weight_load := io.weight_load
  --         array.io.weights     := io.kernel
  --         array.io.data_in     := skew.io.out
  let psumOuts := systolicArray K weightLoad kernel skewed

  -- -------------------------------------------------------
  -- 4. デスキューバッファ
  -- -------------------------------------------------------
  -- Chisel: val deskew = Module(new OutputDeskewBuffer(K))
  --         deskew.io.in := array.io.psum_out
  let deskewed := outputDeskewBuffer K psumOuts

  -- -------------------------------------------------------
  -- 5. 出力アキュムレータ: K 列の部分和を合算
  -- -------------------------------------------------------
  -- Chisel: val accumulated = deskew.io.out.reduce(_ + _)
  --         io.out := accumulated
  let accumulated : Signal dom (BitVec ACC_W) :=
    deskewed.foldl
      (fun acc s => (· + ·) <$> acc <*> s)
      (Signal.pure (0 : BitVec ACC_W))

  -- -------------------------------------------------------
  -- 6. Valid パイプライン
  -- -------------------------------------------------------
  -- Chisel: val pipeline_depth = (K-1) + K + (K-1)  // = 3K - 2 = 7
  --         valid_sr := Cat(valid_sr(...), io.valid_in)
  --         io.valid_out := valid_sr(pipeline_depth - 1)
  let pipelineDepth := (K - 1) + K + (K - 1)  -- = 7 for K=3
  let validOut := validPipeline pipelineDepth validIn

  -- -------------------------------------------------------
  -- 7. Ready 信号: weight_loaded レジスタ
  -- -------------------------------------------------------
  -- Chisel: val weight_loaded = RegInit(false.B)
  --         when(io.weight_load) { weight_loaded := true.B }
  --         io.ready := weight_loaded
  let weightLoaded : Signal dom Bool := Signal.loop fun prev =>
    let next := Signal.mux weightLoad (Signal.pure true) prev
    Signal.register false next

  -- -------------------------------------------------------
  -- 出力の組み立て
  -- -------------------------------------------------------
  (fun r v rdy => { result := r, validOut := v, ready := rdy : Conv2dOutput })
    <$> accumulated <*> validOut <*> weightLoaded


-- ============================================================
-- Verilog 生成
-- ============================================================
-- #synthesizeVerilog (sdipConv2d
--     (Signal.pure (0 : BitVec DATA_W))
--     (List.replicate (KERNEL_SIZE * KERNEL_SIZE) (Signal.pure (0 : BitVec DATA_W)))
--     (Signal.pure false)
--     (Signal.pure false))


-- ============================================================
-- シミュレーション / テスト
-- ============================================================

/-- PE の純粋仕様 (テスト・検証用) -/
def macPure (dataIn : BitVec DATA_W) (weight : BitVec DATA_W)
    (psumIn : BitVec ACC_W) : BitVec ACC_W :=
  let dExt : BitVec ACC_W := BitVec.signExtend ACC_W dataIn
  let wExt : BitVec ACC_W := BitVec.signExtend ACC_W weight
  psumIn + dExt * wExt

/-- 検証: ゼロ入力で部分和が変化しないことの証明 -/
theorem mac_zero_data (w : BitVec DATA_W) (psum : BitVec ACC_W) :
    macPure (0 : BitVec DATA_W) w psum = psum := by
  simp [macPure, BitVec.signExtend]
  ring

/-- 検証: ゼロ重みで部分和が変化しないことの証明 -/
theorem mac_zero_weight (d : BitVec DATA_W) (psum : BitVec ACC_W) :
    macPure d (0 : BitVec DATA_W) psum = psum := by
  simp [macPure, BitVec.signExtend]
  ring


-- ============================================================
-- Chisel → Sparkle 対応表
-- ============================================================
/-!
## 変換対応表

| Chisel (SDIP_conv2d.scala)              | Sparkle (SDIP_conv2d.lean)                    |
|-----------------------------------------|-----------------------------------------------|
| `class PE extends Module`               | `def pe ... : Signal dom PEOutput`            |
| `val weight_reg = RegInit(0.S(8.W))`    | `Signal.loop fun wPrev => Signal.register ..` |
| `val data_reg = RegInit(0.S(8.W))`      | `Signal.register (0 : BitVec 8) dataIn`       |
| `val psum_reg = RegInit(0.S(20.W))`     | `Signal.register (0 : BitVec 20) psumNext`    |
| `when(load) { weight_reg := in }`       | `Signal.mux weightLoad weightIn wPrev`        |
| `io.data_in * weight_reg`               | `(fun d w => dExt * wExt) <$> .. <*> ..`      |
| `Seq.fill(K,K)(Module(new PE))`         | `systolicRowChain` + `systolicArray` (foldl)  |
| `if (c==0) data_in := io.data_in(r)`    | foldl の初期値 `dataIn`                       |
| `if (r==0) psum_in := 0.S`             | foldl の初期値 `zeroPsums`                    |
| `RegNext(signal, 0.S)` (チェーン)       | `delayN n sig`                                |
| `InputSkewBuffer`                       | `inputSkewBuffer` (enum + delayN)             |
| `OutputDeskewBuffer`                    | `outputDeskewBuffer` (enum + delayN)          |
| `Queue(DataType, IMG_WIDTH)`            | `lineDelay imgWidth sig` (register チェーン)  |
| `Seq.fill(K-1)(Module(new Queue(...)))` | `lineBuffers K IMG_WIDTH pixelIn`             |
| `deskew.io.out.reduce(_ + _)`           | `deskewed.foldl (fun acc s => (+) <$> ..) ..` |
| `Cat(valid_sr(..), valid_in)`           | `validPipeline pipelineDepth validIn`         |
| `val weight_loaded = RegInit(false.B)`  | `Signal.loop fun prev => Signal.register ..`  |
| `(new ChiselStage).emitVerilog(..)`     | `#synthesizeVerilog sdipConv2d`               |

## Sparkle の利点

1. **ラッチ不在の保証**: Lean の網羅的パターンマッチにより default 漏れが起きない
2. **組合せループ不在**: Signal モナドが DAG を強制、フィードバックは register/loop のみ
3. **形式検証**: `mac_zero_data`, `mac_zero_weight` を Lean カーネルが機械検証
4. **DRC 内蔵**: 出力レジスタチェックで STA 違反を自動検出
5. **可読 Verilog**: FIRRTL を経由しない 1:1 構造対応の SystemVerilog 生成
-/

end SDIP
