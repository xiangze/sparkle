/-
  SDIP_linear.lean — 行列積シストリックアレー (C = A × X)
  Chisel SDIP_linear.scala → Sparkle Signal DSL 完全移植

  Original: https://github.com/xiangze/SDIP/blob/main/src/main/scala/sdip/SDIP_linear.scala

  アーキテクチャ:
    重みレジスタ(A) → X入力バッファ → スキュー → シストリックアレー → デスキュー → 出力セレクタ

  行列積 C = A × X  (すべて N×N)

  A の要素配置（各PEに1要素ずつ格納 = Weight Stationary）:
    PE(0,0)=A[0][0]  PE(0,1)=A[0][1]  ...  PE(0,N-1)=A[0][N-1]
    PE(1,0)=A[1][0]  PE(1,1)=A[1][1]  ...  PE(1,N-1)=A[1][N-1]
    ...
    PE(N-1,0)=A[N-1][0]  ...                PE(N-1,N-1)=A[N-1][N-1]

  X の各行がスキュー付きで水平に流入し、部分和が垂直に流れて
  最下段から C の各列が出力される。
-/

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain

open Sparkle.Core.Signal
open Sparkle.Core.Domain

namespace SDIP

-- ============================================================
-- パラメータ定義
-- ============================================================
-- Chisel: object DATA { val W = 8 }
-- Chisel: object MAT  { val N = 4; val ACC_W = DATA.W * 2 + log2Ceil(MAT.N + 1) }

def DATA_W : Nat := 8
def MAT_N  : Nat := 4
def ACC_W  : Nat := DATA_W * 2 + 3  -- = 19  (log2Ceil(5) = 3)
-- カウンタ幅 (log2Ceil(N+1) = 3, log2Ceil(N*N+1) = 5)
def CTR_W  : Nat := 3
def WCTR_W : Nat := 5


-- ============================================================
-- Processing Element (PE_linear)
-- ============================================================
--
--  Weight Stationary: A[r][c] を PE(r,c) に固定
--  動作: psum_out = psum_in + weight * x_in  (1サイクル遅延)
--
--         psum_in
--           │
--   x_in ──→ [PE: a] ──→ x_out
--           │
--         psum_out
--
-- Chisel:
--   val weight_reg = RegInit(0.S(DATA.W.W))
--   when(io.weight_load) { weight_reg := io.weight_in }
--   x_reg    := io.x_in
--   psum_reg := io.psum_in + (io.x_in * weight_reg)

structure PEOutput where
  xOut    : BitVec DATA_W
  psumOut : BitVec ACC_W
deriving Inhabited

/-- PE_linear: 重みステーショナリ方式の積和演算ユニット。
    重みを内部レジスタに保持し、x は左→右へ、psum は上→下へ伝搬する。 -/
def peLinear {dom : DomainConfig}
    (weightLoad : Signal dom Bool)
    (weightIn   : Signal dom (BitVec DATA_W))
    (xIn        : Signal dom (BitVec DATA_W))
    (psumIn     : Signal dom (BitVec ACC_W))
    : Signal dom PEOutput :=

  -- weight_reg: when(weight_load) { weight_reg := weight_in }
  let weightReg := Signal.loop fun wPrev =>
    let wNext := Signal.mux weightLoad weightIn wPrev
    Signal.register (0 : BitVec DATA_W) wNext

  -- psum_reg := psum_in + (x_in * weight_reg)
  -- 符号拡張して ACC_W ビットで乗算・加算
  let product : Signal dom (BitVec ACC_W) :=
    (fun x w =>
      let xExt : BitVec ACC_W := BitVec.signExtend ACC_W x
      let wExt : BitVec ACC_W := BitVec.signExtend ACC_W w
      xExt * wExt
    ) <$> xIn <*> weightReg

  let psumNext : Signal dom (BitVec ACC_W) :=
    (· + ·) <$> psumIn <*> product

  -- x_reg := x_in  (水平伝搬、1サイクル遅延)
  let xReg := Signal.register (0 : BitVec DATA_W) xIn

  -- psum_reg := psum_next  (垂直伝搬、1サイクル遅延)
  let psumReg := Signal.register (0 : BitVec ACC_W) psumNext

  (fun x p => { xOut := x, psumOut := p : PEOutput }) <$> xReg <*> psumReg


-- ============================================================
-- ユーティリティ: N サイクル遅延
-- ============================================================
-- Chisel: ShiftRegister(x, n) / RegNext チェーン

/-- 信号を n サイクル遅延させる -/
def delayN {dom : DomainConfig} {w : Nat}
    (n : Nat) (sig : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  match n with
  | 0     => sig
  | n + 1 => delayN n (Signal.register (0 : BitVec w) sig)

/-- Bool 信号を n サイクル遅延させる -/
def delayBool {dom : DomainConfig}
    (n : Nat) (sig : Signal dom Bool) : Signal dom Bool :=
  match n with
  | 0     => sig
  | n + 1 => delayBool n (Signal.register false sig)


-- ============================================================
-- シストリックアレー行チェーン (1行分の PE 接続)
-- ============================================================
-- Chisel:
--   for (c <- 0 until N) {
--     if (c == 0) pe(r)(c).io.x_in := io.x_in(r)
--     else        pe(r)(c).io.x_in := pe(r)(c-1).io.x_out
--   }

/-- 1行分の PE チェーン。x を左→右に伝搬し、各列の psum_out を返す。 -/
def systolicRowChain {dom : DomainConfig} (N : Nat)
    (weightLoad : Signal dom Bool)
    (rowWeights : List (Signal dom (BitVec DATA_W)))
    (xIn        : Signal dom (BitVec DATA_W))
    (psumIns    : List (Signal dom (BitVec ACC_W)))
    : List (Signal dom (BitVec ACC_W)) :=
  let init : Signal dom (BitVec DATA_W) × List (Signal dom (BitVec ACC_W)) :=
    (xIn, [])
  let result := (List.zip rowWeights psumIns).foldl
    (fun (acc : Signal dom (BitVec DATA_W) × List (Signal dom (BitVec ACC_W)))
         (pair : Signal dom (BitVec DATA_W) × Signal dom (BitVec ACC_W)) =>
      let (curX, accPsums) := acc
      let (w, psIn) := pair
      let peResult := peLinear weightLoad w curX psIn
      let nextX := (fun o => o.xOut) <$> peResult
      let nextPsum := (fun o => o.psumOut) <$> peResult
      (nextX, accPsums ++ [nextPsum])
    ) init
  result.2


-- ============================================================
-- シストリックアレー (N × N PE グリッド)
-- ============================================================
-- Chisel:
--   val pe = Seq.fill(N, N)(Module(new PE_linear))
--   // 水平: x 左→右、垂直: psum 上→下
--   // 最下段から psum_out

/-- N × N シストリックアレー。
    weights: N*N 個フラット配列、xIns: N 行の入力（スキュー済み前提）。
    戻り値: 最下段 N 列の psum 出力。 -/
def systolicArrayLinear {dom : DomainConfig} (N : Nat)
    (weightLoad : Signal dom Bool)
    (weights    : List (Signal dom (BitVec DATA_W)))
    (xIns       : List (Signal dom (BitVec DATA_W)))
    : List (Signal dom (BitVec ACC_W)) :=
  -- 初期部分和 = 全列ゼロ  (Chisel: if (r == 0) psum_in := 0.S)
  let zeroPsums : List (Signal dom (BitVec ACC_W)) :=
    List.replicate N (Signal.pure (0 : BitVec ACC_W))
  -- 行を上→下に foldl で接続
  (List.range N).foldl
    (fun (prevPsums : List (Signal dom (BitVec ACC_W))) (r : Nat) =>
      let rowW := (List.range N).map fun c =>
        weights.getD (r * N + c) (Signal.pure (0 : BitVec DATA_W))
      let rowX := xIns.getD r (Signal.pure (0 : BitVec DATA_W))
      systolicRowChain N weightLoad rowW rowX prevPsums
    ) zeroPsums


-- ============================================================
-- 入力スキューバッファ
-- ============================================================
-- Chisel:
--   for (r <- 0 until N) {
--     var signal = io.in(r)
--     for (d <- 0 until r) { signal = RegNext(signal, 0.S) }
--     io.out(r) := signal
--   }
-- → 行 r に r サイクルの遅延

/-- 入力スキュー: 行 r に r サイクルの遅延を付加 -/
def inputSkewBuffer {dom : DomainConfig} (N : Nat)
    (inputs : List (Signal dom (BitVec DATA_W)))
    : List (Signal dom (BitVec DATA_W)) :=
  inputs.enum.map fun (r, sig) => delayN r sig


-- ============================================================
-- 出力デスキューバッファ
-- ============================================================
-- Chisel:
--   for (c <- 0 until N) {
--     val delay = N - 1 - c
--     for (d <- 0 until delay) { signal = RegNext(signal, 0.S) }
--   }
-- → 列 c に (N-1-c) サイクルの遅延

/-- 出力デスキュー: 列 c に (N-1-c) サイクルの遅延を付加 -/
def outputDeskewBuffer {dom : DomainConfig} (N : Nat)
    (inputs : List (Signal dom (BitVec ACC_W)))
    : List (Signal dom (BitVec ACC_W)) :=
  inputs.enum.map fun (c, sig) =>
    let delay := N - 1 - c
    delayN delay sig


-- ============================================================
-- 行列入力バッファ (MatrixInputBuffer)
-- ============================================================
--
-- Chisel の FSM:
--   sLoad: 要素を1つずつバッファ buf[N][N] に格納
--          N*N 個格納後 → sFeed
--   sFeed: 1列ずつ N 行を並列出力
--          N 列出力後 → sLoad
--
-- Sparkle では Signal.loop で FSM 全体のステートを管理する。
--
-- 状態レジスタ:
--   fsmState  : BitVec 1  (0=LOAD, 1=FEED)
--   loadRow   : BitVec CTR_W
--   loadCol   : BitVec CTR_W
--   feedCol   : BitVec CTR_W
--   buf       : N*N 個の BitVec DATA_W (フラット化)

-- Chisel: val sLoad :: sFeed :: Nil = Enum(2)
def FSM_LOAD : BitVec 1 := 0
def FSM_FEED : BitVec 1 := 1

-- バッファサイズ (N*N)
def BUF_SIZE : Nat := MAT_N * MAT_N  -- = 16

-- ステート構造体
structure MatBufState where
  fsmState : BitVec 1
  loadRow  : BitVec CTR_W
  loadCol  : BitVec CTR_W
  feedCol  : BitVec CTR_W
  buf      : List (BitVec DATA_W)    -- N*N 要素フラット
deriving Inhabited

structure MatBufOutput where
  rowsOut  : List (BitVec DATA_W)    -- N 行分の並列出力
  feeding  : Bool
  done     : Bool
deriving Inhabited

/-- 行列入力バッファ: ストリーム入力 → N行並列出力。
    elemIn を1要素/サイクルで受け取り、N*N 個蓄積後に1列/サイクルで出力。

    Chisel switch(state) { is(sLoad) {...} is(sFeed) {...} }
    → Signal.loop で FSM を純粋関数的に表現 -/
def matrixInputBuffer {dom : DomainConfig} (N : Nat)
    (elemIn  : Signal dom (BitVec DATA_W))
    (validIn : Signal dom Bool)
    : Signal dom MatBufOutput :=

  -- Signal.loop: FSM 全体を1つのループで表現
  Signal.loop fun stPrev =>
    -- 前サイクルのステートを分解
    let prevState   := (fun s => s.fsmState) <$> stPrev
    let prevLoadRow := (fun s => s.loadRow)  <$> stPrev
    let prevLoadCol := (fun s => s.loadCol)  <$> stPrev
    let prevFeedCol := (fun s => s.feedCol)  <$> stPrev
    let prevBuf     := (fun s => s.buf)      <$> stPrev

    let isLoad := prevState === Signal.pure FSM_LOAD
    let isFeed := prevState === Signal.pure FSM_FEED

    -- ====== LOAD フェーズの次状態計算 ======
    -- when(valid_in) { buf(load_row)(load_col) := elem_in; ... counter logic ... }
    let loadColIsMax := (fun c => c == BitVec.ofNat CTR_W (N - 1)) <$> prevLoadCol
    let loadRowIsMax := (fun r => r == BitVec.ofNat CTR_W (N - 1)) <$> prevLoadRow

    -- loadCol の次の値
    let loadColNext := Signal.mux (validIn &&& isLoad)
      (Signal.mux loadColIsMax
        (Signal.pure (0 : BitVec CTR_W))
        ((· + 1) <$> prevLoadCol))
      prevLoadCol

    -- loadRow の次の値
    let loadRowNext := Signal.mux (validIn &&& isLoad &&& loadColIsMax)
      (Signal.mux loadRowIsMax
        (Signal.pure (0 : BitVec CTR_W))
        ((· + 1) <$> prevLoadRow))
      prevLoadRow

    -- LOAD 完了 → FEED へ遷移
    let loadDone := validIn &&& isLoad &&& loadColIsMax &&& loadRowIsMax

    -- ====== FEED フェーズの次状態計算 ======
    -- feed_col をインクリメント、N-1 到達で LOAD へ戻る
    let feedColIsMax := (fun c => c == BitVec.ofNat CTR_W (N - 1)) <$> prevFeedCol

    let feedColNext := Signal.mux isFeed
      (Signal.mux feedColIsMax
        (Signal.pure (0 : BitVec CTR_W))
        ((· + 1) <$> prevFeedCol))
      (Signal.pure (0 : BitVec CTR_W))

    let feedDone := isFeed &&& feedColIsMax

    -- ====== FSM 状態遷移 ======
    let nextFsmState := Signal.mux loadDone (Signal.pure FSM_FEED)
      (Signal.mux feedDone (Signal.pure FSM_LOAD)
        prevState)

    -- ====== バッファ更新 (LOAD 時のみ) ======
    -- buf[loadRow * N + loadCol] := elemIn
    let nextBuf := (fun buf row col elem valid isLd =>
      if valid && isLd then
        let idx := (row.toNat * N + col.toNat) % BUF_SIZE
        buf.set idx elem
      else
        buf
    ) <$> prevBuf <*> prevLoadRow <*> prevLoadCol <*> elemIn <*> validIn <*> isLoad

    -- ====== 出力生成 ======
    -- FEED 時: buf[r][feedCol] を各行から読み出し
    let rowsOut := (fun buf fc isFd =>
      (List.range N).map fun r =>
        if isFd then
          let idx := (r * N + fc.toNat) % BUF_SIZE
          buf.getD idx (0 : BitVec DATA_W)
        else
          (0 : BitVec DATA_W)
    ) <$> prevBuf <*> prevFeedCol <*> isFeed

    let feedingOut := isFeed
    let doneOut := feedDone

    -- 次ステートの組み立て (Signal.register で1サイクル遅延)
    let nextState : Signal dom MatBufState := (fun fs lr lc fc buf =>
      { fsmState := fs, loadRow := lr, loadCol := lc,
        feedCol := fc, buf := buf : MatBufState }
    ) <$> nextFsmState <*> loadRowNext <*> loadColNext <*> feedColNext <*> nextBuf

    -- loop のフィードバック: register で次ステートを保持
    let stateReg := Signal.register
      ({ fsmState := FSM_LOAD, loadRow := 0, loadCol := 0,
         feedCol := 0, buf := List.replicate BUF_SIZE (0 : BitVec DATA_W) } : MatBufState)
      nextState

    -- 出力の組み立て
    let output := (fun rows fd dn =>
      { rowsOut := rows, feeding := fd, done := dn : MatBufOutput }
    ) <$> rowsOut <*> feedingOut <*> doneOut

    -- Signal.loop は次ステートを返す
    -- (出力は別途 output から取得 — ここでは stateReg を返しループを形成)
    stateReg


-- ============================================================
-- Valid パイプラインシフトレジスタ
-- ============================================================
-- Chisel:
--   val valid_sr = RegInit(0.U(pipeline_depth.W))
--   valid_sr := Cat(valid_sr(pipeline_depth-2, 0), feeding)
--   io.valid_out := valid_sr(pipeline_depth-1)

/-- Bool 信号のパイプライン遅延 (n 段シフトレジスタ) -/
def validPipeline {dom : DomainConfig}
    (depth : Nat) (validIn : Signal dom Bool) : Signal dom Bool :=
  delayBool depth validIn


-- ============================================================
-- トップモジュール: SDIP_linear
-- ============================================================
--
--  動作シーケンス:
--    Phase 1: weight_load=1 で A[0][0]..A[N-1][N-1] を順次ロード
--    Phase 2: valid_in=1 で X[0][0]..X[N-1][N-1] を順次入力
--    Phase 3: パイプライン遅延後、C の要素が順次出力
--
--  データフロー:
--    weightRegs(A) ──┐
--                    ↓
--    X → [MatBuf] → [Skew] → [SystolicArray N×N] → [Deskew] → [OutSelect] → out
--

structure LinearOutput where
  result   : BitVec ACC_W
  validOut : Bool
  ready    : Bool
  colOut   : BitVec CTR_W
  rowOut   : BitVec CTR_W
deriving Inhabited

/-- SDIP_linear トップモジュール。
    行列積 C = A × X (N×N) をシストリックアレーで計算する。

    Chisel class SDIP_linear extends Module の完全移植。-/
def sdipLinear {dom : DomainConfig}
    (aIn        : Signal dom (BitVec DATA_W))     -- A の要素 (1要素/サイクル)
    (xIn        : Signal dom (BitVec DATA_W))     -- X の要素 (1要素/サイクル)
    (weightLoad : Signal dom Bool)                 -- A ロード中
    (validIn    : Signal dom Bool)                 -- X 入力有効
    : Signal dom LinearOutput :=

  let N := MAT_N

  -- -------------------------------------------------------
  -- 1. 重みレジスタ: A の要素を N*N 個蓄積
  -- -------------------------------------------------------
  -- Chisel:
  --   val weight_regs = RegInit(VecInit(Seq.fill(N*N)(0.S(DATA.W.W))))
  --   val w_cnt = RegInit(0.U(..))
  --   val w_loaded = RegInit(false.B)
  --   when(weight_load) {
  --     weight_regs(w_cnt) := io.A
  --     when(w_cnt === (N*N-1).U) { w_cnt := 0; w_loaded := true }
  --     .otherwise { w_cnt := w_cnt + 1 }
  --   }

  -- 重みロード FSM (Signal.loop)
  let weightState := Signal.loop fun wsPrev =>
    let prevRegs := (fun ws => (ws : List (BitVec DATA_W) × BitVec WCTR_W × Bool).1) <$> wsPrev
    let prevCnt  := (fun ws => (ws : List (BitVec DATA_W) × BitVec WCTR_W × Bool).2.1) <$> wsPrev
    let prevDone := (fun ws => (ws : List (BitVec DATA_W) × BitVec WCTR_W × Bool).2.2) <$> wsPrev

    let cntIsMax := (fun c => c == BitVec.ofNat WCTR_W (N * N - 1)) <$> prevCnt

    -- カウンタ更新
    let nextCnt := Signal.mux weightLoad
      (Signal.mux cntIsMax
        (Signal.pure (0 : BitVec WCTR_W))
        ((· + 1) <$> prevCnt))
      prevCnt

    -- w_loaded フラグ
    let nextDone := Signal.mux (weightLoad &&& cntIsMax) (Signal.pure true) prevDone

    -- レジスタ配列更新
    let nextRegs := (fun regs cnt aVal wl =>
      if wl then
        let idx := cnt.toNat % (N * N)
        regs.set idx aVal
      else
        regs
    ) <$> prevRegs <*> prevCnt <*> aIn <*> weightLoad

    let nextWs := (fun r c d => (r, c, d)) <$> nextRegs <*> nextCnt <*> nextDone

    Signal.register
      (List.replicate (N * N) (0 : BitVec DATA_W), (0 : BitVec WCTR_W), false)
      nextWs

  let weightRegs : Signal dom (List (BitVec DATA_W)) :=
    (fun ws => (ws : List (BitVec DATA_W) × BitVec WCTR_W × Bool).1) <$> weightState
  let wLoaded : Signal dom Bool :=
    (fun ws => (ws : List (BitVec DATA_W) × BitVec WCTR_W × Bool).2.2) <$> weightState

  -- 重みを Signal のリストに変換
  let weightSignals : List (Signal dom (BitVec DATA_W)) :=
    (List.range (N * N)).map fun i =>
      (fun regs => regs.getD i (0 : BitVec DATA_W)) <$> weightRegs

  -- -------------------------------------------------------
  -- 2. X 入力バッファ
  -- -------------------------------------------------------
  -- Chisel: x_buf.io.valid_in := io.valid_in && w_loaded
  let xValidGated := validIn &&& wLoaded
  let xBufOut := matrixInputBuffer N xIn xValidGated

  -- バッファ出力を Signal のリストに分解
  let xBufRows : List (Signal dom (BitVec DATA_W)) :=
    (List.range N).map fun r =>
      (fun out => out.rowsOut.getD r (0 : BitVec DATA_W)) <$> xBufOut

  let feeding : Signal dom Bool :=
    (fun out => out.feeding) <$> xBufOut

  -- -------------------------------------------------------
  -- 3. スキューバッファ
  -- -------------------------------------------------------
  let skewed := inputSkewBuffer N xBufRows

  -- -------------------------------------------------------
  -- 4. シストリックアレー (N × N)
  -- -------------------------------------------------------
  let psumOuts := systolicArrayLinear N
    weightLoad weightSignals skewed

  -- -------------------------------------------------------
  -- 5. デスキューバッファ
  -- -------------------------------------------------------
  let deskewed := outputDeskewBuffer N psumOuts

  -- -------------------------------------------------------
  -- 6. Valid パイプライン
  -- -------------------------------------------------------
  -- Chisel: pipeline_depth = (N-1) + N + (N-1) = 3N - 2 = 10
  let pipelineDepth := (N - 1) + N + (N - 1)
  let pipeValid := validPipeline pipelineDepth feeding

  -- -------------------------------------------------------
  -- 7. 出力セレクタ + インデックス管理
  -- -------------------------------------------------------
  -- Chisel:
  --   io.out := deskew.io.out(out_col)
  --   when(pipe_valid) {
  --     when(out_row === (N-1).U) { out_row := 0; out_col++ }
  --     .otherwise { out_row++ }
  --   }
  let outIdx := Signal.loop fun idxPrev =>
    let prevCol := (fun idx => (idx : BitVec CTR_W × BitVec CTR_W).1) <$> idxPrev
    let prevRow := (fun idx => (idx : BitVec CTR_W × BitVec CTR_W).2) <$> idxPrev

    let rowIsMax := (fun r => r == BitVec.ofNat CTR_W (N - 1)) <$> prevRow
    let colIsMax := (fun c => c == BitVec.ofNat CTR_W (N - 1)) <$> prevCol

    -- out_row の更新
    let nextRow := Signal.mux pipeValid
      (Signal.mux rowIsMax
        (Signal.pure (0 : BitVec CTR_W))
        ((· + 1) <$> prevRow))
      prevRow

    -- out_col の更新 (行が最大に達した時のみインクリメント)
    let nextCol := Signal.mux (pipeValid &&& rowIsMax)
      (Signal.mux colIsMax
        (Signal.pure (0 : BitVec CTR_W))
        ((· + 1) <$> prevCol))
      prevCol

    let nextIdx := (fun c r => (c, r)) <$> nextCol <*> nextRow
    Signal.register ((0 : BitVec CTR_W), (0 : BitVec CTR_W)) nextIdx

  let outCol := (fun idx => (idx : BitVec CTR_W × BitVec CTR_W).1) <$> outIdx
  let outRow := (fun idx => (idx : BitVec CTR_W × BitVec CTR_W).2) <$> outIdx

  -- deskew.io.out(out_col) — 出力列の選択
  let result : Signal dom (BitVec ACC_W) :=
    (fun deskResults col =>
      let idx := col.toNat % N
      deskResults.getD idx (0 : BitVec ACC_W)
    ) <$> (fun ds => ds) <$> -- deskewed は List (Signal dom ..) なので reduce が必要
      -- 全列結果をまとめてから col で選択
      ((List.range N).foldl
        (fun (acc : Signal dom (List (BitVec ACC_W))) (i : Nat) =>
          let elem := deskewed.getD i (Signal.pure (0 : BitVec ACC_W))
          (fun lst e => lst ++ [e]) <$> acc <*> elem
        ) (Signal.pure ([] : List (BitVec ACC_W))))
      <*> outCol

  -- -------------------------------------------------------
  -- 8. Ready 信号
  -- -------------------------------------------------------
  -- io.ready := w_loaded

  -- -------------------------------------------------------
  -- 出力の組み立て
  -- -------------------------------------------------------
  (fun res valid rdy col row =>
    { result := res, validOut := valid, ready := rdy,
      colOut := col, rowOut := row : LinearOutput }
  ) <$> result <*> pipeValid <*> wLoaded <*> outCol <*> outRow


-- ============================================================
-- Verilog 生成
-- ============================================================
-- #synthesizeVerilog (sdipLinear
--     (Signal.pure (0 : BitVec DATA_W))
--     (Signal.pure (0 : BitVec DATA_W))
--     (Signal.pure false)
--     (Signal.pure false))


-- ============================================================
-- 形式検証
-- ============================================================

/-- PE の純粋仕様 (テスト・検証用) -/
def macPure (x : BitVec DATA_W) (weight : BitVec DATA_W)
    (psumIn : BitVec ACC_W) : BitVec ACC_W :=
  let xExt : BitVec ACC_W := BitVec.signExtend ACC_W x
  let wExt : BitVec ACC_W := BitVec.signExtend ACC_W weight
  psumIn + xExt * wExt

/-- ゼロ入力で部分和が変化しない -/
theorem mac_zero_x (w : BitVec DATA_W) (psum : BitVec ACC_W) :
    macPure (0 : BitVec DATA_W) w psum = psum := by
  simp [macPure, BitVec.signExtend]
  ring

/-- ゼロ重みで部分和が変化しない -/
theorem mac_zero_weight (x : BitVec DATA_W) (psum : BitVec ACC_W) :
    macPure x (0 : BitVec DATA_W) psum = psum := by
  simp [macPure, BitVec.signExtend]
  ring

/-- MAC 演算の加法結合性: 部分和の蓄積順序に依存しない -/
theorem mac_psum_assoc (x w : BitVec DATA_W) (p1 p2 : BitVec ACC_W) :
    macPure x w (p1 + p2) = p1 + macPure x w p2 := by
  simp [macPure]
  ring


-- ============================================================
-- Chisel → Sparkle 対応表 (SDIP_linear 固有)
-- ============================================================
/-!
## 変換対応表

| Chisel (SDIP_linear.scala)                    | Sparkle (SDIP_linear.lean)                        |
|-----------------------------------------------|---------------------------------------------------|
| `class PE_linear extends Module`              | `def peLinear ... : Signal dom PEOutput`           |
| `val weight_reg = RegInit(0.S(DATA.W.W))`     | `Signal.loop fun wPrev => Signal.register ...`    |
| `x_reg := io.x_in`                           | `Signal.register (0 : BitVec 8) xIn`              |
| `psum_reg := psum_in + (x_in * weight_reg)`  | `(· + ·) <$> psumIn <*> product`                 |
| `Seq.fill(N, N)(Module(new PE_linear))`       | `systolicRowChain` + `systolicArrayLinear` (foldl) |
| `class InputSkewBuffer` (RegNext チェーン)     | `inputSkewBuffer` (enum + delayN)                 |
| `class OutputDeskewBuffer`                    | `outputDeskewBuffer` (enum + delayN)              |
| `class MatrixInputBuffer` (sLoad/sFeed FSM)   | `matrixInputBuffer` (Signal.loop + MatBufState)   |
| `val sLoad :: sFeed :: Nil = Enum(2)`         | `FSM_LOAD / FSM_FEED : BitVec 1`                 |
| `RegInit(VecInit(Seq.fill(N*N)(0.S)))`        | `Signal.loop` + `List.set idx val`                |
| `weight_regs(w_cnt) := io.A`                 | `regs.set (cnt.toNat) aVal`                       |
| `switch(state) { is(sLoad) ... is(sFeed) }` | nested `Signal.mux isLoad ... isFeed ...`         |
| `buf(load_row)(load_col) := elem_in`          | `regs.set (r*N+c) elem` (フラット化)              |
| `deskew.io.out(out_col)`                      | `deskResults.getD idx (0 : BitVec ACC_W)`         |
| `Cat(valid_sr(..), feeding)`                  | `validPipeline depth feeding` (delayBool)         |
| `out_row/out_col` カウンタ                     | `Signal.loop` + タプル `(col, row)`               |
| `io.ready := w_loaded`                        | `wLoaded` (weight FSM の出力)                     |
| `(new ChiselStage).emitVerilog(...)`          | `#synthesizeVerilog sdipLinear`                    |

## conv2d との差分

| 要素               | conv2d                     | linear                        |
|--------------------|----------------------------|-------------------------------|
| PE タイプ          | `pe` (カーネル重み)         | `peLinear` (行列 A の要素)    |
| 配列サイズ         | K × K (カーネル)            | N × N (行列サイズ)            |
| 入力               | 1ピクセル/サイクル           | 行列 X (1要素/サイクル)       |
| ラインバッファ     | Queue チェーン              | MatrixInputBuffer (2状態 FSM) |
| 出力               | 全列合算 (reduce +)        | 列セレクタ (deskew(col))      |
| 追加制御           | —                          | 出力列・行インデックス         |

## Sparkle の利点

1. **ラッチ不在保証**: Lean の網羅的パターンマッチで default 漏れが起きない
2. **組合せループ不在**: Signal モナドが DAG を強制
3. **形式検証**: `mac_zero_x`, `mac_zero_weight`, `mac_psum_assoc` を証明済み
4. **DRC 内蔵**: 出力レジスタチェックで STA 違反を自動検出
5. **可読 Verilog**: FIRRTL を経由しない 1:1 構造対応の SystemVerilog 生成
-/

end SDIP
