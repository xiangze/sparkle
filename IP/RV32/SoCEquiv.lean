/-
  SoCEquiv.lean — 旧SoCState（フラット124フィールド）と
                   新SoCState（7グループ構造）の等価性証明

  証明の構造:
  ────────────────────────────────────────────────────────────────
  Step 1. 状態同型 (toNew / toOld)
    各時刻 t で新旧の状態型は相互に変換可能であることを示す。
    toNew : OldSoC.SoCState → NewSoC.SoCState
    toOld : NewSoC.SoCState → OldSoC.SoCState
    + 左逆・右逆の証明 (toOld_toNew / toNew_toOld)
    これにより OldSoC.SoCState ≃ NewSoC.SoCState が成立。

  Step 2. ループボディの可換性 (body_comm)
    imem_rdata を固定したとき、以下の図式が可換であることを示す。
      toNew ∘ OldBody ∘ toOld = NewBody   (Signal 上でpoint-wise)
    すなわち任意の時刻 t・任意の grouped 状態 s に対して
      (toNew (OldBody (toOld s))).val t = (NewBody s).val t

  Step 3. 主定理 (rv32iSoCWithFirmware_eq)
    Step 1 + 2 と Signal.loop の合同性から
      OldSoC.rv32iSoCWithFirmware firmware
      = NewSoC.rv32iSoCWithFirmware firmware
    が結論される。

  注意:
  ─ body_comm の証明は「newBody s = toNew (oldBody (toOld s))」を
    simp + rfl で閉じる。両ボディは同じ Signal.* 関数呼び出し列を
    持ち、フィールド名だけが異なるため、unfold + simp で簡約できる。
  ─ フィールド順序の差異（old では exwb_funct3/idex_isMext が index
    59/60、new では PipelineState の末尾側）は toNew/toOld の定義で
    吸収される。
  ─ declare_signal_state が生成するアクセサは @[simp] lemma を持つ
    ので、展開後は bv_decide / decide で閉じるものが多い。
-/

import IP.RV32.SoC          -- 旧: OldSoC.SoCState / OldSoC.rv32iSoCBody
import IP.RV32.SoCorg  -- 新: NewSoC.SoCState / NewSoC.rv32iSoCBody

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.RV32.SoCEquiv

-- =============================================================================
-- §0  エイリアス
-- =============================================================================

abbrev OldState := SoCorg.SoCState
abbrev NewState := SoC.SoCState

-- =============================================================================
-- §1  状態同型
--
-- フィールドの並び順が異なる箇所に注意:
--   old index 58/59  : aiStatusReg, aiInputReg  → NewSoC.SoCState 直下
--   old index 59/60  : exwb_funct3, idex_isMext → PipelineState 末尾
--   old index 116/117: mcounterenReg, scounterenReg → SModeCsrState
--   old index 122/123: stallDelay, mipSoftReg → PipelineState / CSRMState
-- =============================================================================

/-- フラット OldState → グループ NewState -/
def toNew (s : OldState) : NewState :=
  { pipe :=
    { pcReg          := s.pcReg
      fetchPC        := s.fetchPC
      flushDelay     := s.flushDelay
      ifid_inst      := s.ifid_inst
      ifid_pc        := s.ifid_pc
      ifid_pc4       := s.ifid_pc4
      idex_aluOp     := s.idex_aluOp
      idex_regWrite  := s.idex_regWrite
      idex_memRead   := s.idex_memRead
      idex_memWrite  := s.idex_memWrite
      idex_memToReg  := s.idex_memToReg
      idex_branch    := s.idex_branch
      idex_jump      := s.idex_jump
      idex_auipc     := s.idex_auipc
      idex_aluSrcB   := s.idex_aluSrcB
      idex_isJalr    := s.idex_isJalr
      idex_isCsr     := s.idex_isCsr
      idex_isEcall   := s.idex_isEcall
      idex_isMret    := s.idex_isMret
      idex_rs1Val    := s.idex_rs1Val
      idex_rs2Val    := s.idex_rs2Val
      idex_imm       := s.idex_imm
      idex_rd        := s.idex_rd
      idex_rs1Idx    := s.idex_rs1Idx
      idex_rs2Idx    := s.idex_rs2Idx
      idex_funct3    := s.idex_funct3
      idex_pc        := s.idex_pc
      idex_pc4       := s.idex_pc4
      idex_csrAddr   := s.idex_csrAddr
      idex_csrFunct3 := s.idex_csrFunct3
      exwb_alu       := s.exwb_alu
      exwb_physAddr  := s.exwb_physAddr
      exwb_rd        := s.exwb_rd
      exwb_regW      := s.exwb_regW
      exwb_m2r       := s.exwb_m2r
      exwb_pc4       := s.exwb_pc4
      exwb_jump      := s.exwb_jump
      exwb_isCsr     := s.exwb_isCsr
      exwb_csrRdata  := s.exwb_csrRdata
      prev_wb_addr   := s.prev_wb_addr
      prev_wb_data   := s.prev_wb_data
      prev_wb_en     := s.prev_wb_en
      prevStoreAddr  := s.prevStoreAddr
      prevStoreData  := s.prevStoreData
      prevStoreEn    := s.prevStoreEn
      -- old index 59/60 を PipelineState 末尾へ (順序変更を吸収)
      exwb_funct3    := s.exwb_funct3
      idex_isMext    := s.idex_isMext
      -- old index 108/109
      idex_isSret      := s.idex_isSret
      idex_isSFenceVMA := s.idex_isSFenceVMA
      -- old index 122
      stallDelay     := s.stallDelay }
    clint :=
    { msipReg       := s.msipReg
      mtimeLoReg    := s.mtimeLoReg
      mtimeHiReg    := s.mtimeHiReg
      mtimecmpLoReg := s.mtimecmpLoReg
      mtimecmpHiReg := s.mtimecmpHiReg }
    csrm :=
    { mstatusReg  := s.mstatusReg
      mieReg      := s.mieReg
      mtvecReg    := s.mtvecReg
      mscratchReg := s.mscratchReg
      mepcReg     := s.mepcReg
      mcauseReg   := s.mcauseReg
      mtvalReg    := s.mtvalReg
      -- old index 123
      mipSoftReg  := s.mipSoftReg }
    smode :=
    { privMode      := s.privMode
      sieReg        := s.sieReg
      stvecReg      := s.stvecReg
      sscratchReg   := s.sscratchReg
      sepcReg       := s.sepcReg
      scauseReg     := s.scauseReg
      stvalReg      := s.stvalReg
      satpReg       := s.satpReg
      medelegReg    := s.medelegReg
      midelegReg    := s.midelegReg
      -- old index 116/117
      mcounterenReg := s.mcounterenReg
      scounterenReg := s.scounterenReg }
    aext :=
    { reservationValid := s.reservationValid
      reservationAddr  := s.reservationAddr
      idex_isAMO       := s.idex_isAMO
      idex_amoOp       := s.idex_amoOp
      exwb_isAMO       := s.exwb_isAMO
      exwb_amoOp       := s.exwb_amoOp
      pendingWriteEn   := s.pendingWriteEn
      pendingWriteAddr := s.pendingWriteAddr
      pendingWriteData := s.pendingWriteData }
    mmu :=
    { mmuStateReg        := s.mmuStateReg
      ptwStateReg        := s.ptwStateReg
      ptwVaddrReg        := s.ptwVaddrReg
      ptwPteReg          := s.ptwPteReg
      ptwMegaReg         := s.ptwMegaReg
      replPtrReg         := s.replPtrReg
      tlb0Valid          := s.tlb0Valid
      tlb0VPN            := s.tlb0VPN
      tlb0PPN            := s.tlb0PPN
      tlb0Flags          := s.tlb0Flags
      tlb0Mega           := s.tlb0Mega
      tlb1Valid          := s.tlb1Valid
      tlb1VPN            := s.tlb1VPN
      tlb1PPN            := s.tlb1PPN
      tlb1Flags          := s.tlb1Flags
      tlb1Mega           := s.tlb1Mega
      tlb2Valid          := s.tlb2Valid
      tlb2VPN            := s.tlb2VPN
      tlb2PPN            := s.tlb2PPN
      tlb2Flags          := s.tlb2Flags
      tlb2Mega           := s.tlb2Mega
      tlb3Valid          := s.tlb3Valid
      tlb3VPN            := s.tlb3VPN
      tlb3PPN            := s.tlb3PPN
      tlb3Flags          := s.tlb3Flags
      tlb3Mega           := s.tlb3Mega
      ptwIsIfetch        := s.ptwIsIfetch
      ifetchFaultPending := s.ifetchFaultPending
      dMissPC            := s.dMissPC
      dMissVaddr         := s.dMissVaddr
      dMissIsStore       := s.dMissIsStore }
    uart :=
    { uartLCRReg := s.uartLCRReg
      uartIERReg := s.uartIERReg
      uartMCRReg := s.uartMCRReg
      uartSCRReg := s.uartSCRReg
      uartDLLReg := s.uartDLLReg
      uartDLMReg := s.uartDLMReg }
    aiStatusReg := s.aiStatusReg
    aiInputReg  := s.aiInputReg
    divPending  := s.divPending }

/-- グループ NewState → フラット OldState -/
def toOld (s : NewState) : OldState :=
  let p  := s.pipe;  let c  := s.clint; let m  := s.csrm
  let sm := s.smode; let a  := s.aext;  let mu := s.mmu
  let u  := s.uart
  { pcReg          := p.pcReg
    fetchPC        := p.fetchPC
    flushDelay     := p.flushDelay
    ifid_inst      := p.ifid_inst
    ifid_pc        := p.ifid_pc
    ifid_pc4       := p.ifid_pc4
    idex_aluOp     := p.idex_aluOp
    idex_regWrite  := p.idex_regWrite
    idex_memRead   := p.idex_memRead
    idex_memWrite  := p.idex_memWrite
    idex_memToReg  := p.idex_memToReg
    idex_branch    := p.idex_branch
    idex_jump      := p.idex_jump
    idex_auipc     := p.idex_auipc
    idex_aluSrcB   := p.idex_aluSrcB
    idex_isJalr    := p.idex_isJalr
    idex_isCsr     := p.idex_isCsr
    idex_isEcall   := p.idex_isEcall
    idex_isMret    := p.idex_isMret
    idex_rs1Val    := p.idex_rs1Val
    idex_rs2Val    := p.idex_rs2Val
    idex_imm       := p.idex_imm
    idex_rd        := p.idex_rd
    idex_rs1Idx    := p.idex_rs1Idx
    idex_rs2Idx    := p.idex_rs2Idx
    idex_funct3    := p.idex_funct3
    idex_pc        := p.idex_pc
    idex_pc4       := p.idex_pc4
    idex_csrAddr   := p.idex_csrAddr
    idex_csrFunct3 := p.idex_csrFunct3
    exwb_alu       := p.exwb_alu
    exwb_physAddr  := p.exwb_physAddr
    exwb_rd        := p.exwb_rd
    exwb_regW      := p.exwb_regW
    exwb_m2r       := p.exwb_m2r
    exwb_pc4       := p.exwb_pc4
    exwb_jump      := p.exwb_jump
    exwb_isCsr     := p.exwb_isCsr
    exwb_csrRdata  := p.exwb_csrRdata
    prev_wb_addr   := p.prev_wb_addr
    prev_wb_data   := p.prev_wb_data
    prev_wb_en     := p.prev_wb_en
    prevStoreAddr  := p.prevStoreAddr
    prevStoreData  := p.prevStoreData
    prevStoreEn    := p.prevStoreEn
    msipReg        := c.msipReg
    mtimeLoReg     := c.mtimeLoReg
    mtimeHiReg     := c.mtimeHiReg
    mtimecmpLoReg  := c.mtimecmpLoReg
    mtimecmpHiReg  := c.mtimecmpHiReg
    mstatusReg     := m.mstatusReg
    mieReg         := m.mieReg
    mtvecReg       := m.mtvecReg
    mscratchReg    := m.mscratchReg
    mepcReg        := m.mepcReg
    mcauseReg      := m.mcauseReg
    mtvalReg       := m.mtvalReg
    aiStatusReg    := s.aiStatusReg
    aiInputReg     := s.aiInputReg
    exwb_funct3    := p.exwb_funct3
    idex_isMext    := p.idex_isMext
    reservationValid := a.reservationValid
    reservationAddr  := a.reservationAddr
    idex_isAMO     := a.idex_isAMO
    idex_amoOp     := a.idex_amoOp
    exwb_isAMO     := a.exwb_isAMO
    exwb_amoOp     := a.exwb_amoOp
    pendingWriteEn   := a.pendingWriteEn
    pendingWriteAddr := a.pendingWriteAddr
    pendingWriteData := a.pendingWriteData
    privMode       := sm.privMode
    sieReg         := sm.sieReg
    stvecReg       := sm.stvecReg
    sscratchReg    := sm.sscratchReg
    sepcReg        := sm.sepcReg
    scauseReg      := sm.scauseReg
    stvalReg       := sm.stvalReg
    satpReg        := sm.satpReg
    medelegReg     := sm.medelegReg
    midelegReg     := sm.midelegReg
    mmuStateReg    := mu.mmuStateReg
    ptwStateReg    := mu.ptwStateReg
    ptwVaddrReg    := mu.ptwVaddrReg
    ptwPteReg      := mu.ptwPteReg
    ptwMegaReg     := mu.ptwMegaReg
    replPtrReg     := mu.replPtrReg
    tlb0Valid      := mu.tlb0Valid
    tlb0VPN        := mu.tlb0VPN
    tlb0PPN        := mu.tlb0PPN
    tlb0Flags      := mu.tlb0Flags
    tlb0Mega       := mu.tlb0Mega
    tlb1Valid      := mu.tlb1Valid
    tlb1VPN        := mu.tlb1VPN
    tlb1PPN        := mu.tlb1PPN
    tlb1Flags      := mu.tlb1Flags
    tlb1Mega       := mu.tlb1Mega
    tlb2Valid      := mu.tlb2Valid
    tlb2VPN        := mu.tlb2VPN
    tlb2PPN        := mu.tlb2PPN
    tlb2Flags      := mu.tlb2Flags
    tlb2Mega       := mu.tlb2Mega
    tlb3Valid      := mu.tlb3Valid
    tlb3VPN        := mu.tlb3VPN
    tlb3PPN        := mu.tlb3PPN
    tlb3Flags      := mu.tlb3Flags
    tlb3Mega       := mu.tlb3Mega
    ptwIsIfetch    := mu.ptwIsIfetch
    ifetchFaultPending := mu.ifetchFaultPending
    idex_isSret      := p.idex_isSret
    idex_isSFenceVMA := p.idex_isSFenceVMA
    uartLCRReg     := u.uartLCRReg
    uartIERReg     := u.uartIERReg
    uartMCRReg     := u.uartMCRReg
    uartSCRReg     := u.uartSCRReg
    uartDLLReg     := u.uartDLLReg
    uartDLMReg     := u.uartDLMReg
    mcounterenReg  := sm.mcounterenReg
    scounterenReg  := sm.scounterenReg
    divPending     := s.divPending
    dMissPC        := mu.dMissPC
    dMissVaddr     := mu.dMissVaddr
    dMissIsStore   := mu.dMissIsStore
    stallDelay     := p.stallDelay
    mipSoftReg     := m.mipSoftReg }

-- ── 往復律 ────────────────────────────────────────────────────────

/-- フラット → グループ → フラット = id -/
theorem toOld_toNew (s : OldState) : toOld (toNew s) = s := by
  simp [toOld, toNew]

/-- グループ → フラット → グループ = id -/
theorem toNew_toOld (s : NewState) : toNew (toOld s) = s := by
  -- サブ構造まで展開するため ext/congr を先に使う
  obtain ⟨p, c, m, sm, a, mu, u, ai_st, ai_in, div⟩ := s
  simp [toNew, toOld]

-- =============================================================================
-- §2  Signal 上への持ち上げ
-- =============================================================================

def liftToNew {dom} (s : Signal dom OldState) : Signal dom NewState :=
  s.map toNew

def liftToOld {dom} (s : Signal dom NewState) : Signal dom OldState :=
  s.map toOld

theorem liftToOld_liftToNew {dom} (s : Signal dom OldState) :
    liftToOld (liftToNew s) = s := by
  simp [liftToOld, liftToNew, Signal.map_comp, Function.comp, toOld_toNew, Signal.map_id]

theorem liftToNew_liftToOld {dom} (s : Signal dom NewState) :
    liftToNew (liftToOld s) = s := by
  simp [liftToOld, liftToNew, Signal.map_comp, Function.comp, toNew_toOld, Signal.map_id]

-- =============================================================================
-- §3  ループボディの可換性
--
-- NewBody s = liftToNew (OldBody (liftToOld s))
--
-- 証明方針:
--   両ボディを unfold → 全アクセサを simp で展開すると、
--   両辺の各フィールドは同じ Signal.* 関数呼び出しになり rfl で閉じる。
--   (Lean の simp は @[simp] が付いた declare_signal_state アクセサを
--    自動的に展開するため、手動での rewrite は不要。)
-- =============================================================================

-- simp で使うアクセサ全リスト (旧・新とも)
private def oldAccessors : List Name := [
  `OldSoC.SoCState.pcReg,          `OldSoC.SoCState.fetchPC,
  `OldSoC.SoCState.flushDelay,     `OldSoC.SoCState.stallDelay,
  `OldSoC.SoCState.ifid_inst,      `OldSoC.SoCState.ifid_pc,
  `OldSoC.SoCState.ifid_pc4,
  `OldSoC.SoCState.idex_aluOp,     `OldSoC.SoCState.idex_regWrite,
  `OldSoC.SoCState.idex_memRead,   `OldSoC.SoCState.idex_memWrite,
  `OldSoC.SoCState.idex_memToReg,  `OldSoC.SoCState.idex_branch,
  `OldSoC.SoCState.idex_jump,      `OldSoC.SoCState.idex_auipc,
  `OldSoC.SoCState.idex_aluSrcB,   `OldSoC.SoCState.idex_isJalr,
  `OldSoC.SoCState.idex_isCsr,     `OldSoC.SoCState.idex_isEcall,
  `OldSoC.SoCState.idex_isMret,    `OldSoC.SoCState.idex_isMext,
  `OldSoC.SoCState.idex_isAMO,     `OldSoC.SoCState.idex_amoOp,
  `OldSoC.SoCState.idex_isSret,    `OldSoC.SoCState.idex_isSFenceVMA,
  `OldSoC.SoCState.idex_rs1Val,    `OldSoC.SoCState.idex_rs2Val,
  `OldSoC.SoCState.idex_imm,       `OldSoC.SoCState.idex_rd,
  `OldSoC.SoCState.idex_rs1Idx,    `OldSoC.SoCState.idex_rs2Idx,
  `OldSoC.SoCState.idex_funct3,    `OldSoC.SoCState.idex_pc,
  `OldSoC.SoCState.idex_pc4,       `OldSoC.SoCState.idex_csrAddr,
  `OldSoC.SoCState.idex_csrFunct3,
  `OldSoC.SoCState.exwb_alu,       `OldSoC.SoCState.exwb_physAddr,
  `OldSoC.SoCState.exwb_rd,        `OldSoC.SoCState.exwb_regW,
  `OldSoC.SoCState.exwb_m2r,       `OldSoC.SoCState.exwb_pc4,
  `OldSoC.SoCState.exwb_jump,      `OldSoC.SoCState.exwb_isCsr,
  `OldSoC.SoCState.exwb_csrRdata,  `OldSoC.SoCState.exwb_funct3,
  `OldSoC.SoCState.exwb_isAMO,     `OldSoC.SoCState.exwb_amoOp,
  `OldSoC.SoCState.prev_wb_addr,   `OldSoC.SoCState.prev_wb_data,
  `OldSoC.SoCState.prev_wb_en,
  `OldSoC.SoCState.prevStoreAddr,  `OldSoC.SoCState.prevStoreData,
  `OldSoC.SoCState.prevStoreEn,
  `OldSoC.SoCState.msipReg,        `OldSoC.SoCState.mtimeLoReg,
  `OldSoC.SoCState.mtimeHiReg,     `OldSoC.SoCState.mtimecmpLoReg,
  `OldSoC.SoCState.mtimecmpHiReg,
  `OldSoC.SoCState.mstatusReg,     `OldSoC.SoCState.mieReg,
  `OldSoC.SoCState.mtvecReg,       `OldSoC.SoCState.mscratchReg,
  `OldSoC.SoCState.mepcReg,        `OldSoC.SoCState.mcauseReg,
  `OldSoC.SoCState.mtvalReg,       `OldSoC.SoCState.mipSoftReg,
  `OldSoC.SoCState.aiStatusReg,    `OldSoC.SoCState.aiInputReg,
  `OldSoC.SoCState.reservationValid, `OldSoC.SoCState.reservationAddr,
  `OldSoC.SoCState.pendingWriteEn,   `OldSoC.SoCState.pendingWriteAddr,
  `OldSoC.SoCState.pendingWriteData,
  `OldSoC.SoCState.privMode,       `OldSoC.SoCState.sieReg,
  `OldSoC.SoCState.stvecReg,       `OldSoC.SoCState.sscratchReg,
  `OldSoC.SoCState.sepcReg,        `OldSoC.SoCState.scauseReg,
  `OldSoC.SoCState.stvalReg,       `OldSoC.SoCState.satpReg,
  `OldSoC.SoCState.medelegReg,     `OldSoC.SoCState.midelegReg,
  `OldSoC.SoCState.mmuStateReg,    `OldSoC.SoCState.ptwStateReg,
  `OldSoC.SoCState.ptwVaddrReg,    `OldSoC.SoCState.ptwPteReg,
  `OldSoC.SoCState.ptwMegaReg,     `OldSoC.SoCState.replPtrReg,
  `OldSoC.SoCState.tlb0Valid,      `OldSoC.SoCState.tlb0VPN,
  `OldSoC.SoCState.tlb0PPN,        `OldSoC.SoCState.tlb0Flags,
  `OldSoC.SoCState.tlb0Mega,
  `OldSoC.SoCState.tlb1Valid,      `OldSoC.SoCState.tlb1VPN,
  `OldSoC.SoCState.tlb1PPN,        `OldSoC.SoCState.tlb1Flags,
  `OldSoC.SoCState.tlb1Mega,
  `OldSoC.SoCState.tlb2Valid,      `OldSoC.SoCState.tlb2VPN,
  `OldSoC.SoCState.tlb2PPN,        `OldSoC.SoCState.tlb2Flags,
  `OldSoC.SoCState.tlb2Mega,
  `OldSoC.SoCState.tlb3Valid,      `OldSoC.SoCState.tlb3VPN,
  `OldSoC.SoCState.tlb3PPN,        `OldSoC.SoCState.tlb3Flags,
  `OldSoC.SoCState.tlb3Mega,
  `OldSoC.SoCState.ptwIsIfetch,    `OldSoC.SoCState.ifetchFaultPending,
  `OldSoC.SoCState.uartLCRReg,     `OldSoC.SoCState.uartIERReg,
  `OldSoC.SoCState.uartMCRReg,     `OldSoC.SoCState.uartSCRReg,
  `OldSoC.SoCState.uartDLLReg,     `OldSoC.SoCState.uartDLMReg,
  `OldSoC.SoCState.mcounterenReg,  `OldSoC.SoCState.scounterenReg,
  `OldSoC.SoCState.divPending,
  `OldSoC.SoCState.dMissPC,        `OldSoC.SoCState.dMissVaddr,
  `OldSoC.SoCState.dMissIsStore]

-- body_comm の実装:
-- 両ボディを unfold → toNew / toOld のアクセサを simp で展開 → rfl
theorem body_comm {dom : DomainConfig}
    (imem_rdata       : Signal dom (BitVec 32))
    (dmemExtWriteEn   : Signal dom Bool        := Signal.pure false)
    (dmemExtWriteAddr : Signal dom (BitVec 23) := Signal.pure 0#23)
    (dmemExtWriteData : Signal dom (BitVec 32) := Signal.pure 0#32)
    (s : Signal dom NewState) :
    NewSoC.rv32iSoCBody imem_rdata dmemExtWriteEn dmemExtWriteAddr dmemExtWriteData s
    = liftToNew (OldSoC.rv32iSoCBody imem_rdata dmemExtWriteEn dmemExtWriteAddr
                  dmemExtWriteData (liftToOld s)) := by
  -- Signal の外延性: 全時刻での値の等しさに帰着
  apply Signal.ext; intro t
  -- liftToNew / liftToOld / Signal.map を展開して点ごとの等式にする
  simp only [liftToNew, liftToOld, Signal.map]
  -- 両ボディの定義を展開する
  unfold NewSoC.rv32iSoCBody OldSoC.rv32iSoCBody
  -- toNew / toOld の全アクセサを simp で展開する
  -- (declare_signal_state が生成するアクセサは @[simp] を持つ)
  simp only [toNew, toOld,
    -- 旧アクセサ (toOld の展開で現れる)
    OldSoC.SoCState.pcReg,          OldSoC.SoCState.fetchPC,
    OldSoC.SoCState.flushDelay,     OldSoC.SoCState.stallDelay,
    OldSoC.SoCState.ifid_inst,      OldSoC.SoCState.ifid_pc,
    OldSoC.SoCState.ifid_pc4,
    OldSoC.SoCState.idex_aluOp,     OldSoC.SoCState.idex_regWrite,
    OldSoC.SoCState.idex_memRead,   OldSoC.SoCState.idex_memWrite,
    OldSoC.SoCState.idex_memToReg,  OldSoC.SoCState.idex_branch,
    OldSoC.SoCState.idex_jump,      OldSoC.SoCState.idex_auipc,
    OldSoC.SoCState.idex_aluSrcB,   OldSoC.SoCState.idex_isJalr,
    OldSoC.SoCState.idex_isCsr,     OldSoC.SoCState.idex_isEcall,
    OldSoC.SoCState.idex_isMret,    OldSoC.SoCState.idex_isMext,
    OldSoC.SoCState.idex_isAMO,     OldSoC.SoCState.idex_amoOp,
    OldSoC.SoCState.idex_isSret,    OldSoC.SoCState.idex_isSFenceVMA,
    OldSoC.SoCState.idex_rs1Val,    OldSoC.SoCState.idex_rs2Val,
    OldSoC.SoCState.idex_imm,       OldSoC.SoCState.idex_rd,
    OldSoC.SoCState.idex_rs1Idx,    OldSoC.SoCState.idex_rs2Idx,
    OldSoC.SoCState.idex_funct3,    OldSoC.SoCState.idex_pc,
    OldSoC.SoCState.idex_pc4,       OldSoC.SoCState.idex_csrAddr,
    OldSoC.SoCState.idex_csrFunct3,
    OldSoC.SoCState.exwb_alu,       OldSoC.SoCState.exwb_physAddr,
    OldSoC.SoCState.exwb_rd,        OldSoC.SoCState.exwb_regW,
    OldSoC.SoCState.exwb_m2r,       OldSoC.SoCState.exwb_pc4,
    OldSoC.SoCState.exwb_jump,      OldSoC.SoCState.exwb_isCsr,
    OldSoC.SoCState.exwb_csrRdata,  OldSoC.SoCState.exwb_funct3,
    OldSoC.SoCState.exwb_isAMO,     OldSoC.SoCState.exwb_amoOp,
    OldSoC.SoCState.prev_wb_addr,   OldSoC.SoCState.prev_wb_data,
    OldSoC.SoCState.prev_wb_en,
    OldSoC.SoCState.prevStoreAddr,  OldSoC.SoCState.prevStoreData,
    OldSoC.SoCState.prevStoreEn,
    OldSoC.SoCState.msipReg,        OldSoC.SoCState.mtimeLoReg,
    OldSoC.SoCState.mtimeHiReg,     OldSoC.SoCState.mtimecmpLoReg,
    OldSoC.SoCState.mtimecmpHiReg,
    OldSoC.SoCState.mstatusReg,     OldSoC.SoCState.mieReg,
    OldSoC.SoCState.mtvecReg,       OldSoC.SoCState.mscratchReg,
    OldSoC.SoCState.mepcReg,        OldSoC.SoCState.mcauseReg,
    OldSoC.SoCState.mtvalReg,       OldSoC.SoCState.mipSoftReg,
    OldSoC.SoCState.aiStatusReg,    OldSoC.SoCState.aiInputReg,
    OldSoC.SoCState.reservationValid, OldSoC.SoCState.reservationAddr,
    OldSoC.SoCState.pendingWriteEn,   OldSoC.SoCState.pendingWriteAddr,
    OldSoC.SoCState.pendingWriteData,
    OldSoC.SoCState.privMode,       OldSoC.SoCState.sieReg,
    OldSoC.SoCState.stvecReg,       OldSoC.SoCState.sscratchReg,
    OldSoC.SoCState.sepcReg,        OldSoC.SoCState.scauseReg,
    OldSoC.SoCState.stvalReg,       OldSoC.SoCState.satpReg,
    OldSoC.SoCState.medelegReg,     OldSoC.SoCState.midelegReg,
    OldSoC.SoCState.mmuStateReg,    OldSoC.SoCState.ptwStateReg,
    OldSoC.SoCState.ptwVaddrReg,    OldSoC.SoCState.ptwPteReg,
    OldSoC.SoCState.ptwMegaReg,     OldSoC.SoCState.replPtrReg,
    OldSoC.SoCState.tlb0Valid,      OldSoC.SoCState.tlb0VPN,
    OldSoC.SoCState.tlb0PPN,        OldSoC.SoCState.tlb0Flags,
    OldSoC.SoCState.tlb0Mega,       OldSoC.SoCState.tlb1Valid,
    OldSoC.SoCState.tlb1VPN,        OldSoC.SoCState.tlb1PPN,
    OldSoC.SoCState.tlb1Flags,      OldSoC.SoCState.tlb1Mega,
    OldSoC.SoCState.tlb2Valid,      OldSoC.SoCState.tlb2VPN,
    OldSoC.SoCState.tlb2PPN,        OldSoC.SoCState.tlb2Flags,
    OldSoC.SoCState.tlb2Mega,       OldSoC.SoCState.tlb3Valid,
    OldSoC.SoCState.tlb3VPN,        OldSoC.SoCState.tlb3PPN,
    OldSoC.SoCState.tlb3Flags,      OldSoC.SoCState.tlb3Mega,
    OldSoC.SoCState.ptwIsIfetch,    OldSoC.SoCState.ifetchFaultPending,
    OldSoC.SoCState.uartLCRReg,     OldSoC.SoCState.uartIERReg,
    OldSoC.SoCState.uartMCRReg,     OldSoC.SoCState.uartSCRReg,
    OldSoC.SoCState.uartDLLReg,     OldSoC.SoCState.uartDLMReg,
    OldSoC.SoCState.mcounterenReg,  OldSoC.SoCState.scounterenReg,
    OldSoC.SoCState.divPending,
    OldSoC.SoCState.dMissPC,        OldSoC.SoCState.dMissVaddr,
    OldSoC.SoCState.dMissIsStore,
    -- 新アクセサ (toNew の展開で現れる)
    NewSoC.SoCState.pipe,  NewSoC.SoCState.clint, NewSoC.SoCState.csrm,
    NewSoC.SoCState.smode, NewSoC.SoCState.aext,  NewSoC.SoCState.mmu,
    NewSoC.SoCState.uart,
    NewSoC.SoCState.aiStatusReg,       NewSoC.SoCState.aiInputReg,
    NewSoC.SoCState.divPending,
    NewSoC.PipelineState.pcReg,        NewSoC.PipelineState.fetchPC,
    NewSoC.PipelineState.flushDelay,   NewSoC.PipelineState.stallDelay,
    NewSoC.PipelineState.ifid_inst,    NewSoC.PipelineState.ifid_pc,
    NewSoC.PipelineState.ifid_pc4,
    NewSoC.PipelineState.idex_aluOp,   NewSoC.PipelineState.idex_regWrite,
    NewSoC.PipelineState.idex_memRead, NewSoC.PipelineState.idex_memWrite,
    NewSoC.PipelineState.idex_memToReg,NewSoC.PipelineState.idex_branch,
    NewSoC.PipelineState.idex_jump,    NewSoC.PipelineState.idex_auipc,
    NewSoC.PipelineState.idex_aluSrcB, NewSoC.PipelineState.idex_isJalr,
    NewSoC.PipelineState.idex_isCsr,   NewSoC.PipelineState.idex_isEcall,
    NewSoC.PipelineState.idex_isMret,  NewSoC.PipelineState.idex_isMext,
    NewSoC.PipelineState.idex_isAMO,   NewSoC.PipelineState.idex_amoOp,
    NewSoC.PipelineState.idex_isSret,  NewSoC.PipelineState.idex_isSFenceVMA,
    NewSoC.PipelineState.idex_rs1Val,  NewSoC.PipelineState.idex_rs2Val,
    NewSoC.PipelineState.idex_imm,     NewSoC.PipelineState.idex_rd,
    NewSoC.PipelineState.idex_rs1Idx,  NewSoC.PipelineState.idex_rs2Idx,
    NewSoC.PipelineState.idex_funct3,  NewSoC.PipelineState.idex_pc,
    NewSoC.PipelineState.idex_pc4,     NewSoC.PipelineState.idex_csrAddr,
    NewSoC.PipelineState.idex_csrFunct3,
    NewSoC.PipelineState.exwb_alu,     NewSoC.PipelineState.exwb_physAddr,
    NewSoC.PipelineState.exwb_rd,      NewSoC.PipelineState.exwb_regW,
    NewSoC.PipelineState.exwb_m2r,     NewSoC.PipelineState.exwb_pc4,
    NewSoC.PipelineState.exwb_jump,    NewSoC.PipelineState.exwb_isCsr,
    NewSoC.PipelineState.exwb_csrRdata,NewSoC.PipelineState.exwb_funct3,
    NewSoC.PipelineState.exwb_isAMO,   NewSoC.PipelineState.exwb_amoOp,
    NewSoC.PipelineState.prev_wb_addr, NewSoC.PipelineState.prev_wb_data,
    NewSoC.PipelineState.prev_wb_en,
    NewSoC.PipelineState.prevStoreAddr,NewSoC.PipelineState.prevStoreData,
    NewSoC.PipelineState.prevStoreEn,
    NewSoC.CLINTState.msipReg,         NewSoC.CLINTState.mtimeLoReg,
    NewSoC.CLINTState.mtimeHiReg,      NewSoC.CLINTState.mtimecmpLoReg,
    NewSoC.CLINTState.mtimecmpHiReg,
    NewSoC.CSRMState.mstatusReg,       NewSoC.CSRMState.mieReg,
    NewSoC.CSRMState.mtvecReg,         NewSoC.CSRMState.mscratchReg,
    NewSoC.CSRMState.mepcReg,          NewSoC.CSRMState.mcauseReg,
    NewSoC.CSRMState.mtvalReg,         NewSoC.CSRMState.mipSoftReg,
    NewSoC.SModeCsrState.privMode,     NewSoC.SModeCsrState.sieReg,
    NewSoC.SModeCsrState.stvecReg,     NewSoC.SModeCsrState.sscratchReg,
    NewSoC.SModeCsrState.sepcReg,      NewSoC.SModeCsrState.scauseReg,
    NewSoC.SModeCsrState.stvalReg,     NewSoC.SModeCsrState.satpReg,
    NewSoC.SModeCsrState.medelegReg,   NewSoC.SModeCsrState.midelegReg,
    NewSoC.SModeCsrState.mcounterenReg,NewSoC.SModeCsrState.scounterenReg,
    NewSoC.AExtState.reservationValid, NewSoC.AExtState.reservationAddr,
    NewSoC.AExtState.idex_isAMO,       NewSoC.AExtState.idex_amoOp,
    NewSoC.AExtState.exwb_isAMO,       NewSoC.AExtState.exwb_amoOp,
    NewSoC.AExtState.pendingWriteEn,   NewSoC.AExtState.pendingWriteAddr,
    NewSoC.AExtState.pendingWriteData,
    NewSoC.MMUState.mmuStateReg,       NewSoC.MMUState.ptwStateReg,
    NewSoC.MMUState.ptwVaddrReg,       NewSoC.MMUState.ptwPteReg,
    NewSoC.MMUState.ptwMegaReg,        NewSoC.MMUState.replPtrReg,
    NewSoC.MMUState.tlb0Valid,         NewSoC.MMUState.tlb0VPN,
    NewSoC.MMUState.tlb0PPN,           NewSoC.MMUState.tlb0Flags,
    NewSoC.MMUState.tlb0Mega,          NewSoC.MMUState.tlb1Valid,
    NewSoC.MMUState.tlb1VPN,           NewSoC.MMUState.tlb1PPN,
    NewSoC.MMUState.tlb1Flags,         NewSoC.MMUState.tlb1Mega,
    NewSoC.MMUState.tlb2Valid,         NewSoC.MMUState.tlb2VPN,
    NewSoC.MMUState.tlb2PPN,           NewSoC.MMUState.tlb2Flags,
    NewSoC.MMUState.tlb2Mega,          NewSoC.MMUState.tlb3Valid,
    NewSoC.MMUState.tlb3VPN,           NewSoC.MMUState.tlb3PPN,
    NewSoC.MMUState.tlb3Flags,         NewSoC.MMUState.tlb3Mega,
    NewSoC.MMUState.ptwIsIfetch,       NewSoC.MMUState.ifetchFaultPending,
    NewSoC.MMUState.dMissPC,           NewSoC.MMUState.dMissVaddr,
    NewSoC.MMUState.dMissIsStore,
    NewSoC.UARTState.uartLCRReg,       NewSoC.UARTState.uartIERReg,
    NewSoC.UARTState.uartMCRReg,       NewSoC.UARTState.uartSCRReg,
    NewSoC.UARTState.uartDLLReg,       NewSoC.UARTState.uartDLMReg]
  -- アクセサ展開後は両辺が同一式になるため rfl で閉じる

-- =============================================================================
-- §4  Signal.loop の合同性
-- =============================================================================

/-- ループ合同性補題:
    body_new s = liftToNew (body_old (liftToOld s))  が成り立てば
    Signal.loop body_new = liftToNew (Signal.loop body_old)    -/
private theorem loop_congr_via_iso {dom : DomainConfig}
    {body_old : Signal dom OldState → Signal dom OldState}
    {body_new : Signal dom NewState → Signal dom NewState}
    (h : ∀ s, body_new s = liftToNew (body_old (liftToOld s))) :
    Signal.loop body_new = liftToNew (Signal.loop body_old) := by
  -- liftToNew (Signal.loop body_old) が body_new の不動点であることを示し、
  -- Signal.loop の一意性から等式を得る。
  symm
  apply Signal.loop_unique
  intro s hs
  -- hs : s = body_new s  (s は body_new の不動点)
  -- 目標 : liftToNew (body_old (liftToOld s)) = s
  rw [← hs, h s]

-- =============================================================================
-- §5  主定理と帰結
-- =============================================================================

/-- **主定理**: 旧・新 `rv32iSoCWithFirmware` は全ての firmware に対して等しい。

    外部から観測可能な出力 (Signal dom (BitVec 32) = pc の時系列) において
    フラット設計とグループ設計は完全に同一の振る舞いをする。 -/
theorem rv32iSoCWithFirmware_eq {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32) :
    OldSoC.rv32iSoCWithFirmware firmware
    = NewSoC.rv32iSoCWithFirmware firmware := by
  unfold OldSoC.rv32iSoCWithFirmware NewSoC.rv32iSoCWithFirmware
  -- Signal.fst の合同性: ループ等価性があれば fst も等しい
  congr 1
  -- WithFirmwareBody = rv32iSoCBody ∘ fetchPC-rdata を展開
  unfold OldSoC.rv32iSoCWithFirmwareBody NewSoC.rv32iSoCWithFirmwareBody
  apply loop_congr_via_iso
  intro s
  -- fetchPC アクセス方法の差異 (Old: .fetchPC s  /  New: .pipe.fetchPC s) を解消
  simp only [liftToOld, Signal.map, toOld,
    NewSoC.SoCState.pipe, NewSoC.PipelineState.fetchPC]
  exact body_comm firmware (Signal.pure false) (Signal.pure 0#23) (Signal.pure 0#32) s

/-- **全状態の等価性**: 旧ループを toNew で変換したものが新ループに等しい。
    これにより CSR / MMU / UART 等の全フィールドの一致が保証される。 -/
theorem rv32iSoCFull_eq {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32) :
    liftToNew (Signal.loop (OldSoC.rv32iSoCWithFirmwareBody firmware))
    = Signal.loop (NewSoC.rv32iSoCWithFirmwareBody firmware) := by
  symm
  unfold OldSoC.rv32iSoCWithFirmwareBody NewSoC.rv32iSoCWithFirmwareBody
  apply loop_congr_via_iso
  intro s
  simp only [liftToOld, Signal.map, toOld,
    NewSoC.SoCState.pipe, NewSoC.PipelineState.fetchPC]
  exact body_comm firmware (Signal.pure false) (Signal.pure 0#23) (Signal.pure 0#32) s

end Sparkle.IP.RV32.SoCEquiv
