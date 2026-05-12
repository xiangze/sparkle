/-
  RV32I 4-Stage Pipeline — Signal DSL

  Uses Signal.loop with a 4-sub-state structure for feedback.
  Pipeline registers are split into 4 declare_signal_state groups:

    PCIFRegs   (6 regs):  pcReg, fetchPC, flushDelay, ifid_*
    IDEXLatch  (24 regs): idex_*
    EXWBLatch  (8 regs):  exwb_*
    PrevWBStore(6 regs):  prev_wb_*, prevStore*

  Full state = PCIFRegs × IDEXLatch × EXWBLatch × PrevWBStore
  projN! uses 4-element outer index; stage accessors handle inner fields.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

namespace Sparkle.IP.RV32

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- NOP instruction = ADDI x0, x0, 0
def nopInst : BitVec 32 := 0x00000013#32

-- Number of pipeline registers (6 + 24 + 8 + 6)
def numPipelineRegs : Nat := 44

-- =============================================================================
-- Pipeline register state grouped by stage
-- =============================================================================

declare_signal_state PCIFRegs
  | pcReg      : BitVec 32 := 0#32
  | fetchPC    : BitVec 32 := 0#32
  | flushDelay : Bool      := false
  | ifid_inst  : BitVec 32 := 0x00000013#32
  | ifid_pc    : BitVec 32 := 0#32
  | ifid_pc4   : BitVec 32 := 0#32

declare_signal_state IDEXLatch
  | aluOp     : BitVec 4  := 0#4
  | regWrite  : Bool      := false
  | memRead   : Bool      := false
  | memWrite  : Bool      := false
  | memToReg  : Bool      := false
  | branch    : Bool      := false
  | jump      : Bool      := false
  | auipc     : Bool      := false
  | aluSrcB   : Bool      := false
  | isJalr    : Bool      := false
  | isCsr     : Bool      := false
  | isEcall   : Bool      := false
  | isMret    : Bool      := false
  | rs1Val    : BitVec 32 := 0#32
  | rs2Val    : BitVec 32 := 0#32
  | imm       : BitVec 32 := 0#32
  | rd        : BitVec 5  := 0#5
  | rs1Idx    : BitVec 5  := 0#5
  | rs2Idx    : BitVec 5  := 0#5
  | funct3    : BitVec 3  := 0#3
  | pc        : BitVec 32 := 0#32
  | pc4       : BitVec 32 := 0#32
  | csrAddr   : BitVec 12 := 0#12
  | csrFunct3 : BitVec 3  := 0#3

declare_signal_state EXWBLatch
  | alu      : BitVec 32 := 0#32
  | rd       : BitVec 5  := 0#5
  | regW     : Bool      := false
  | m2r      : Bool      := false
  | pc4      : BitVec 32 := 0#32
  | jump     : Bool      := false
  | isCsr    : Bool      := false
  | csrRdata : BitVec 32 := 0#32

declare_signal_state PrevWBStore
  | wbAddr    : BitVec 5  := 0#5
  | wbData    : BitVec 32 := 0#32
  | wbEn      : Bool      := false
  | storeAddr : BitVec 32 := 0#32
  | storeData : BitVec 32 := 0#32
  | storeEn   : Bool      := false

/-- RV32I 4-stage pipeline core (Signal DSL).

    Uses Signal.loop with state = PCIFRegs × IDEXLatch × EXWBLatch × PrevWBStore.
    Output: debug_pc (pcReg from PCIFRegs). -/
def rv32iCore {dom : DomainConfig}
    (imem_rdata : Signal dom (BitVec 32))
    (dmem_rdata : Signal dom (BitVec 32))
    (csr_rdata : Signal dom (BitVec 32))
    (trap_taken : Signal dom Bool)
    (trap_target : Signal dom (BitVec 32))
    (mret_target : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=  -- debug_pc
  let pipeline := Signal.loop fun state =>
    -- =================================================================
    -- Unbundle: extract sub-states, then individual register outputs
    -- =================================================================
    let pcif := projN! state 4 0
    let idex := projN! state 4 1
    let exwb := projN! state 4 2
    let prev := projN! state 4 3

    -- PC/IF stage registers
    let pcReg         := PCIFRegs.pcReg      pcif
    let fetchPC       := PCIFRegs.fetchPC    pcif
    let flushDelay    := PCIFRegs.flushDelay pcif
    let ifid_inst     := PCIFRegs.ifid_inst  pcif
    let ifid_pc       := PCIFRegs.ifid_pc    pcif
    let ifid_pc4      := PCIFRegs.ifid_pc4   pcif

    -- ID/EX latch registers
    let idex_aluOp    := IDEXLatch.aluOp     idex
    let idex_regWrite := IDEXLatch.regWrite  idex
    let idex_memRead  := IDEXLatch.memRead   idex
    let idex_memWrite := IDEXLatch.memWrite  idex
    let idex_memToReg := IDEXLatch.memToReg  idex
    let idex_branch   := IDEXLatch.branch    idex
    let idex_jump     := IDEXLatch.jump      idex
    let idex_auipc    := IDEXLatch.auipc     idex
    let idex_aluSrcB  := IDEXLatch.aluSrcB   idex
    let idex_isJalr   := IDEXLatch.isJalr    idex
    let idex_isCsr    := IDEXLatch.isCsr     idex
    let idex_isEcall  := IDEXLatch.isEcall   idex
    let idex_isMret   := IDEXLatch.isMret    idex
    let idex_rs1Val   := IDEXLatch.rs1Val    idex
    let idex_rs2Val   := IDEXLatch.rs2Val    idex
    let idex_imm      := IDEXLatch.imm       idex
    let idex_rd       := IDEXLatch.rd        idex
    let idex_rs1Idx   := IDEXLatch.rs1Idx    idex
    let idex_rs2Idx   := IDEXLatch.rs2Idx    idex
    let idex_funct3   := IDEXLatch.funct3    idex
    let idex_pc       := IDEXLatch.pc        idex
    let idex_pc4      := IDEXLatch.pc4       idex
    let idex_csrAddr  := IDEXLatch.csrAddr   idex
    let idex_csrFunct3 := IDEXLatch.csrFunct3 idex

    -- EX/WB latch registers
    let exwb_alu      := EXWBLatch.alu       exwb
    let exwb_rd       := EXWBLatch.rd        exwb
    let exwb_regW     := EXWBLatch.regW      exwb
    let exwb_m2r      := EXWBLatch.m2r       exwb
    let exwb_pc4      := EXWBLatch.pc4       exwb
    let exwb_jump     := EXWBLatch.jump      exwb
    let exwb_isCsr    := EXWBLatch.isCsr     exwb
    let exwb_csrRdata := EXWBLatch.csrRdata  exwb

    -- Previous WB / store-forwarding registers
    let prev_wb_addr  := PrevWBStore.wbAddr    prev
    let prev_wb_data  := PrevWBStore.wbData    prev
    let prev_wb_en    := PrevWBStore.wbEn      prev
    let prevStoreAddr := PrevWBStore.storeAddr prev
    let prevStoreData := PrevWBStore.storeData prev
    let prevStoreEn   := PrevWBStore.storeEn   prev

    -- =================================================================
    -- WB Stage (compute first — needed for forwarding/bypass)
    -- =================================================================
    -- Store-to-load forwarding (split compound lambda)
    let storeAddrHi := prevStoreAddr[31,2] --(BitVec.extractLsb' 2 30 ·)
    let loadAddrHi := exwb_alu[31,2]
    let addrMatch := storeAddrHi === loadAddrHi
    let storeLoadMatch := prevStoreEn &&& addrMatch
    let dmemRdataFwd := Signal.mux storeLoadMatch prevStoreData dmem_rdata

    let wb_result := Signal.mux exwb_isCsr exwb_csrRdata
                       (Signal.mux exwb_jump exwb_pc4
                       (Signal.mux exwb_m2r dmemRdataFwd
                         exwb_alu))
    let wbRdNz_check := exwb_rd === 0#5
    let wbRdNz := ~~~wbRdNz_check
    let wb_addr := exwb_rd
    let wb_data := wb_result
    let wb_en   := exwb_regW &&& wbRdNz

    -- =================================================================
    -- EX Stage
    -- =================================================================
    -- WB→EX forwarding
    let fwd_rs1_match := wb_en &&& (wb_addr === idex_rs1Idx)
    let fwd_rs2_match := wb_en &&& (wb_addr === idex_rs2Idx)
    let ex_rs1 := Signal.mux fwd_rs1_match wb_data idex_rs1Val
    let ex_rs2 := Signal.mux fwd_rs2_match wb_data idex_rs2Val
    -- ALU
    let alu_a := Signal.mux idex_auipc idex_pc ex_rs1
    let alu_b := Signal.mux idex_aluSrcB idex_imm ex_rs2
    let alu_result := aluSignal idex_aluOp alu_a alu_b
    -- Branch
    let branchCond := branchCompSignal idex_funct3 ex_rs1 ex_rs2
    let branchTaken := idex_branch &&& branchCond
    -- Branch/jump target
    let brTarget := idex_pc + idex_imm
    let jalrSum  := ex_rs1 + idex_imm
    let jalrTarget := jalrSum &&& 0xFFFFFFFE#32
    let jumpTarget := Signal.mux idex_isJalr jalrTarget brTarget
    -- Flush
    let flush := (branchTaken ||| idex_jump) ||| (trap_taken ||| idex_isMret)
    let flushOrDelay := flush ||| flushDelay

    -- =================================================================
    -- Hazard / Stall (depends on idex outputs and ID decode)
    -- =================================================================
    -- ID decode (from ifid_inst)
    let id_opcode := ifid_inst[6,0] --.map (BitVec.extractLsb' 0 7 ·)
    let id_rd     := ifid_inst[11,7]
    let id_funct3 := ifid_inst[14,12]
    let id_rs1    := ifid_inst[19,15]
    let id_rs2    := ifid_inst[24,20]
    let id_funct7 := ifid_inst[31,25]
    let id_imm := immGenSignal ifid_inst id_opcode
    let id_aluOp := aluControlSignal id_opcode id_funct3 id_funct7
    -- Control signals
    let id_isALUrr  := id_opcode === 0b0110011#7
    let id_isALUimm := id_opcode === 0b0010011#7
    let id_isLoad   := id_opcode === 0b0000011#7
    let id_isStore  := id_opcode === 0b0100011#7
    let id_isBranch := id_opcode === 0b1100011#7
    let id_isLUI    := id_opcode === 0b0110111#7
    let id_isAUIPC  := id_opcode === 0b0010111#7
    let id_isJAL    := id_opcode === 0b1101111#7
    let id_isJALR   := id_opcode === 0b1100111#7
    let id_isSystem := id_opcode === 0b1110011#7
    -- Derived
    let id_aluSrcB := ((id_isALUimm ||| id_isLoad) ||| (id_isStore ||| id_isLUI)) |||
                      ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_regWrite := ((id_isALUrr ||| id_isALUimm) ||| (id_isLoad ||| id_isLUI)) |||
                       ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_memRead  := id_isLoad
    let id_memWrite := id_isStore
    let id_memToReg := id_isLoad
    let id_jump     := id_isJAL ||| id_isJALR
    let id_auipc    := id_isAUIPC ||| id_isJAL
    let f3isZero := id_funct3 === 0#3
    let f3notZero := ~~~f3isZero
    let id_isCsr := id_isSystem &&& f3notZero
    let id_isEcall := id_isSystem &&& f3isZero
    let id_csrAddr := ifid_inst[31,20] --.map (BitVec.extractLsb' 20 12 ·)
    let mretField :=  ifid_inst[31,20]
    let isMretField := mretField === 0x302#12
    let id_isMret := id_isSystem &&& isMretField

    -- Stall
    let stall := hazardSignal idex_memRead idex_rd id_rs1 id_rs2

    -- =================================================================
    -- Register File (dual-read, single-write via Signal.memory)
    -- =================================================================
    let rf_rs1_addr := Signal.mux stall id_rs1 imem_rdata[19,15]
    let rf_rs2_addr := Signal.mux stall id_rs2 imem_rdata[24,20]
    let rf_rs1_raw := Signal.memory wb_addr wb_data wb_en rf_rs1_addr
    let rf_rs2_raw := Signal.memory wb_addr wb_data wb_en rf_rs2_addr
    -- WB→ID bypass
    let wb_fwd_rs1 := wb_en &&& (wb_addr === id_rs1)
    let wb_fwd_rs2 := wb_en &&& (wb_addr === id_rs2)
    -- Previous-cycle WB bypass
    let prev_fwd_rs1 := prev_wb_en &&& (prev_wb_addr === id_rs1)
    let prev_fwd_rs2 := prev_wb_en &&& (prev_wb_addr === id_rs2)
    let rf_rs1_bypassed := Signal.mux wb_fwd_rs1 wb_data
                             (Signal.mux prev_fwd_rs1 prev_wb_data rf_rs1_raw)
    let rf_rs2_bypassed := Signal.mux wb_fwd_rs2 wb_data
                             (Signal.mux prev_fwd_rs2 prev_wb_data rf_rs2_raw)
    -- x0 hardwiring
    let id_rs1Val := Signal.mux (id_rs1 === 0#5)
                       (Signal.pure 0#32) rf_rs1_bypassed
    let id_rs2Val := Signal.mux (id_rs2 === 0#5)
                       (Signal.pure 0#32) rf_rs2_bypassed

    -- =================================================================
    -- IF Stage: PC + fetch
    -- =================================================================
    let pcPlus4 := pcReg + 4#32
    let fetchPCIn := Signal.mux stall fetchPC pcReg
    let fetchPCPlus4 := fetchPC + 4#32

    -- =================================================================
    -- IF/ID register inputs
    -- =================================================================
    let ifid_inst_in := Signal.mux flushOrDelay (Signal.pure nopInst) (Signal.mux stall ifid_inst imem_rdata)
    let ifid_pc_in := Signal.mux stall ifid_pc fetchPC
    let ifid_pc4_in := Signal.mux stall ifid_pc4 fetchPCPlus4

    -- =================================================================
    -- ID/EX register inputs (squash on stall or flush)
    -- =================================================================
    let squash := stall ||| flushOrDelay
    -- CSR interface
    let csrIsImm_bit := idex_csrFunct3[2]
    let csrIsImm := csrIsImm_bit === 1#1
    let csrZimm  := 0#27 ++ idex_rs1Idx

    -- =================================================================
    -- PC Next
    -- =================================================================
    let pcNext := Signal.mux trap_taken trap_target
                    (Signal.mux idex_isMret mret_target
                    (Signal.mux flush jumpTarget
                    (Signal.mux stall pcReg
                      pcPlus4)))

    -- =================================================================
    -- Rebundle: create next-cycle registers per stage
    -- =================================================================
    let pcifNext := bundleAll! [
      Signal.register 0#32 pcNext,
      Signal.register 0#32 fetchPCIn,
      Signal.register false flush,
      Signal.register 0x00000013#32 ifid_inst_in,
      Signal.register 0#32 ifid_pc_in,
      Signal.register 0#32 ifid_pc4_in
    ]

    let idexNext := bundleAll! [
      Signal.register 0#4 (Signal.mux squash (Signal.pure 0#4) id_aluOp),
      Signal.register false (Signal.mux squash (Signal.pure false) id_regWrite),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memRead),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memWrite),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memToReg),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isBranch),
      Signal.register false (Signal.mux squash (Signal.pure false) id_jump),
      Signal.register false (Signal.mux squash (Signal.pure false) id_auipc),
      Signal.register false (Signal.mux squash (Signal.pure false) id_aluSrcB),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isJALR),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isCsr),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isEcall),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isMret),
      Signal.register 0#32 id_rs1Val,
      Signal.register 0#32 id_rs2Val,
      Signal.register 0#32 id_imm,
      Signal.register 0#5 (Signal.mux squash (Signal.pure 0#5) id_rd),
      Signal.register 0#5 id_rs1,
      Signal.register 0#5 id_rs2,
      Signal.register 0#3 id_funct3,
      Signal.register 0#32 ifid_pc,
      Signal.register 0#32 ifid_pc4,
      Signal.register 0#12 id_csrAddr,
      Signal.register 0#3 id_funct3
    ]

    let exwbNext := bundleAll! [
      Signal.register 0#32 alu_result,
      Signal.register 0#5 idex_rd,
      Signal.register false idex_regWrite,
      Signal.register false idex_memToReg,
      Signal.register 0#32 idex_pc4,
      Signal.register false idex_jump,
      Signal.register false idex_isCsr,
      Signal.register 0#32 csr_rdata
    ]

    let prevNext := bundleAll! [
      Signal.register 0#5 wb_addr,
      Signal.register 0#32 wb_data,
      Signal.register false wb_en,
      Signal.register 0#32 alu_result,
      Signal.register 0#32 ex_rs2,
      Signal.register false idex_memWrite
    ]

    bundleAll! [pcifNext, idexNext, exwbNext, prevNext]

  -- Output: debug_pc = pcReg
  PCIFRegs.pcReg (Signal.fst pipeline)

-- Test synthesis of the pipeline core
#synthesizeVerilog rv32iCore

end Sparkle.IP.RV32
