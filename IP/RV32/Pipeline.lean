/-
  RV32I 5-Stage Pipeline — Signal DSL

  Classic 5 stages: IF → ID → EX → MEM → WB

  State = PCIFRegs × IDEXLatch × EXMEMLatch × MEMWBLatch
  projN! uses 4-element outer index; stage accessors handle inner fields.

  Forwarding paths:
    MEM→EX : EX/MEM ALU result forwarded to EX operands (highest priority)
    WB→EX  : MEM/WB result forwarded to EX operands
    WB→ID  : WB result bypassed into register file reads
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

def nopInst : BitVec 32 := 0x00000013#32

-- =============================================================================
-- Pipeline register state grouped by stage boundary
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

-- EX/MEM pipeline latch (carries EX outputs into the MEM stage)
declare_signal_state EXMEMLatch
  | alu      : BitVec 32 := 0#32
  | rd       : BitVec 5  := 0#5
  | regW     : Bool      := false
  | memR     : Bool      := false
  | memW     : Bool      := false
  | m2r      : Bool      := false
  | rs2Val   : BitVec 32 := 0#32  -- store data
  | funct3   : BitVec 3  := 0#3   -- load/store width
  | pc4      : BitVec 32 := 0#32
  | jump     : Bool      := false
  | isCsr    : Bool      := false
  | csrRdata : BitVec 32 := 0#32

-- MEM/WB pipeline latch (carries MEM outputs into the WB stage)
declare_signal_state MEMWBLatch
  | aluResult : BitVec 32 := 0#32
  | memData   : BitVec 32 := 0#32  -- dmem read result
  | rd        : BitVec 5  := 0#5
  | regW      : Bool      := false
  | m2r       : Bool      := false
  | pc4       : BitVec 32 := 0#32
  | jump      : Bool      := false
  | isCsr     : Bool      := false
  | csrRdata  : BitVec 32 := 0#32

/-- RV32I 5-stage pipeline core (Signal DSL).

    State = PCIFRegs × IDEXLatch × EXMEMLatch × MEMWBLatch.
    Output: debug_pc (pcReg from PCIFRegs). -/
def rv32iCore {dom : DomainConfig}
    (imem_rdata : Signal dom (BitVec 32))
    (dmem_rdata : Signal dom (BitVec 32))
    (csr_rdata  : Signal dom (BitVec 32))
    (trap_taken  : Signal dom Bool)
    (trap_target : Signal dom (BitVec 32))
    (mret_target : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let pipeline := Signal.loop fun state =>
    -- =================================================================
    -- Unbundle: extract sub-states, then individual register outputs
    -- =================================================================
    let pcif  := projN! state 4 0
    let idex  := projN! state 4 1
    let exmem := projN! state 4 2
    let memwb := projN! state 4 3

    -- IF/ID registers
    let pcReg      := PCIFRegs.pcReg      pcif
    let fetchPC    := PCIFRegs.fetchPC    pcif
    let flushDelay := PCIFRegs.flushDelay pcif
    let ifid_inst  := PCIFRegs.ifid_inst  pcif
    let ifid_pc    := PCIFRegs.ifid_pc    pcif
    let ifid_pc4   := PCIFRegs.ifid_pc4   pcif

    -- ID/EX registers
    let idex_aluOp     := IDEXLatch.aluOp     idex
    let idex_regWrite  := IDEXLatch.regWrite   idex
    let idex_memRead   := IDEXLatch.memRead    idex
    let idex_memWrite  := IDEXLatch.memWrite   idex
    let idex_memToReg  := IDEXLatch.memToReg   idex
    let idex_branch    := IDEXLatch.branch     idex
    let idex_jump      := IDEXLatch.jump       idex
    let idex_auipc     := IDEXLatch.auipc      idex
    let idex_aluSrcB   := IDEXLatch.aluSrcB    idex
    let idex_isJalr    := IDEXLatch.isJalr     idex
    let idex_isCsr     := IDEXLatch.isCsr      idex
    let idex_isEcall   := IDEXLatch.isEcall    idex
    let idex_isMret    := IDEXLatch.isMret     idex
    let idex_rs1Val    := IDEXLatch.rs1Val     idex
    let idex_rs2Val    := IDEXLatch.rs2Val     idex
    let idex_imm       := IDEXLatch.imm        idex
    let idex_rd        := IDEXLatch.rd         idex
    let idex_rs1Idx    := IDEXLatch.rs1Idx     idex
    let idex_rs2Idx    := IDEXLatch.rs2Idx     idex
    let idex_funct3    := IDEXLatch.funct3     idex
    let idex_pc        := IDEXLatch.pc         idex
    let idex_pc4       := IDEXLatch.pc4        idex
    let idex_csrAddr   := IDEXLatch.csrAddr    idex
    let idex_csrFunct3 := IDEXLatch.csrFunct3  idex

    -- EX/MEM registers
    let exmem_alu      := EXMEMLatch.alu       exmem
    let exmem_rd       := EXMEMLatch.rd        exmem
    let exmem_regW     := EXMEMLatch.regW      exmem
    let exmem_memR     := EXMEMLatch.memR      exmem
    let exmem_memW     := EXMEMLatch.memW      exmem
    let exmem_m2r      := EXMEMLatch.m2r       exmem
    let exmem_rs2Val   := EXMEMLatch.rs2Val    exmem
    let exmem_funct3   := EXMEMLatch.funct3    exmem
    let exmem_pc4      := EXMEMLatch.pc4       exmem
    let exmem_jump     := EXMEMLatch.jump      exmem
    let exmem_isCsr    := EXMEMLatch.isCsr     exmem
    let exmem_csrRdata := EXMEMLatch.csrRdata  exmem

    -- MEM/WB registers
    let memwb_aluResult := MEMWBLatch.aluResult memwb
    let memwb_memData   := MEMWBLatch.memData   memwb
    let memwb_rd        := MEMWBLatch.rd        memwb
    let memwb_regW      := MEMWBLatch.regW      memwb
    let memwb_m2r       := MEMWBLatch.m2r       memwb
    let memwb_pc4       := MEMWBLatch.pc4       memwb
    let memwb_jump      := MEMWBLatch.jump      memwb
    let memwb_isCsr     := MEMWBLatch.isCsr     memwb
    let memwb_csrRdata  := MEMWBLatch.csrRdata  memwb

    -- =================================================================
    -- WB Stage (compute first — needed for forwarding into ID/EX)
    -- =================================================================
    let wb_result := Signal.mux memwb_isCsr memwb_csrRdata
                       (Signal.mux memwb_jump memwb_pc4
                       (Signal.mux memwb_m2r memwb_memData
                         memwb_aluResult))
    let wbRdNz := ~~~(memwb_rd === 0#5)
    let wb_addr := memwb_rd
    let wb_data := wb_result
    let wb_en   := memwb_regW &&& wbRdNz

    -- =================================================================
    -- MEM Stage (address = exmem_alu, store data = exmem_rs2Val)
    -- dmem_rdata is driven externally by the memory subsystem
    -- =================================================================
    let mem_rdata := dmem_rdata

    -- =================================================================
    -- EX Stage
    -- Forwarding priority: MEM→EX (exmem) > WB→EX (memwb/wb)
    -- =================================================================
    let exmem_rdNz   := ~~~(exmem_rd === 0#5)
    let exmem_fwd_en := exmem_regW &&& exmem_rdNz

    let fwd_mem_rs1 := exmem_fwd_en &&& (exmem_rd === idex_rs1Idx)
    let fwd_mem_rs2 := exmem_fwd_en &&& (exmem_rd === idex_rs2Idx)
    let fwd_wb_rs1  := wb_en &&& (wb_addr === idex_rs1Idx)
    let fwd_wb_rs2  := wb_en &&& (wb_addr === idex_rs2Idx)

    -- Nested mux gives MEM→EX priority over WB→EX
    let ex_rs1 := Signal.mux fwd_mem_rs1 exmem_alu
                    (Signal.mux fwd_wb_rs1 wb_data idex_rs1Val)
    let ex_rs2 := Signal.mux fwd_mem_rs2 exmem_alu
                    (Signal.mux fwd_wb_rs2 wb_data idex_rs2Val)

    -- ALU
    let alu_a      := Signal.mux idex_auipc idex_pc ex_rs1
    let alu_b      := Signal.mux idex_aluSrcB idex_imm ex_rs2
    let alu_result := aluSignal idex_aluOp alu_a alu_b

    -- Branch resolution
    let branchCond  := branchCompSignal idex_funct3 ex_rs1 ex_rs2
    let branchTaken := idex_branch &&& branchCond
    let brTarget    := idex_pc + idex_imm
    let jalrSum     := ex_rs1 + idex_imm
    let jalrTarget  := jalrSum &&& 0xFFFFFFFE#32
    let jumpTarget  := Signal.mux idex_isJalr jalrTarget brTarget
    let flush       := (branchTaken ||| idex_jump) ||| (trap_taken ||| idex_isMret)
    let flushOrDelay := flush ||| flushDelay

    -- =================================================================
    -- Hazard / Stall (load-use: EX stage has load, ID reads that rd)
    -- =================================================================
    let id_opcode := ifid_inst.map (BitVec.extractLsb' 0 7 ·)
    let id_rd     := ifid_inst.map (BitVec.extractLsb' 7 5 ·)
    let id_funct3 := ifid_inst.map (BitVec.extractLsb' 12 3 ·)
    let id_rs1    := ifid_inst.map (BitVec.extractLsb' 15 5 ·)
    let id_rs2    := ifid_inst.map (BitVec.extractLsb' 20 5 ·)
    let id_funct7 := ifid_inst.map (BitVec.extractLsb' 25 7 ·)
    let id_imm    := immGenSignal ifid_inst id_opcode
    let id_aluOp  := aluControlSignal id_opcode id_funct3 id_funct7

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

    let id_aluSrcB  := ((id_isALUimm ||| id_isLoad) ||| (id_isStore ||| id_isLUI)) |||
                       ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_regWrite := ((id_isALUrr ||| id_isALUimm) ||| (id_isLoad ||| id_isLUI)) |||
                       ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_memRead  := id_isLoad
    let id_memWrite := id_isStore
    let id_memToReg := id_isLoad
    let id_jump     := id_isJAL ||| id_isJALR
    let id_auipc    := id_isAUIPC ||| id_isJAL
    let f3isZero    := id_funct3 === 0#3
    let f3notZero   := ~~~f3isZero
    let id_isCsr    := id_isSystem &&& f3notZero
    let id_isEcall  := id_isSystem &&& f3isZero
    let id_csrAddr  := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let mretField   := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let isMretField := mretField === 0x302#12
    let id_isMret   := id_isSystem &&& isMretField

    let stall := hazardSignal idex_memRead idex_rd id_rs1 id_rs2

    -- =================================================================
    -- Register File (dual-read, single-write via Signal.memory)
    -- =================================================================
    let rf_rs1_addr := Signal.mux stall id_rs1 (imem_rdata.map (BitVec.extractLsb' 15 5 ·))
    let rf_rs2_addr := Signal.mux stall id_rs2 (imem_rdata.map (BitVec.extractLsb' 20 5 ·))
    let rf_rs1_raw  := Signal.memory wb_addr wb_data wb_en rf_rs1_addr
    let rf_rs2_raw  := Signal.memory wb_addr wb_data wb_en rf_rs2_addr

    -- WB→ID bypass for same-cycle write/read
    let wb_fwd_rs1      := wb_en &&& (wb_addr === id_rs1)
    let wb_fwd_rs2      := wb_en &&& (wb_addr === id_rs2)
    let rf_rs1_bypassed := Signal.mux wb_fwd_rs1 wb_data rf_rs1_raw
    let rf_rs2_bypassed := Signal.mux wb_fwd_rs2 wb_data rf_rs2_raw

    -- x0 hardwired to zero
    let id_rs1Val := Signal.mux (id_rs1 === 0#5) (Signal.pure 0#32) rf_rs1_bypassed
    let id_rs2Val := Signal.mux (id_rs2 === 0#5) (Signal.pure 0#32) rf_rs2_bypassed

    -- =================================================================
    -- IF Stage: PC + fetch
    -- =================================================================
    let pcPlus4      := pcReg + 4#32
    let fetchPCIn    := Signal.mux stall fetchPC pcReg
    let fetchPCPlus4 := fetchPC + 4#32

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
    let squash := stall ||| flushOrDelay

    let pcifNext := bundleAll! [
      Signal.register 0#32           pcNext,
      Signal.register 0#32           fetchPCIn,
      Signal.register false          flush,
      Signal.register 0x00000013#32
        (Signal.mux flushOrDelay (Signal.pure nopInst) (Signal.mux stall ifid_inst imem_rdata)),
      Signal.register 0#32           (Signal.mux stall ifid_pc  fetchPC),
      Signal.register 0#32           (Signal.mux stall ifid_pc4 fetchPCPlus4)
    ]

    let idexNext := bundleAll! [
      Signal.register 0#4   (Signal.mux squash (Signal.pure 0#4)   id_aluOp),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_regWrite),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_memRead),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_memWrite),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_memToReg),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_isBranch),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_jump),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_auipc),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_aluSrcB),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_isJALR),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_isCsr),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_isEcall),
      Signal.register false  (Signal.mux squash (Signal.pure false) id_isMret),
      Signal.register 0#32  id_rs1Val,
      Signal.register 0#32  id_rs2Val,
      Signal.register 0#32  id_imm,
      Signal.register 0#5   (Signal.mux squash (Signal.pure 0#5)   id_rd),
      Signal.register 0#5   id_rs1,
      Signal.register 0#5   id_rs2,
      Signal.register 0#3   id_funct3,
      Signal.register 0#32  ifid_pc,
      Signal.register 0#32  ifid_pc4,
      Signal.register 0#12  id_csrAddr,
      Signal.register 0#3   id_funct3
    ]

    -- EX/MEM latch: EX results → MEM stage
    let exmemNext := bundleAll! [
      Signal.register 0#32  alu_result,
      Signal.register 0#5   idex_rd,
      Signal.register false  idex_regWrite,
      Signal.register false  idex_memRead,
      Signal.register false  idex_memWrite,
      Signal.register false  idex_memToReg,
      Signal.register 0#32  ex_rs2,       -- forwarded store data
      Signal.register 0#3   idex_funct3,  -- load/store width
      Signal.register 0#32  idex_pc4,
      Signal.register false  idex_jump,
      Signal.register false  idex_isCsr,
      Signal.register 0#32  csr_rdata
    ]

    -- MEM/WB latch: MEM results → WB stage
    let memwbNext := bundleAll! [
      Signal.register 0#32  exmem_alu,      -- pass-through ALU result
      Signal.register 0#32  mem_rdata,      -- loaded data from dmem
      Signal.register 0#5   exmem_rd,
      Signal.register false  exmem_regW,
      Signal.register false  exmem_m2r,
      Signal.register 0#32  exmem_pc4,
      Signal.register false  exmem_jump,
      Signal.register false  exmem_isCsr,
      Signal.register 0#32  exmem_csrRdata
    ]

    bundleAll! [pcifNext, idexNext, exmemNext, memwbNext]

  -- Output: debug_pc = pcReg
  PCIFRegs.pcReg (Signal.fst pipeline)

#synthesizeVerilog rv32iCore

theorem latency_is_5 :
  ∀ (t : Nat),
  --let a:=
  sorry

end Sparkle.IP.RV32
