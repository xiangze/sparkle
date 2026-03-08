#!/usr/bin/env python3
"""
chisel2sparkle.py — Chisel (Scala) → Sparkle (Lean 4) Signal DSL 変換スクリプト

変換対応表に基づき、Chisel HDL のソースコードを Sparkle Signal DSL の
Lean 4 コードに変換するパターンベースのトランスパイラ。

使い方:
    python chisel2sparkle.py input.scala              # → input.lean
    python chisel2sparkle.py input.scala -o out.lean   # → out.lean
    python chisel2sparkle.py input.scala --dry-run     # 変換結果を標準出力のみ
    python chisel2sparkle.py input.scala --verbose      # 変換ログ付き

対応パターン (変換対応表):
  ┌──────────────────────────────────────────┬──────────────────────────────────────────────┐
  │ Chisel (Scala)                           │ Sparkle (Lean 4)                             │
  ├──────────────────────────────────────────┼──────────────────────────────────────────────┤
  │ class Foo extends Module                 │ def foo {dom : DomainConfig} ... : Signal .. │
  │ val io = IO(new Bundle { ... })          │ 関数引数 + 戻り値型                          │
  │ val reg = RegInit(0.U(8.W))             │ Signal.register (0#8) input                  │
  │ val reg = RegInit(0.S(8.W))             │ Signal.register (0 : BitVec 8) input         │
  │ RegNext(signal, init)                    │ Signal.register init signal                  │
  │ when(cond) { a := b } .otherwise { ... } │ Signal.mux cond b <else>                    │
  │ switch(state) { is(s0) {...} ... }       │ nested Signal.mux / hw_cond                  │
  │ Wire(UInt(8.W))                          │ let binding                                  │
  │ Vec(n, UInt(8.W))                        │ HWVector (BitVec 8) n / List                 │
  │ io.out := expr                           │ pure functional return                       │
  │ Seq.fill(n)(Module(new Sub))             │ List.range n |>.map (fun _ => sub ...)       │
  │ Cat(a, b)                                │ BitVec.append a b                            │
  │ a +& b                                   │ zeroExtend + add                             │
  │ ShiftRegister(x, n)                      │ delayN n init x                              │
  │ SyncReadMem(size, type)                  │ Signal.memory                                │
  │ Module(new Queue(type, depth))           │ delayN depth / SyncFIFO                      │
  │ .reduce(_ + _)                           │ .foldl (fun acc s => (+) <$> acc <*> s) zero │
  │ Enum(n)                                  │ BitVec encoding: 0#w, 1#w, ...               │
  │ (new ChiselStage).emitVerilog(...)       │ #synthesizeVerilog                            │
  └──────────────────────────────────────────┴──────────────────────────────────────────────┘

制限事項:
  - 完全な Scala パーサではなく、パターンベースの変換です
  - 複雑な Scala 式 (高階関数の連鎖等) は手動修正が必要な場合があります
  - 変換後のコードは Sparkle プロジェクトへの統合前にレビューを推奨します
  - /* MANUAL */ コメントで手動確認が必要な箇所をマークします
"""

import re
import sys
import argparse
import dataclasses
from dataclasses import dataclass, field
from typing import Optional
from enum import Enum, auto


# ============================================================
# 1. データ構造
# ============================================================

class PortDir(Enum):
    INPUT = auto()
    OUTPUT = auto()

@dataclass
class Port:
    """Chisel IO ポート"""
    name: str
    direction: PortDir
    typ: str          # "UInt(8.W)", "SInt(20.W)", "Bool()", "Vec(3, UInt(8.W))"
    width: int = 0    # ビット幅 (推定)
    is_signed: bool = False
    is_vec: bool = False
    vec_size: int = 0

@dataclass
class Register:
    """Chisel レジスタ"""
    name: str
    init_val: str     # "0.U(8.W)", "0.S", "false.B"
    width: int = 0
    is_signed: bool = False

@dataclass
class WhenBlock:
    """when/elsewhen/otherwise ブロック"""
    condition: str
    assignments: list  # [(target, expr), ...]

@dataclass
class ModuleInfo:
    """パース済み Chisel モジュール情報"""
    name: str
    ports: list = field(default_factory=list)
    registers: list = field(default_factory=list)
    wires: list = field(default_factory=list)
    when_blocks: list = field(default_factory=list)
    assignments: list = field(default_factory=list)   # 無条件代入
    submodules: list = field(default_factory=list)
    params: dict = field(default_factory=dict)
    raw_lines: list = field(default_factory=list)
    object_constants: dict = field(default_factory=dict)


# ============================================================
# 2. Chisel パーサ
# ============================================================

class ChiselParser:
    """Chisel ソースからモジュール構造を抽出するパーサ"""

    # --- 正規表現パターン ---

    # object Foo { val X = 8 }
    RE_OBJECT_VAL = re.compile(
        r'val\s+(\w+)\s*=\s*(.+?)(?:\s*//.*)?$'
    )

    # class Foo(val K: Int = 3) extends Module
    RE_MODULE_DEF = re.compile(
        r'class\s+(\w+)(?:\(([^)]*)\))?\s+extends\s+Module'
    )

    # val port = Input(UInt(8.W)) / Output(SInt(20.W)) / Input(Bool())
    RE_PORT = re.compile(
        r'val\s+(\w+)\s*=\s*(Input|Output)\s*\(\s*(.+?)\s*\)\s*$'
    )

    # val port = Input(Vec(K, UInt(8.W))) / Output(Vec(K, SInt(20.W)))
    RE_PORT_VEC = re.compile(
        r'val\s+(\w+)\s*=\s*(Input|Output)\s*\(\s*Vec\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)\s*\)'
    )

    # val reg = RegInit(0.U(8.W)) / RegInit(0.S(20.W)) / RegInit(false.B)
    RE_REGINIT = re.compile(
        r'val\s+(\w+)\s*=\s*RegInit\s*\(\s*(.+?)\s*\)'
    )

    # RegNext(signal, 0.S)
    RE_REGNEXT = re.compile(
        r'RegNext\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)'
    )

    # ShiftRegister(signal, n)
    RE_SHIFTREG = re.compile(
        r'ShiftRegister\s*\(\s*(.+?)\s*,\s*(\w+)\s*\)'
    )

    # when(cond) {
    RE_WHEN = re.compile(r'when\s*\(\s*(.+?)\s*\)\s*\{')

    # } .elsewhen(cond) {
    RE_ELSEWHEN = re.compile(r'\}\s*\.?\s*elsewhen\s*\(\s*(.+?)\s*\)\s*\{')

    # } .otherwise {
    RE_OTHERWISE = re.compile(r'\}\s*\.?\s*otherwise\s*\{')

    # target := expr
    RE_ASSIGN = re.compile(r'(\S+)\s*:=\s*(.+?)(?:\s*//.*)?$')

    # Wire(UInt(8.W))
    RE_WIRE = re.compile(r'val\s+(\w+)\s*=\s*Wire\s*\(\s*(.+?)\s*\)')

    # Seq.fill(n)(Module(new Sub))
    RE_SEQ_FILL_MODULE = re.compile(
        r'val\s+(\w+)\s*=\s*Seq\.fill\s*\((.+?)\)\s*\(\s*Module\s*\(\s*new\s+(\w+)(?:\(([^)]*)\))?\s*\)\s*\)'
    )

    # Seq.fill(K, K)(Module(new Sub))
    RE_SEQ_FILL_2D = re.compile(
        r'val\s+(\w+)\s*=\s*Seq\.fill\s*\((.+?)\s*,\s*(.+?)\)\s*\(\s*Module\s*\(\s*new\s+(\w+)(?:\(([^)]*)\))?\s*\)\s*\)'
    )

    # Module(new Queue(type, depth))
    RE_QUEUE = re.compile(
        r'val\s+(\w+)\s*=\s*(?:Seq\.fill\s*\((.+?)\)\s*\()?\s*Module\s*\(\s*new\s+Queue\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)\s*\)'
    )

    # .reduce(_ + _)
    RE_REDUCE = re.compile(r'\.reduce\s*\(\s*_\s*(\+|\*|\||\&)\s*_\s*\)')

    # val x = io.foo (wire alias)
    RE_WIRE_ALIAS = re.compile(r'val\s+(\w+)\s*=\s*(io\.\w+)')

    # Cat(a, b)
    RE_CAT = re.compile(r'Cat\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)')

    # for (r <- 0 until K)
    RE_FOR = re.compile(r'for\s*\(\s*(\w+)\s*<-\s*(\d+)\s+until\s+(\w+)\s*\)')

    def __init__(self, verbose=False):
        self.verbose = verbose
        self.modules: list[ModuleInfo] = []
        self.objects: dict[str, dict] = {}  # object名 → {変数名: 値}

    def log(self, msg):
        if self.verbose:
            print(f"  [PARSE] {msg}", file=sys.stderr)

    def parse(self, source: str) -> list[ModuleInfo]:
        """Chisel ソースコード全体をパース"""
        lines = source.split('\n')
        self._parse_objects(lines)
        self._parse_modules(lines)
        return self.modules

    def _parse_objects(self, lines: list[str]):
        """object 定義内の定数を収集"""
        in_object = None
        brace_depth = 0
        for line in lines:
            stripped = line.strip()

            if stripped.startswith('object ') and '{' in stripped:
                # 'extends App' はエントリポイントなのでスキップ
                if 'extends App' in stripped:
                    continue
                name = stripped.split('object ')[1].split('{')[0].strip().split('(')[0].strip()
                in_object = name
                self.objects[name] = {}
                brace_depth = stripped.count('{') - stripped.count('}')
                continue

            if in_object:
                brace_depth += stripped.count('{') - stripped.count('}')
                m = self.RE_OBJECT_VAL.search(stripped)
                if m:
                    var_name, var_val = m.group(1), m.group(2).strip()
                    # 'def apply' パターンはスキップ
                    if 'def ' in stripped:
                        pass
                    else:
                        self.objects[in_object][var_name] = var_val
                        self.log(f"Object {in_object}.{var_name} = {var_val}")
                if brace_depth <= 0:
                    in_object = None

    def _parse_modules(self, lines: list[str]):
        """class ... extends Module をパース"""
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            m = self.RE_MODULE_DEF.search(line)
            if m:
                mod = ModuleInfo(name=m.group(1))
                # パラメータ
                if m.group(2):
                    for param in m.group(2).split(','):
                        param = param.strip()
                        if '=' in param:
                            parts = param.split('=')
                            pname = parts[0].strip().split()[-1]
                            pval = parts[1].strip()
                            mod.params[pname] = pval
                self.log(f"Module: {mod.name} params={mod.params}")
                # モジュール本体をパース
                i = self._parse_module_body(lines, i, mod)
                self.modules.append(mod)
            i += 1

    def _parse_module_body(self, lines, start_idx, mod: ModuleInfo) -> int:
        """モジュール本体 (中括弧の中身) をパース"""
        brace_depth = 0
        in_io_bundle = False
        io_brace_depth = 0
        i = start_idx

        # 開始行の中括弧
        brace_depth += lines[i].count('{') - lines[i].count('}')

        i += 1
        while i < len(lines) and brace_depth > 0:
            line = lines[i].strip()
            raw_line = lines[i]
            mod.raw_lines.append(raw_line)

            brace_depth += line.count('{') - line.count('}')

            # IO Bundle 検出
            if 'IO(new Bundle' in line:
                in_io_bundle = True
                io_brace_depth = brace_depth

            if in_io_bundle:
                # Vec ポート
                m = self.RE_PORT_VEC.search(line)
                if m:
                    port = Port(
                        name=m.group(1),
                        direction=PortDir.INPUT if m.group(2) == 'Input' else PortDir.OUTPUT,
                        typ=f"Vec({m.group(3)}, {m.group(4)})",
                        is_vec=True
                    )
                    self._infer_vec_port(port, m.group(3), m.group(4))
                    mod.ports.append(port)
                    self.log(f"  Port(Vec): {port}")
                else:
                    # 通常ポート
                    m = self.RE_PORT.search(line)
                    if m:
                        port = Port(
                            name=m.group(1),
                            direction=PortDir.INPUT if m.group(2) == 'Input' else PortDir.OUTPUT,
                            typ=m.group(3)
                        )
                        self._infer_port_width(port)
                        mod.ports.append(port)
                        self.log(f"  Port: {port}")

                if brace_depth < io_brace_depth:
                    in_io_bundle = False

            # RegInit
            m = self.RE_REGINIT.search(line)
            if m and not in_io_bundle:
                reg = Register(name=m.group(1), init_val=m.group(2))
                self._infer_reg_width(reg)
                mod.registers.append(reg)
                self.log(f"  Reg: {reg}")

            # Wire
            m = self.RE_WIRE.search(line)
            if m and not in_io_bundle:
                mod.wires.append((m.group(1), m.group(2)))
                self.log(f"  Wire: {m.group(1)} : {m.group(2)}")

            # Submodule (Seq.fill 2D)
            m = self.RE_SEQ_FILL_2D.search(line)
            if m:
                mod.submodules.append({
                    'name': m.group(1), 'type': m.group(4),
                    'dim': '2d', 'size1': m.group(2), 'size2': m.group(3),
                    'params': m.group(5)
                })
                self.log(f"  SubModule(2D): {m.group(1)}")
            else:
                m = self.RE_SEQ_FILL_MODULE.search(line)
                if m:
                    mod.submodules.append({
                        'name': m.group(1), 'type': m.group(3),
                        'dim': '1d', 'size': m.group(2),
                        'params': m.group(4)
                    })
                    self.log(f"  SubModule(1D): {m.group(1)}")

            # Queue
            m = self.RE_QUEUE.search(line)
            if m:
                mod.submodules.append({
                    'name': m.group(1), 'type': 'Queue',
                    'count': m.group(2), 'data_type': m.group(3),
                    'depth': m.group(4)
                })
                self.log(f"  Queue: {m.group(1)}")

            # 代入 (target := expr)
            m = self.RE_ASSIGN.search(line)
            if m:
                mod.assignments.append((m.group(1), m.group(2).strip()))

            i += 1
        return i

    def _infer_port_width(self, port: Port):
        """ポートのビット幅を推定"""
        typ = port.typ.strip().rstrip(')')
        if typ in ('Bool()', 'Bool(', 'Bool'):
            port.width = 1
            port.is_signed = False
        elif 'UInt' in typ:
            m = re.search(r'(\d+)\.W', typ)
            if m:
                port.width = int(m.group(1))
            port.is_signed = False
        elif 'SInt' in typ:
            m = re.search(r'(\d+)\.W', typ)
            if m:
                port.width = int(m.group(1))
            port.is_signed = True
        # DataType(w) → SInt(w.W) (SDIP 固有)
        elif 'DataType' in typ:
            m = re.search(r'DataType\s*\(\s*([^)]+)', typ)
            if m:
                port.is_signed = True
                val = m.group(1).strip()
                port.width = self._resolve_const(val)

    def _infer_vec_port(self, port: Port, size_str: str, elem_str: str):
        """Vec ポートの情報を推定"""
        port.vec_size = self._resolve_const(size_str.strip())
        # 内部型
        inner = Port(name="", direction=port.direction, typ=elem_str.strip())
        self._infer_port_width(inner)
        port.width = inner.width
        port.is_signed = inner.is_signed

    def _infer_reg_width(self, reg: Register):
        """レジスタのビット幅を推定"""
        init = reg.init_val.strip().rstrip(')')
        if 'false.B' in init or 'true.B' in init:
            reg.width = 1
            reg.is_signed = False
        elif '.U(' in init:
            m = re.search(r'(\d+)\.W', init)
            if m:
                reg.width = int(m.group(1))
            reg.is_signed = False
        elif '.S(' in init:
            m = re.search(r'(\w[\w.]+)\.W', init)
            if m:
                reg.width = self._resolve_const(m.group(1))
            reg.is_signed = True

    def _resolve_const(self, val: str) -> int:
        """定数名を解決 (簡易版)"""
        val = val.strip()
        try:
            return int(val)
        except ValueError:
            pass

        # Dotted reference: DATA.W → objects["DATA"]["W"]
        if '.' in val:
            parts = val.split('.')
            if parts[0] in self.objects and parts[1] in self.objects[parts[0]]:
                return self._resolve_const(self.objects[parts[0]][parts[1]])

        # Flat reference within any object
        for obj_name, obj_vals in self.objects.items():
            if val in obj_vals:
                return self._resolve_const(obj_vals[val])

        # 式の評価を試みる (object 定数を解決済みの値に置換)
        try:
            expr = val
            for obj_name, obj_vals in self.objects.items():
                for vname, vval in obj_vals.items():
                    expr = expr.replace(f'{obj_name}.{vname}', str(self._resolve_const(vval)))
            return int(eval(expr, {"__builtins__": {}}, {}))
        except Exception:
            return 0


# ============================================================
# 3. Sparkle コード生成器
# ============================================================

class SparkleGenerator:
    """パース済み Chisel モジュール情報から Sparkle Lean 4 コードを生成"""

    def __init__(self, parser: ChiselParser, verbose=False):
        self.parser = parser
        self.verbose = verbose
        self.indent = 0
        self.output_lines: list[str] = []
        self.warnings: list[str] = []

    def log(self, msg):
        if self.verbose:
            print(f"  [GEN] {msg}", file=sys.stderr)

    def warn(self, msg):
        self.warnings.append(msg)
        if self.verbose:
            print(f"  [WARN] {msg}", file=sys.stderr)

    def emit(self, line=""):
        prefix = "  " * self.indent
        self.output_lines.append(f"{prefix}{line}")

    def generate(self, modules: list[ModuleInfo]) -> str:
        """全モジュールから Sparkle コードを生成"""
        self._emit_header()
        self._emit_imports()
        self._emit_object_constants()

        for mod in modules:
            self.emit()
            self._generate_module(mod)

        self._emit_footer()
        return '\n'.join(self.output_lines)

    # --- ヘッダ / フッタ ---

    def _emit_header(self):
        self.emit("/-")
        self.emit("  Auto-generated by chisel2sparkle.py")
        self.emit("  Chisel → Sparkle Signal DSL 変換")
        self.emit("")
        self.emit("  変換対応表:")
        self.emit("    RegInit(x)          → Signal.register x input")
        self.emit("    RegNext(sig, init)   → Signal.register init sig")
        self.emit("    when(c) { a := b }   → Signal.mux c b <else>")
        self.emit("    Module(new Sub)      → sub args")
        self.emit("    io.out := expr       → pure functional return")
        self.emit("    .reduce(_ + _)       → .foldl (fun a b => (+) <$> a <*> b) zero")
        self.emit("-/")
        self.emit()

    def _emit_imports(self):
        self.emit("import Sparkle")
        self.emit("import Sparkle.Core.Signal")
        self.emit("import Sparkle.Core.Domain")
        self.emit()
        self.emit("open Sparkle.Core.Signal")
        self.emit("open Sparkle.Core.Domain")
        self.emit()

    def _emit_object_constants(self):
        """object 定数 → namespace + def"""
        # 定数を持つ object のみ出力 (空のものやファクトリはスキップ)
        const_objects = {k: v for k, v in self.parser.objects.items() if v}
        if not const_objects:
            return

        self.emit("-- ============================================================")
        self.emit("-- パラメータ定義 (自動変換: object → namespace/def)")
        self.emit("-- ============================================================")

        for obj_name, vals in const_objects.items():
            self.emit()
            self.emit(f"namespace {obj_name}")
            for var_name, var_val in vals.items():
                lean_val = self._convert_const_expr(var_val)
                self.emit(f"def {var_name} : Nat := {lean_val}")
            self.emit(f"end {obj_name}")

        self.emit()

    def _emit_footer(self):
        self.emit()
        self.emit("-- ============================================================")
        self.emit("-- 変換レポート")
        self.emit("-- ============================================================")
        if self.warnings:
            self.emit("/-!")
            self.emit("## 手動確認が必要な箇所")
            self.emit()
            for i, w in enumerate(self.warnings, 1):
                self.emit(f"{i}. {w}")
            self.emit("-/")
        else:
            self.emit("-- 全てのパターンが自動変換されました")

    # --- モジュール変換 ---

    def _generate_module(self, mod: ModuleInfo):
        self.emit("-- ============================================================")
        self.emit(f"-- {mod.name} (自動変換: class → def)")
        self.emit("-- ============================================================")
        self.emit()

        # 出力ポートが複数 → structure 定義
        out_ports = [p for p in mod.ports if p.direction == PortDir.OUTPUT]
        if len(out_ports) > 1:
            self._emit_output_structure(mod.name, out_ports)

        # 関数シグネチャ
        self._emit_function_signature(mod, out_ports)

        # 関数本体
        self.indent += 1
        self._emit_registers(mod)
        self._emit_submodules(mod)
        self._emit_assignments(mod)
        self._emit_return(mod, out_ports)
        self.indent -= 1
        self.emit()

    def _emit_output_structure(self, mod_name: str, out_ports: list[Port]):
        """複数出力 → Sparkle structure"""
        struct_name = f"{mod_name}Output"
        self.emit(f"structure {struct_name} where")
        self.indent += 1
        for p in out_ports:
            lean_type = self._chisel_type_to_lean(p)
            self.emit(f"{self._to_camel(p.name)} : {lean_type}")
        self.indent -= 1
        self.emit("deriving Inhabited")
        self.emit()

    def _emit_function_signature(self, mod: ModuleInfo, out_ports: list[Port]):
        """Chisel class → Sparkle def のシグネチャ"""
        func_name = self._to_camel(mod.name)
        in_ports = [p for p in mod.ports if p.direction == PortDir.INPUT]

        # 戻り値型
        if len(out_ports) == 0:
            ret_type = "Unit"
        elif len(out_ports) == 1:
            ret_type = self._chisel_type_to_lean(out_ports[0])
        else:
            ret_type = f"{mod.name}Output"

        # パラメータ部分
        params_str = ""
        if mod.params:
            param_parts = []
            for pname, pval in mod.params.items():
                param_parts.append(f"({pname} : Nat := {pval})")
            params_str = " ".join(param_parts)

        self.emit(f"/-- {mod.name}: Chisel Module からの自動変換 -/")
        sig_line = f"def {func_name} {{dom : DomainConfig}}"
        if params_str:
            sig_line += f" {params_str}"
        self.emit(sig_line)

        # 入力ポート → 関数引数
        self.indent += 1
        for p in in_ports:
            lean_type = self._chisel_type_to_lean_signal(p)
            self.emit(f"({self._to_camel(p.name)} : {lean_type})")
        self.emit(f": Signal dom {ret_type} :=")
        self.indent -= 1
        self.emit()

    def _emit_registers(self, mod: ModuleInfo):
        """レジスタ → Signal.register / Signal.loop"""
        if not mod.registers:
            return

        self.emit("-- レジスタ (自動変換: RegInit → Signal.register / Signal.loop)")

        for reg in mod.registers:
            # when ブロックで条件付き更新されるレジスタを探す
            conditional_update = self._find_conditional_update(mod, reg.name)
            unconditional_update = self._find_unconditional_update(mod, reg.name)

            init_val = self._convert_init_value(reg)
            lean_type = self._reg_lean_type(reg)

            if conditional_update and unconditional_update is None:
                # when(cond) { reg := val } → Signal.loop + Signal.mux
                cond, new_val = conditional_update
                cond_lean = self._convert_expr(cond)
                val_lean = self._convert_expr(new_val)
                self.emit(f"let {self._to_camel(reg.name)} := Signal.loop fun prev =>")
                self.indent += 1
                self.emit(f"let next := Signal.mux {cond_lean} {val_lean} prev")
                self.emit(f"Signal.register ({init_val} : {lean_type}) next")
                self.indent -= 1
            elif unconditional_update:
                # reg := expr → Signal.register init expr
                expr_lean = self._convert_expr(unconditional_update)
                self.emit(f"let {self._to_camel(reg.name)} := Signal.register ({init_val} : {lean_type}) {expr_lean}")
            else:
                # 更新元不明 → プレースホルダ
                self.emit(f"let {self._to_camel(reg.name)} := Signal.register ({init_val} : {lean_type}) (Signal.pure ({init_val} : {lean_type}))")
                self.warn(f"{mod.name}.{reg.name}: レジスタの更新元が検出できませんでした")

        self.emit()

    def _emit_submodules(self, mod: ModuleInfo):
        """サブモジュール → 関数呼び出し"""
        if not mod.submodules:
            return

        self.emit("-- サブモジュール (自動変換: Module(new Sub) → sub args)")

        for sub in mod.submodules:
            if sub['type'] == 'Queue':
                # Queue → delayN (ラインバッファ近似)
                depth = sub.get('depth', '0')
                count = sub.get('count', None)
                name = sub['name']
                if count:
                    self.emit(f"-- {name}: Chisel Queue×{count} → register chain (depth={depth})")
                    self.emit(f"-- /* MANUAL */ Queue の FIFO 動作が必要な場合は SyncFIFO IP を使用してください")
                    self.warn(f"{name}: Queue → delayN 近似。FIFO 動作が必要なら SyncFIFO を使用")
                else:
                    self.emit(f"-- {name}: Chisel Queue → register chain (depth={depth})")
            else:
                sub_func = self._to_camel(sub['type'])
                self.emit(f"-- {sub['name']}: Chisel Module(new {sub['type']}) → {sub_func} ...")
                if sub.get('dim') == '2d':
                    self.emit(f"-- /* MANUAL */ 2D 配列 Seq.fill({sub['size1']},{sub['size2']}) → foldl の入れ子で接続")
                    self.warn(f"{sub['name']}: 2D サブモジュール配列は foldl の入れ子で手動変換してください")

        self.emit()

    def _emit_assignments(self, mod: ModuleInfo):
        """無条件代入 → let 束縛 / 組合せ論理"""
        # レジスタ代入以外の assign をまとめて出力
        reg_names = {r.name for r in mod.registers}
        combo_assigns = [(t, e) for t, e in mod.assignments
                         if not any(t.endswith(rn) for rn in reg_names)
                         and ':=' not in e]

        if combo_assigns:
            self.emit("-- 組合せ論理 (自動変換: io.x := expr → let x := expr)")
            for target, expr in combo_assigns:
                lean_target = self._convert_target(target)
                lean_expr = self._convert_expr(expr)
                if lean_target and lean_expr:
                    self.emit(f"let {lean_target} := {lean_expr}")
            self.emit()

    def _emit_return(self, mod: ModuleInfo, out_ports: list[Port]):
        """出力ポートの組み立て → return"""
        if len(out_ports) == 0:
            self.emit("Signal.pure ()")
        elif len(out_ports) == 1:
            p = out_ports[0]
            target = f"io.{p.name}"
            expr = self._find_output_expr(mod, target)
            if expr:
                self.emit(f"-- 出力: io.{p.name} := {expr}")
                self.emit(f"{self._convert_expr(expr)}")
            else:
                self.emit(f"-- /* MANUAL */ 出力 io.{p.name} の接続を確認してください")
                self.emit(f"Signal.pure (0 : {self._chisel_type_to_lean(p)})")
                self.warn(f"{mod.name}: 出力 {p.name} の式が検出できませんでした")
        else:
            # 複数出力 → structure constructor via <$> <*>
            self.emit("-- 出力の組み立て")
            field_names = [self._to_camel(p.name) for p in out_ports]
            # 最初の引数
            lambda_args = " ".join(field_names)
            struct_name = f"{mod.name}Output"
            fields = ", ".join(f"{fn} := {fn}" for fn in field_names)
            self.emit(f"(fun {lambda_args} => {{ {fields} : {struct_name} }})")
            self.indent += 1
            for i, p in enumerate(out_ports):
                op = "<$>" if i == 0 else "<*>"
                target = f"io.{p.name}"
                expr = self._find_output_expr(mod, target)
                expr_lean = self._convert_expr(expr) if expr else f"Signal.pure (0 : {self._chisel_type_to_lean(p)})"
                self.emit(f"{op} {expr_lean}")
            self.indent -= 1

    # --- ヘルパー ---

    def _find_conditional_update(self, mod: ModuleInfo, reg_name: str):
        """when ブロック内の条件付き代入を探す"""
        for target, expr in mod.assignments:
            # 直前の when 条件を探す (簡易版)
            pass
        # raw_lines をスキャンして when { reg := val } パターンを探す
        lines = mod.raw_lines
        for i, line in enumerate(lines):
            m = self.RE_WHEN.search(line.strip()) if hasattr(self, 'RE_WHEN') else None
            m = ChiselParser.RE_WHEN.search(line.strip())
            if m:
                cond = m.group(1)
                # 次の数行で reg_name := val を探す
                for j in range(i+1, min(i+10, len(lines))):
                    assign_m = ChiselParser.RE_ASSIGN.search(lines[j].strip())
                    if assign_m and assign_m.group(1).strip() == reg_name:
                        return (cond, assign_m.group(2).strip())
                    if '}' in lines[j]:
                        break
        return None

    def _find_unconditional_update(self, mod: ModuleInfo, reg_name: str):
        """when ブロック外の無条件代入を探す"""
        # raw_lines を走査。when ブロック外で reg_name := expr を見つける
        in_when = 0
        for line in mod.raw_lines:
            stripped = line.strip()
            if ChiselParser.RE_WHEN.search(stripped):
                in_when += 1
            if ChiselParser.RE_OTHERWISE.search(stripped):
                pass  # still in when block
            if in_when > 0 and '}' in stripped:
                close_count = stripped.count('}')
                in_when = max(0, in_when - close_count)

            if in_when == 0:
                m = ChiselParser.RE_ASSIGN.search(stripped)
                if m and m.group(1).strip() == reg_name:
                    return m.group(2).strip()
        return None

    def _find_output_expr(self, mod: ModuleInfo, target: str):
        """出力ポートの代入式を探す"""
        for t, e in mod.assignments:
            if t.strip() == target:
                return e
        return None

    def _convert_expr(self, expr: str) -> str:
        """Chisel 式 → Sparkle 式"""
        if expr is None:
            return "sorry -- /* MANUAL */"

        s = expr.strip()

        # 数値リテラル
        s = re.sub(r'(\d+)\.U\((\d+)\.W\)', r'(\1#\2)', s)    # 0.U(8.W) → (0#8)
        s = re.sub(r'(\d+)\.S\((\d+)\.W\)', r'((\1) : BitVec \2)', s)  # 0.S(20.W) → (0 : BitVec 20)
        s = re.sub(r'(\d+)\.U', r'\1', s)                       # 0.U → 0
        s = re.sub(r'(\d+)\.S', r'(\1 : BitVec _)', s)          # 0.S → (0 : BitVec _)
        s = re.sub(r'false\.B', 'false', s)
        s = re.sub(r'true\.B', 'true', s)

        # io.prefix 除去
        s = re.sub(r'io\.(\w+)', lambda m: self._to_camel(m.group(1)), s)

        # 演算子
        s = s.replace(':=', ':=')  # keep (shouldn't appear in expr)

        # RegNext(signal, init)
        m = ChiselParser.RE_REGNEXT.search(s)
        if m:
            sig = self._convert_expr(m.group(1))
            init = self._convert_expr(m.group(2))
            s = ChiselParser.RE_REGNEXT.sub(f'Signal.register {init} {sig}', s)

        # ShiftRegister(signal, n)
        m = ChiselParser.RE_SHIFTREG.search(s)
        if m:
            sig = self._convert_expr(m.group(1))
            n = m.group(2)
            s = ChiselParser.RE_SHIFTREG.sub(f'delayN {n} {sig}', s)

        # Cat(a, b) → BitVec.append a b
        m = ChiselParser.RE_CAT.search(s)
        if m:
            a = self._convert_expr(m.group(1))
            b = self._convert_expr(m.group(2))
            s = ChiselParser.RE_CAT.sub(f'BitVec.append {a} {b}', s)

        # .reduce(_ + _) → .foldl ...
        m = ChiselParser.RE_REDUCE.search(s)
        if m:
            op = m.group(1)
            prefix = s[:m.start()]
            s = f"{prefix}.foldl (fun acc x => (· {op} ·) <$> acc <*> x) (Signal.pure 0)"

        # 乗算: a * b → (· * ·) <$> a <*> b (Signal context)
        if ' * ' in s and '<$>' not in s and 'Signal' not in s:
            parts = s.split(' * ', 1)
            if len(parts) == 2:
                a, b = parts[0].strip(), parts[1].strip()
                # 単純な変数同士の乗算のみ変換
                if re.match(r'^[\w.()]+$', a) and re.match(r'^[\w.()]+$', b):
                    s = f"(· * ·) <$> {a} <*> {b}"

        # 加算: a + b → (· + ·) <$> a <*> b (Signal context で括弧つき)
        if ' + ' in s and '<$>' not in s and 'Signal' not in s and 'foldl' not in s:
            parts = s.split(' + ', 1)
            if len(parts) == 2:
                a, b = parts[0].strip(), parts[1].strip()
                if re.match(r'^[\w.()]+$', a) and re.match(r'^[\w.()]+$', b):
                    s = f"(· + ·) <$> {a} <*> {b}"

        # 変数名をキャメルケースに
        # (ただし Lean 予約語や Signal.xxx は変換しない)
        s = re.sub(r'(?<![.\w])(\w+_\w+)(?!\w*\.)', lambda m: self._to_camel(m.group(1)), s)

        return s

    def _convert_target(self, target: str) -> str:
        """代入先を Lean let 名に変換"""
        t = target.strip()
        t = re.sub(r'^io\.', '', t)
        return self._to_camel(t)

    def _convert_init_value(self, reg: Register) -> str:
        """RegInit の初期値 → Lean"""
        init = reg.init_val.strip().rstrip(')')
        if 'false.B' in init:
            return "false"
        if 'true.B' in init:
            return "true"
        # 0.U(8.W) or 0.S(8.W)
        m = re.match(r'(\d+)\.[US]\((\d+)\.W', init)
        if m:
            val, width = m.group(1), m.group(2)
            return f"{val} : BitVec {width}"
        # 0.S(DATA.W.W) → resolve DATA.W
        m = re.match(r'(\d+)\.[US]\((\w[\w.]+)\.W', init)
        if m:
            val = m.group(1)
            width_ref = m.group(2)
            width = self.parser._resolve_const(width_ref)
            if width > 0:
                return f"{val} : BitVec {width}"
            return f"{val} : BitVec {width_ref}"
        # bare 0.U / 0.S
        m = re.match(r'(\d+)\.[US]', init)
        if m:
            return m.group(1)
        return init

    def _convert_const_expr(self, val: str) -> str:
        """object 定数値 → Lean"""
        s = val.strip()
        # DATA.W → DATA.W (そのまま namespace 参照)
        s = re.sub(r'(\d+)\.W', r'\1', s)
        s = s.replace('//', '--')
        return s

    def _chisel_type_to_lean(self, port: Port) -> str:
        """Chisel 型 → Lean 型 (非 Signal)"""
        if port.width == 1 and not port.is_signed and ('Bool' in port.typ or port.typ.strip().rstrip(')') in ('Bool(', 'Bool')):
            return "Bool"
        if port.is_vec:
            inner = f"BitVec {port.width}" if port.width > 0 else "BitVec DATA.W"
            return f"List ({inner})"
        if port.width > 0:
            return f"BitVec {port.width}"
        return "BitVec DATA.W"

    def _chisel_type_to_lean_signal(self, port: Port) -> str:
        """Chisel 型 → Signal dom (Lean 型)"""
        if port.width == 1 and not port.is_signed and ('Bool' in port.typ or port.typ.strip().rstrip(')') in ('Bool(', 'Bool')):
            return "Signal dom Bool"
        if port.is_vec:
            elem_type = f"BitVec {port.width}" if port.width > 0 else "BitVec DATA.W"
            return f"List (Signal dom ({elem_type}))"
        inner = self._chisel_type_to_lean(port)
        return f"Signal dom {inner}" if ' ' not in inner else f"Signal dom ({inner})"

    def _reg_lean_type(self, reg: Register) -> str:
        """レジスタの Lean 型"""
        if reg.width == 1 and not reg.is_signed:
            return "Bool"
        if reg.width > 0:
            return f"BitVec {reg.width}"
        return "BitVec DATA.W"

    @staticmethod
    def _to_camel(name: str) -> str:
        """snake_case → camelCase (Lean 命名規則)"""
        if not name or '_' not in name:
            # 先頭小文字化
            return name[0].lower() + name[1:] if name else name
        parts = name.split('_')
        return parts[0].lower() + ''.join(p.capitalize() for p in parts[1:])


# ============================================================
# 4. 高レベル変換ルール (ソース行ベース)
# ============================================================

class LineTransformer:
    """ソースコードの行単位での変換を行う補助トランスフォーマ。
    パーサで構造化できなかった部分のフォールバック変換に使用。"""

    RULES = [
        # (Chisel pattern regex, Sparkle replacement, description)
        (r'import\s+chisel3\._',
         'import Sparkle\nimport Sparkle.Core.Signal\nimport Sparkle.Core.Domain',
         'chisel3 import → Sparkle import'),

        (r'import\s+chisel3\.util\._',
         'open Sparkle.Core.Signal\nopen Sparkle.Core.Domain',
         'chisel3.util import → open Signal/Domain'),

        (r'class\s+(\w+)\s+extends\s+Module\s*\{',
         r'def \1 {dom : DomainConfig}',
         'class Module → def'),

        (r'val\s+io\s*=\s*IO\s*\(\s*new\s+Bundle\s*\{',
         '-- IO ports (converted to function arguments/return)',
         'IO Bundle → comment'),

        (r'RegInit\s*\(\s*(\d+)\.U\((\d+)\.W\)\s*\)',
         r'Signal.register (\1#\2)',
         'RegInit UInt → Signal.register'),

        (r'RegInit\s*\(\s*(\d+)\.S\((\d+)\.W\)\s*\)',
         r'Signal.register ((\1) : BitVec \2)',
         'RegInit SInt → Signal.register'),

        (r'RegInit\s*\(\s*false\.B\s*\)',
         'Signal.register false',
         'RegInit Bool false → Signal.register false'),

        (r'RegInit\s*\(\s*true\.B\s*\)',
         'Signal.register true',
         'RegInit Bool true → Signal.register true'),

        (r'RegNext\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)',
         r'Signal.register \2 \1',
         'RegNext → Signal.register'),

        (r'ShiftRegister\s*\(\s*(.+?)\s*,\s*(\w+)\s*\)',
         r'delayN \2 \1',
         'ShiftRegister → delayN'),

        (r'Cat\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)',
         r'BitVec.append \1 \2',
         'Cat → BitVec.append'),

        (r'(\w+)\.asSInt',
         r'-- /* MANUAL */ \1 を符号付きとして扱う (BitVec.signExtend)',
         '.asSInt → signExtend comment'),

        (r'(\w+)\.asUInt',
         r'-- /* MANUAL */ \1 を符号なしとして扱う',
         '.asUInt → comment'),

        (r'\.reduce\s*\(\s*_\s*\+\s*_\s*\)',
         '.foldl (fun acc x => (· + ·) <$> acc <*> x) (Signal.pure 0)',
         '.reduce(_ + _) → .foldl'),

        (r'Mux\s*\(\s*(.+?)\s*,\s*(.+?)\s*,\s*(.+?)\s*\)',
         r'Signal.mux \1 \2 \3',
         'Mux → Signal.mux'),

        (r'(\d+)\.U\((\d+)\.W\)',
         r'(\1#\2)',
         'literal UInt → BitVec literal'),

        (r'(\d+)\.S\((\d+)\.W\)',
         r'((\1) : BitVec \2)',
         'literal SInt → BitVec literal'),

        (r'(\d+)\.U',
         r'\1',
         'bare .U literal'),

        (r'(\d+)\.S',
         r'((\1) : BitVec _)',
         'bare .S literal'),

        (r'false\.B',
         'false',
         'false.B → false'),

        (r'true\.B',
         'true',
         'true.B → true'),

        (r'UInt\((\d+)\.W\)',
         r'BitVec \1',
         'UInt(N.W) → BitVec N'),

        (r'SInt\((\d+)\.W\)',
         r'BitVec \1',
         'SInt(N.W) → BitVec N'),

        (r'Bool\(\)',
         'Bool',
         'Bool() → Bool'),

        (r'\(new\s+chisel3\.stage\.ChiselStage\)\.emitVerilog\s*\(',
         '-- #synthesizeVerilog',
         'emitVerilog → #synthesizeVerilog'),
    ]

    @classmethod
    def transform_line(cls, line: str) -> tuple[str, list[str]]:
        """1行を変換。(変換後文字列, 適用ルール名リスト) を返す"""
        applied = []
        result = line
        for pattern, replacement, desc in cls.RULES:
            new_result, count = re.subn(pattern, replacement, result)
            if count > 0:
                result = new_result
                applied.append(desc)
        return result, applied

    @classmethod
    def transform_source(cls, source: str) -> tuple[str, list[str]]:
        """ソース全体を行単位で変換"""
        all_applied = []
        out_lines = []
        for line in source.split('\n'):
            new_line, applied = cls.transform_line(line)
            out_lines.append(new_line)
            all_applied.extend(applied)
        return '\n'.join(out_lines), all_applied


# ============================================================
# 5. メイン: 2段階変換パイプライン
# ============================================================

def convert(source: str, verbose=False) -> tuple[str, list[str]]:
    """
    Chisel ソース → Sparkle コード変換のメインパイプライン。

    Phase 1: 構造的変換 (パーサ + コード生成)
      - class Module をパースして def に変換
      - IO Bundle → 関数引数/戻り値
      - RegInit → Signal.register / Signal.loop
      - サブモジュール → 関数呼び出し

    Phase 2: 行単位パターン変換 (フォールバック)
      - Phase 1 でカバーできなかったリテラル・演算子変換
      - import / emitVerilog 等の定型句
    """
    warnings = []

    # --- Phase 1: 構造的変換 ---
    if verbose:
        print("=== Phase 1: Structural Parsing ===", file=sys.stderr)

    parser = ChiselParser(verbose=verbose)
    modules = parser.parse(source)

    if modules:
        if verbose:
            print(f"  Found {len(modules)} module(s): {[m.name for m in modules]}", file=sys.stderr)

        gen = SparkleGenerator(parser, verbose=verbose)
        structural_output = gen.generate(modules)
        warnings.extend(gen.warnings)
    else:
        if verbose:
            print("  No modules found, falling back to line-level transform", file=sys.stderr)
        structural_output = None

    # --- Phase 2: 行単位パターン変換 ---
    if verbose:
        print("\n=== Phase 2: Line-level Pattern Transform ===", file=sys.stderr)

    if structural_output:
        # Phase 1 の出力を Phase 2 でさらに変換 (残りのリテラル等)
        final_output, applied = LineTransformer.transform_source(structural_output)
    else:
        # Phase 1 がスキップされた場合、ソースを直接変換
        final_output, applied = LineTransformer.transform_source(source)

    if verbose and applied:
        unique_rules = set(applied)
        print(f"  Applied {len(applied)} line-level rules ({len(unique_rules)} unique types)", file=sys.stderr)

    return final_output, warnings


# ============================================================
# 6. CLI エントリポイント
# ============================================================

def main():
    parser = argparse.ArgumentParser(
        description='Chisel (Scala) → Sparkle (Lean 4) Signal DSL 変換スクリプト',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用例:
  python chisel2sparkle.py SDIP_conv2d.scala
  python chisel2sparkle.py SDIP_conv2d.scala -o SDIP_conv2d.lean
  python chisel2sparkle.py SDIP_conv2d.scala --dry-run --verbose

変換対応表の詳細は --show-rules オプションで確認できます。
        """
    )
    parser.add_argument('input', nargs='?', help='入力 Chisel ソースファイル (.scala)')
    parser.add_argument('-o', '--output', help='出力 Sparkle ファイル (.lean)')
    parser.add_argument('--dry-run', action='store_true',
                        help='ファイル出力せず標準出力のみ')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='変換過程の詳細ログを出力')
    parser.add_argument('--show-rules', action='store_true',
                        help='変換ルール一覧を表示して終了')
    parser.add_argument('--line-only', action='store_true',
                        help='Phase 2 (行単位変換) のみ実行')

    args = parser.parse_args()

    if args.show_rules:
        print("=" * 72)
        print("Chisel → Sparkle 変換ルール一覧")
        print("=" * 72)
        print()
        print("Phase 1: 構造的変換")
        print("-" * 72)
        rules_phase1 = [
            ("class Foo extends Module", "def foo {dom} ... : Signal dom α"),
            ("val io = IO(new Bundle { ... })", "関数引数 + 戻り値型"),
            ("val reg = RegInit(0.U(8.W))", "Signal.register (0#8) input"),
            ("when(c) { reg := v }", "Signal.loop + Signal.mux c v prev"),
            ("reg := expr (無条件)", "Signal.register init expr"),
            ("Seq.fill(n)(Module(new S))", "List.range n |>.map sub"),
            ("Seq.fill(n,m)(Module(...))", "foldl の入れ子"),
            ("Module(new Queue(t, d))", "delayN d / SyncFIFO"),
            ("object Foo { val X = 8 }", "namespace Foo / def X : Nat := 8"),
            ("io.out := expr", "pure functional return value"),
            (".reduce(_ + _)", ".foldl (fun acc s => (+) <$> acc <*> s) zero"),
        ]
        for chisel, sparkle in rules_phase1:
            print(f"  {chisel:<40} → {sparkle}")

        print()
        print("Phase 2: 行単位パターン変換")
        print("-" * 72)
        for pattern, replacement, desc in LineTransformer.RULES:
            print(f"  [{desc}]")
            print(f"    /{pattern}/")
            print(f"    → {replacement}")
            print()
        return

    # ファイル読み込み
    if not args.input:
        parser.error("入力ファイルを指定してください")
    try:
        with open(args.input, 'r', encoding='utf-8') as f:
            source = f.read()
    except FileNotFoundError:
        print(f"Error: File '{args.input}' not found", file=sys.stderr)
        sys.exit(1)

    # 変換実行
    if args.line_only:
        output, applied = LineTransformer.transform_source(source)
        warnings = []
    else:
        output, warnings = convert(source, verbose=args.verbose)

    # 結果出力
    if args.dry_run:
        print(output)
    else:
        out_path = args.output
        if not out_path:
            out_path = args.input.rsplit('.', 1)[0] + '.lean'
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(output)
        print(f"✓ 変換完了: {args.input} → {out_path}", file=sys.stderr)

    # 警告表示
    if warnings:
        print(f"\n⚠ {len(warnings)} 件の手動確認が必要:", file=sys.stderr)
        for i, w in enumerate(warnings, 1):
            print(f"  {i}. {w}", file=sys.stderr)

    if args.verbose:
        print(f"\n=== 変換統計 ===", file=sys.stderr)
        print(f"  入力: {len(source.split(chr(10)))} 行", file=sys.stderr)
        print(f"  出力: {len(output.split(chr(10)))} 行", file=sys.stderr)
        print(f"  警告: {len(warnings)} 件", file=sys.stderr)


if __name__ == '__main__':
    main()
