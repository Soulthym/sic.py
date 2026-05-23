from copy import copy
from dataclasses import dataclass
from typing import cast
from .utils import *
from . import sic
from . import parser

class CompileError(parser.ParseError):
    pass

class CompilerPass:
    def __init__(self, ctx: "Context"):
        self.ctx = ctx

    def __repr__(self):
        return f"{type(self).__name__}(ctx={pf(self.ctx)})"

    def error(self, message: str, pos: parser.Pos):
        raise CompileError(
            message=message,
            src=self.ctx.src,
            pos=pos,
            filename=self.ctx.filename,
        )

    def visit_ast(self, ast: parser.Ast):
        if isinstance(ast, parser.Tag):
            self.visit_tag(ast)
        elif isinstance(ast, parser.Label):
            self.visit_label(ast)
        elif isinstance(ast, parser.Info):
            self.visit_info(ast)
        elif isinstance(ast, parser.Port):
            self.visit_port(ast)
        elif isinstance(ast, parser.Aux):
            self.visit_aux(ast)
        elif isinstance(ast, parser.Node):
            self.visit_node(ast)
        elif isinstance(ast, parser.Value):
            self.visit_value(ast)
        elif isinstance(ast, parser.Eq):
            self.visit_eq(ast)
        else:
            raise NotImplementedError(
                f"Unknown AST node: {ast!r} "
                f"of type {type(ast)}"
            )
    def visit_tag(self, tag: parser.Tag):
        pass

    def visit_label(self, label: parser.Label):
        pass

    def visit_info(self, info: parser.Info):
        self.visit_tag(info.tag)
        self.visit_label(info.label)

    def visit_port(self, port: parser.Port):
        pass

    def visit_aux(self, aux: parser.Aux):
        self.visit_value(aux.lhs)
        self.visit_value(aux.rhs)

    def visit_node(self, node: parser.Node) -> NodeId:
        self.visit_info(node.info)
        if node.aux is not None:
            self.visit_aux(node.aux)
        return -1

    def visit_value(self, value: parser.Value):
        if isinstance(value.val, parser.Port):
            self.visit_port(value.val)
        elif isinstance(value.val, parser.Node):
            self.visit_node(value.val)
        else:
            raise NotImplementedError(f"Unknown value type: {value.val!r}")

    def visit_eq(self, eq: parser.Eq):
        self.visit_value(eq.lhs)
        self.visit_value(eq.rhs)

    def finalize(self):
        pass

type NodeId = int
type LabelId = int
type LabelName = str
type PortName = str
type PortId = int
type Wire = tuple[sic.Port, sic.Port]

@dataclass
class Context:
    src: str
    filename: str
    label_map: dict[LabelName, LabelId]
    info_map: dict[NodeId, parser.Info]
    port_map: dict[PortName, tuple[list[tuple[sic.Port | PortName, parser.Pos]], parser.Pos]]
    wires: set[Wire]
    net: sic.Net

    def __init__(
        self,
        src: str,
        filename: str = "<input>",
        net: sic.Net | None = None,
        ctx: Context | None = None
    ):
        if ctx is not None:
            self.label_map = copy(ctx.label_map)
            self.info_map = copy(ctx.info_map)
            self.port_map = copy(ctx.port_map)
            self.wires = copy(ctx.wires)
        else:
            self.label_map = {"": 0}
            self.info_map = {
                0: parser.Info(parser.Tag(parser.Token("tag", "φ", parser.no_pos)),
                           parser.no_label)}
            self.port_map = {"main": ([(sic.Port.top(0), parser.no_pos)], parser.no_pos)}
            self.wires = set()
        if net is None:
            net = sic.Net()
        self.net = net
        self.src = src
        self.filename = filename

    def add_wire(self, p1: sic.Port, p2: sic.Port):
        wire = cast(Wire, tuple(sorted((p1, p2))))
        if wire not in self.wires:
            self.net.connect(p1, p2)
        self.wires.add(wire)

class Sema(CompilerPass):
    def alloc_node(self, info: parser.Info) -> NodeId:
        label = info.label.token.value
        if label not in self.ctx.label_map:
            label_id = len(self.ctx.label_map)
            self.ctx.label_map[label] = label_id
        sic_label = self.ctx.label_map[label]
        tag = info.tag.token.value
        if tag == "φ":
            sic_tag = sic.PHI
        elif tag == "ε":
            sic_tag = sic.EPS
        elif tag == "δ":
            sic_tag = sic.DLT
        elif tag == "γ":
            sic_tag = sic.GAM
        else:
            return self.error(f"Unknown tag: {tag!r}", info.tag.pos())
        sic_info = sic.Info(sic_tag, sic_label)
        return self.ctx.net.alloc(sic_info)


    def visit_label(self, label: parser.Label):
        if label != parser.no_label:
            key = label.token.value
            if key not in self.ctx.label_map:
                label_id = len(self.ctx.label_map)
                self.ctx.label_map[key] = label_id
        super().visit_label(label)

    def visit_port(self, port: parser.Port, node_id: NodeId = 0, port_id: PortId = 0):
        name = port.token.value
        if name not in self.ctx.port_map:
            self.ctx.port_map[name] = ([], port.pos())
        ports = self.ctx.port_map[name][0]
        if port_id != 0:
            ports.append((sic.Port(node_id, port_id), port.pos()))
        if len(ports) > 2:
            return self.error(f"Port name '{name}' cannot be used more than twice", port.pos())
        super().visit_port(port)

    def visit_aux(self, aux: parser.Aux, node_id: NodeId = 0):
        self.visit_value(aux.lhs, node_id=node_id, port_id=2)
        self.visit_value(aux.rhs, node_id=node_id, port_id=3)

    def visit_node(self, node: parser.Node, node_id: NodeId = 0, port_id: PortId = 0) -> NodeId:
        info = node.info
        self.visit_info(info)
        new_id = self.alloc_node(info)
        self.ctx.info_map[new_id] = info
        if port_id != 0:
            self.ctx.add_wire(sic.Port.top(new_id), sic.Port(node_id, port_id))
        if node.aux is not None:
            self.visit_aux(node.aux, node_id=new_id)
        return new_id

    def visit_value(self, value: parser.Value, node_id: NodeId = 0, port_id: PortId = 0):
        if isinstance(value.val, parser.Port):
            self.visit_port(value.val, node_id=node_id, port_id=port_id)
        else:
            self.visit_node(value.val, node_id=node_id, port_id=port_id)

    def visit_eq_port_port(self, eq: parser.Eq):
        assert isinstance(eq.lhs.val, parser.Port)
        assert isinstance(eq.rhs.val, parser.Port)
        self.visit_port(eq.lhs.val)
        self.visit_port(eq.rhs.val)
        lhs = eq.lhs.val.token.value
        rhs = eq.rhs.val.token.value
        port_map = self.ctx.port_map
        if lhs not in port_map:
            port_map[lhs] = ([], eq.lhs.pos())
        if rhs not in port_map:
            port_map[rhs] = ([], eq.rhs.pos())
        lhs_ports = port_map[lhs][0]
        rhs_ports = port_map[rhs][0]
        lhs_ports.append((rhs, eq.rhs.pos()))
        rhs_ports.append((lhs, eq.lhs.pos()))

    def visit_eq_port_node(self, eq: parser.Eq):
        assert isinstance(eq.lhs.val, parser.Port)
        assert isinstance(eq.rhs.val, parser.Node)
        node_id = self.visit_node(eq.rhs.val)
        self.visit_port(eq.lhs.val, node_id=node_id, port_id=1)

    def visit_eq_node_port(self, eq: parser.Eq):
        assert isinstance(eq.lhs.val, parser.Node)
        assert isinstance(eq.rhs.val, parser.Port)
        node_id = self.visit_node(eq.lhs.val)
        self.visit_port(eq.rhs.val, node_id=node_id, port_id=1)

    def visit_eq_node_node(self, eq: parser.Eq):
        assert isinstance(eq.lhs.val, parser.Node)
        assert isinstance(eq.rhs.val, parser.Node)
        lhs_id = self.visit_node(eq.lhs.val)
        rhs_id = self.visit_node(eq.rhs.val)
        self.ctx.add_wire(sic.Port.top(lhs_id), sic.Port.top(rhs_id))

    def visit_eq(self, eq: parser.Eq):
        lhs = eq.lhs
        rhs = eq.rhs
        lhs_is_port = isinstance(lhs.val, parser.Port)
        rhs_is_port = isinstance(rhs.val, parser.Port)
        if lhs_is_port and rhs_is_port:
            return self.visit_eq_port_port(eq)
        elif lhs_is_port and not rhs_is_port:
            return self.visit_eq_port_node(eq)
        elif not lhs_is_port and rhs_is_port:
            return self.visit_eq_node_port(eq)
        else:
            return self.visit_eq_node_node(eq)

    def finalize(self):
        port_map = self.ctx.port_map
        for name, ports_and_pos in port_map.items():
            ports_or_names, pos = ports_and_pos
            names = set(n for n, _ in ports_or_names if isinstance(n, str))
            ports = set(p for p, _ in ports_or_names if isinstance(p, sic.Port))
            seen = set()
            while names:
                key = names.pop()
                if key in seen:
                    continue
                seen.add(key)
                other_ports_or_names, other_pos = port_map.get(key, ([], parser.no_pos))
                other_names = set(n for n, _ in other_ports_or_names if isinstance(n, str))
                other_ports = set(p for p, _ in other_ports_or_names if isinstance(p, sic.Port))
                names.update(other_names - seen)
                ports.update(other_ports)
            if len(ports) > 2:
                return self.error(f"Port name '{name}' cannot be connected to more than two ports, got {ports!r}", pos)
            if len(ports) == 2:
                wire = cast(Wire, tuple(sorted(ports)))
                self.ctx.add_wire(*wire)

@dataclass
class Compiler:
    def __init__(
        self,
        src: str,
        filename: str = "<input>",
        ctx: Context | None = None,
        net: sic.Net | None = None,
    ):
        if ctx is None:
            ctx = Context(src=src, filename=filename, net=net)
        self.ctx = ctx
        self.parser = parser.Parser(src=src, filename=filename)
        self.passes = [
            Sema(ctx),
        ]

    def compile(self):
        asts = self.parser.parse()
        for p in self.passes:
            for ast in asts:
                p.visit_ast(ast)
            p.finalize()
        wires = self.ctx.wires
        infos = self.ctx.info_map

@test
def test_compile():
    src = "a = b d = γA(b c) ε = δ(a c)"
    compiler = Compiler(src)
    compiler.compile()
    expect_eq(compiler.ctx.label_map, {
        "": 0,
        "A": 1,
    })
    expect_eq(compiler.ctx.info_map, {
        0: parser.Info(parser.Tag(parser.Token("tag", "φ", parser.no_pos)), parser.no_label),
        1: parser.Info(parser.Tag(parser.Token("tag", "γ", parser.Pos(10, 11))), parser.Label(parser.Token("label", "A", parser.Pos(11, 12)))),
        2: parser.Info(parser.Tag(parser.Token("tag", "ε", parser.Pos(18, 19))), parser.no_label),
        3: parser.Info(parser.Tag(parser.Token("tag", "δ", parser.Pos(22, 23))), parser.no_label),
    })
    expect_eq(compiler.ctx.port_map, {
        "main": ([
            (sic.Port.top(0), parser.no_pos),
        ], parser.no_pos),
        "a": ([
            ("b", parser.Pos(4, 5)),
            (sic.Port.lhs(3), parser.Pos(24, 25)),
        ], parser.Pos(0, 1)),
        "b": ([
            ("a", parser.Pos(0, 1)),
            (sic.Port.lhs(1), parser.Pos(13, 14)),
        ], parser.Pos(4, 5)),
        "c": ([
            (sic.Port.rhs(1), parser.Pos(15, 16)),
            (sic.Port.rhs(3), parser.Pos(26, 27)),
        ], parser.Pos(15, 16)),
        "d": ([
            (sic.Port.top(1), parser.Pos(6, 7)),
        ], parser.Pos(6, 7)),
    })
    expect_eq(compiler.ctx.wires, {
        (sic.Port.top(2), sic.Port.top(3)),
        (sic.Port.lhs(1), sic.Port.lhs(3)),
        (sic.Port.rhs(1), sic.Port.rhs(3)),
    })

@test
def test_compile_chained():
    src = "a = e d = γA(b c) ε = δ(a c) e = f f = b"
    compiler = Compiler(src)
    compiler.compile()
    expect_eq(compiler.ctx.label_map, {
        "": 0,
        "A": 1,
    })
    expect_eq(compiler.ctx.info_map, {
        0: parser.Info(parser.Tag(parser.Token("tag", "φ", parser.no_pos)), parser.no_label),
        1: parser.Info(parser.Tag(parser.Token("tag", "γ", parser.Pos(10, 11))), parser.Label(parser.Token("label", "A", parser.Pos(11, 12)))),
        2: parser.Info(parser.Tag(parser.Token("tag", "ε", parser.Pos(18, 19))), parser.no_label),
        3: parser.Info(parser.Tag(parser.Token("tag", "δ", parser.Pos(22, 23))), parser.no_label),
    })
    expect_eq(compiler.ctx.port_map, {
        "main": ([
            (sic.Port.top(0), parser.no_pos),
        ], parser.no_pos),
        "a": ([
            ("e", parser.Pos(4, 5)),
            (sic.Port.lhs(3), parser.Pos(24, 25)),
        ], parser.Pos(0, 1)),
        "b": ([
            (sic.Port.lhs(1), parser.Pos(13, 14)),
            ("f", parser.Pos(35, 36)),
        ], parser.Pos(13, 14)),
        "c": ([
            (sic.Port.rhs(1), parser.Pos(15, 16)),
            (sic.Port.rhs(3), parser.Pos(26, 27)),
        ], parser.Pos(15, 16)),
        "d": ([
            (sic.Port.top(1), parser.Pos(6, 7)),
        ], parser.Pos(6, 7)),
        "e": ([
            ("a", parser.Pos(0, 1)),
            ("f", parser.Pos(33, 34)),
        ], parser.Pos(4, 5)),
        "f": ([
            ("e", parser.Pos(29, 30)),
            ("b", parser.Pos(39, 40)),
        ], parser.Pos(33, 34)),
    })
    expect_eq(compiler.ctx.wires, {
        (sic.Port.top(2), sic.Port.top(3)),
        (sic.Port.lhs(1), sic.Port.lhs(3)),
        (sic.Port.rhs(1), sic.Port.rhs(3)),
    })

@test
def test_compile_nested():
    src = "a = b d = γA(δB(b d) c) ε = δ(a c)"
    compiler = Compiler(src)
    compiler.compile()
    expect_eq(compiler.ctx.label_map, {
        "": 0,
        "A": 1,
        "B": 2,
    })
    expect_eq(compiler.ctx.info_map, {
        0: parser.Info(parser.Tag(parser.Token("tag", "φ", parser.no_pos)), parser.no_label),
        1: parser.Info(parser.Tag(parser.Token("tag", "γ", parser.Pos(10, 11))), parser.Label(parser.Token("label", "A", parser.Pos(11, 12)))),
        2: parser.Info(parser.Tag(parser.Token("tag", "δ", parser.Pos(13, 14))), parser.Label(parser.Token("label", "B", parser.Pos(14, 15)))),
        3: parser.Info(parser.Tag(parser.Token("tag", "ε", parser.Pos(24, 25))), parser.no_label),
        4: parser.Info(parser.Tag(parser.Token("tag", "δ", parser.Pos(28, 29))), parser.no_label),
    })
    expect_eq(compiler.ctx.port_map, {
        "main": ([
            (sic.Port.top(0), parser.no_pos),
        ], parser.no_pos),
        "a": ([
            ("b", parser.Pos(4, 5)),
            (sic.Port.lhs(4), parser.Pos(30, 31)),
        ], parser.Pos(0, 1)),
        "b": ([
            ("a", parser.Pos(0, 1)),
            (sic.Port.lhs(2), parser.Pos(16, 17)),
        ], parser.Pos(4, 5)),
        "c": ([
            (sic.Port.rhs(1), parser.Pos(21, 22)),
            (sic.Port.rhs(4), parser.Pos(32, 33)),
        ], parser.Pos(21, 22)),
        "d": ([
            (sic.Port.rhs(2), parser.Pos(18, 19)),
            (sic.Port.top(1), parser.Pos(6, 7)),
        ], parser.Pos(18, 19)),
    })
    expect_eq(sorted(compiler.ctx.wires), sorted({
        (sic.Port.top(3), sic.Port.top(4)),
        (sic.Port.lhs(2), sic.Port.lhs(4)),
        (sic.Port.rhs(1), sic.Port.rhs(4)),
        (sic.Port.top(1), sic.Port.rhs(2)),
        (sic.Port.lhs(1), sic.Port.top(2)),
    }))

if __name__ == "__main__":
    run_tests()
