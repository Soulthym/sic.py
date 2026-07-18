from dataclasses import dataclass
from functools import partial
from pprint import pformat as pf
from typing import cast
from typing import Self
from copy import deepcopy
import re
from .utils import *
from . import compiler

type Arity = bool
AR0 = False
AR2 = True

type Eal = bool
EXP = False
AFF = True

@dataclass(frozen=True, repr=False, order=True)
class Tag:
    arity: Arity
    eal: Eal
    def __repr__(self) -> str:
        bits = (self.arity, self.eal)
        if bits == (AR0, EXP):
            return "φ"
        elif bits == (AR0, AFF):
            return "ε"
        elif bits == (AR2, EXP):
            return "δ"
        elif bits == (AR2, AFF):
            return "γ"
        raise ValueError(f"impossible tag with bits: {bits!r}")

PHI = Tag(AR0, EXP)
EPS = Tag(AR0, AFF)
DLT = Tag(AR2, EXP)
GAM = Tag(AR2, AFF)

type Label = int

@dataclass(frozen=True, repr=False, order=True)
class Info:
    tag: Tag
    label: Label = 0
    @classmethod
    def phi(cls, label: Label = 0) -> Self:
        return cls(PHI, label)
    @classmethod
    def eps(cls, label: Label = 0) -> Self:
        return cls(EPS, label)
    @classmethod
    def dlt(cls, label: Label = 0) -> Self:
        return cls(DLT, label)
    @classmethod
    def gam(cls, label: Label = 0) -> Self:
        return cls(GAM, label)
    def show(
        self,
        label_map: dict[compiler.LabelId, compiler.LabelName],
    ) -> str:
        if label_map is not None:
            label = label_map.get(self.label, f"L{self.label}")
        elif self.label:
            label = f"{self.label}"
        else:
            label = ""
        return f"{self.tag}{label}"
    def __repr__(self) -> str:
        return self.show(label_map={})

FREE = Info.phi() # a dummy info for free nodes

type NodeId = int
type PortId = int

@dataclass(frozen=True, repr=False, order=True)
class Port:
    node_id: NodeId
    port_id: PortId
    @classmethod
    def top(cls, node_id: NodeId) -> Self:
        return cls(node_id, 1)
    @classmethod
    def lhs(cls, node_id: NodeId) -> Self:
        return cls(node_id, 2)
    @classmethod
    def rhs(cls, node_id: NodeId) -> Self:
        return cls(node_id, 3)
    def __repr__(self) -> str:
        if self.port_id == 0 and self.node_id == 0:
            return "ø"
        return f"{self.node_id}:{self.port_id}"

unused = Port(0, 0) # a dummy port for uninitialized ports

@dataclass(init=False, repr=False, order=True)
class Node:
    info: Info
    top: Port
    lhs: Port
    rhs: Port
    def __init__(self, info: Info, node_id: NodeId):
        self.info = info
        self.top = Port.top(node_id)
        self.lhs = Port.lhs(node_id)
        self.rhs = Port.rhs(node_id)
    @classmethod
    def phi(cls, node_id: NodeId, label: Label = 0) -> Self:
        return cls(Info.phi(label), node_id)
    @classmethod
    def eps(cls, node_id: NodeId, label: Label = 0) -> Self:
        return cls(Info.eps(label), node_id)
    @classmethod
    def dlt(cls, node_id: NodeId, label: Label = 0) -> Self:
        return cls(Info.dlt(label), node_id)
    @classmethod
    def gam(cls, node_id: NodeId, label: Label = 0) -> Self:
        return cls(Info.gam(label), node_id)
    def get_port(self, port_id: PortId) -> Port:
        assert 1 <= port_id <= 3, f"invalid port id: {port_id!r}"
        ports = [self.top, self.lhs, self.rhs]
        return ports[port_id - 1]
    def set_port(self, port_id: PortId, p: Port):
        assert 1 <= port_id <= 3, f"invalid port id: {port_id!r}"
        if port_id == 1:
            self.top = p
        elif port_id == 2:
            self.lhs = p
        elif port_id == 3:
            self.rhs = p
    def show(
        self,
        label_map: dict[compiler.LabelId, compiler.LabelName],
    ) -> str:
        aux = ""
        if self.info.tag.arity == AR2:
            aux = f" {self.lhs} {self.rhs}"
        return f"{self.info.show(label_map=label_map)}({self.top}{aux})"
    def __repr__(self) -> str:
        return self.show(label_map={})

@dataclass(init=False)
class Net:
    free_id: NodeId
    nodes: list[Node]
    def __init__(self):
        self.nodes = [Node.phi(0)] # root node
        self.free_id = 0
    def show(
        self,
        label_map: dict[compiler.LabelId, compiler.LabelName],
    ) -> str:
        repr_node = partial(Node.show, label_map=label_map)
        free_id = f"free_id={self.free_id}"
        nodes = ("nodes=[\n        " +
                 ",\n        ".join(map(
                     lambda x: f"{x[0]}: {repr_node(x[1])}",
                     enumerate(self.nodes))) +
                 "\n    ]")
        return f"Net(\n    {free_id},\n    {nodes}\n)"
    def __repr__(self) -> str:
        return self.show(label_map={})
    def root(self) -> Port:
        return Port.top(0)
    def get_node(self, p: Port | NodeId) -> Node:
        if isinstance(p, Port):
            return self.nodes[p.node_id]
        return self.nodes[p]
    def get_port(self, p: Port) -> Port:
        return self.get_node(p).get_port(p.port_id)
    def set_port(self, p: Port, q: Port):
        self.get_node(p).set_port(p.port_id, q)
    def get_info(self, p: Port | NodeId) -> Info:
        return self.get_node(p).info
    def alloc(self, info: Info) -> NodeId:
        if self.free_id != 0:
            node_id = self.free_id
            self.free_id = self.nodes[node_id].top.node_id
            self.nodes[node_id] = Node(info, node_id)
            return node_id
        node_id = len(self.nodes)
        node = Node(info, node_id)
        self.nodes.append(node)
        return node_id
    def free(self, node_id: NodeId):
        node = self.nodes[node_id]
        assert node.info.tag != PHI, f"double free of node id: {node_id!r}"
        # reference the next free node instead of the current node
        next_free_id = self.free_id
        self.nodes[node_id] = Node.phi(next_free_id)
        self.free_id = node_id
    def connect(self, a: Port, b: Port):
        self.set_port(a, b)
        self.set_port(b, a)
    def io(self, a: Port, b: Port):
        raise NotImplementedError("not implemented yet")
    def annihilate_nil(self, a: Port, b: Port):
        a_info = self.get_info(a)
        b_info = self.get_info(b)
        if a_info.tag == PHI or b_info.tag == PHI:
            self.io(a, b)
        self.free(a.node_id)
        self.free(b.node_id)
    def annihilate_bin(self, a: Port, b: Port):
        print(f"{b=}")
        print(f"{a=}")
        a_nid = a.node_id
        b_nid = b.node_id
        print(f"{a_nid=}")
        print(f"{b_nid=}")
        a_lhs = Port.lhs(a.node_id)
        a_rhs = Port.rhs(a.node_id)
        b_lhs = Port.lhs(b.node_id)
        b_rhs = Port.rhs(b.node_id)
        a_lhs_rev = self.get_port(a_lhs)
        a_rhs_rev = self.get_port(a_rhs)
        b_lhs_rev = self.get_port(b_lhs)
        b_rhs_rev = self.get_port(b_rhs)
        inputs  = [a_lhs,     a_rhs,     b_lhs,     b_rhs]
        outputs = [a_lhs_rev, a_rhs_rev, b_lhs_rev, b_rhs_rev]
        print(f"{inputs=}")
        print(f"{outputs=}")
        self_connects = [4, 4, 4, 4]
        for j, out in enumerate(outputs):
            if out.node_id == a_nid or out.node_id == b_nid:
                for i, inp in enumerate(inputs):
                    if inp == out:
                        self_connects[i] = j
                        break
        print(f"{self_connects=}")
        raise NotImplementedError("not implemented yet")

    def distribute(self, a: Port, b: Port):
        raise NotImplementedError("not implemented yet")
    def commute(self, a: Port, b: Port):
        raise NotImplementedError("not implemented yet")
    def whnf(self):
        raise NotImplementedError("not implemented yet")
    def compare(
        self,
        other: Self,
        at: list[tuple[Port, Port]] | None = None,
        label_map: dict[compiler.LabelId, compiler.LabelName] | None = None,
    ) -> tuple[bool, str]:
        l_net = self
        r_net = other
        map_l_r: dict[Port, Port] = {}
        map_r_l: dict[Port, Port] = {}
        if at is None:
            at = (l_net.root(), r_net.root())
        l, r = at
        map_l_r[l] = r
        map_r_l[r] = l
        stack: list[tuple[Port, Port]] = [(l, r)]
        seen: set[tuple[Port, Port]] = set()
        while stack:
            l, r = stack.pop()
            if (l, r) in seen:
                continue
            seen.add((l, r))
            if map_l_r.get(l) != r or map_r_l.get(r) != l:
                return False, (
                    f"inconsistent mapping for ports: {l!r} <-> {r!r}\n"
                    f"left -> right: {pf(map_l_r)}\n"
                    f"right -> left: {pf(map_r_l)}")
            map_l_r[l] = r
            map_r_l[r] = l
            l_node = self.get_node(l)
            r_node = other.get_node(r)
            if l.port_id != r.port_id:
                return False, f"mismatched port ids: {l!r} <-> {r!r} in\n  left node: {l.node_id}: {l_node.show(label_map=label_map)},\n  right node: {r.node_id}: {r_node.show(label_map=label_map)}"
            if l_node.info != r_node.info:
                return False, f"mismatched node info: {l_node.info!r} <-> {r_node.info!r} in\n  left node: {l.node_id}: {l_node.show(label_map=label_map)},\n  right node: {r.node_id}: {r_node.show(label_map=label_map)}"
            stack.append((l_node.top, r_node.top))
            # same as r_node.info since l_node.info == r_node.info
            is_binary = l_node.info.tag.arity
            if is_binary:
                stack.append((l_node.lhs, r_node.lhs))
                stack.append((l_node.rhs, r_node.rhs))
        return True, ""

    def __eq__(self, other) -> bool:
        if not isinstance(other, Net):
            return NotImplemented
        other_cast: Self = cast(Self, other)
        eq, err = self.compare(other_cast)
        return eq

def compiler_test_ctx() -> compiler.Context:
    ctx = compiler.Context("")
    ctx.label_map['A'] = 1
    ctx.label_map['B'] = 2
    ctx.label_map['C'] = 3
    ctx.label_map['D'] = 4
    return ctx

@test
def test_net_annihilate_nil():
    """\
    εA <-> εA
    cases:
      0: ø
    """
    cases = [
        # 0: ø
        ("εA = εA", ""),
        # ("φA = φA", ""),
    ]
    ctx = compiler_test_ctx()
    lhs = Port.top(1)
    rhs = Port.top(2)
    for i, (before, expect) in enumerate(cases):
        before_net = compiler.Compiler(
            before, ctx=deepcopy(ctx)).compile()

        expect_net = compiler.Compiler(
            expect, ctx=deepcopy(ctx)).compile()

        result_net = before_net
        result_net.annihilate_nil(lhs, rhs)
        for l, r in zip(result_net.nodes, expect_net.nodes):
            expect_eq(l.info, FREE)
            expect_eq(r.info, FREE)

@test
def test_net_annihilate_bin():
    """\
    γ(b a) = γ(c d)
    cases:
      0: ø
      1: a <-> b
      2:          c <-> d
      3: a <-> b, c <-> d
      4: a <-> d
      5:          c <-> b
      6: a <-> d, c <-> b
      7: a <-> c
      8:          b <-> d
      9: a <-> c, b <-> d
    """
    suffix_inp = "a = εA, b = εB, c = εC, d = εD, "
    prefix_out = "φ = l, φ = r, "
    cases = [
        # 0: ø
        ("γ(b   a) = γ(c   d)" + suffix_inp,
         prefix_out + "εB = εC, εA = εD"),
        # 1: a <-> b
        ("γ(ab ab) = γ(c   d)" + suffix_inp,
         prefix_out + "ab = εC, ab = εD"),
        # 2:          c <-> d
        ("γ(b   a) = γ(cd cd)" + suffix_inp,
         prefix_out + "εB = cd, εA = cd"),
        # 3: a <-> b, c <-> d
        ("γ(ab ab) = γ(cd cd)" + suffix_inp,
         prefix_out + "ab = cd, ab = cd"),
        # 4: a <-> d
        ("γ(b  ad) = γ(c  ad)" + suffix_inp,
         prefix_out + "εB = εC, ad = ad"),
        # 5:          c <-> b
        ("γ(cb  a) = γ(cb  d)" + suffix_inp,
         prefix_out + "cb = cb, εA = εD"),
        # 6: a <-> d, c <-> b
        ("γ(cb ad) = γ(cb ad)" + suffix_inp,
         prefix_out + "cb = cb, ad = ad"),
        # 7: a <-> c
        ("γ(b  ac) = γ(ac  d)" + suffix_inp,
         prefix_out + "εB = ac, ac = εD"),
        # 8:          b <-> d
        ("γ(bd  a) = γ(c  bd)" + suffix_inp,
         prefix_out + "bd = εC, εA = bd"),
        # 9: a <-> c, b <-> d
        ("γ(bd ac) = γ(ac bd)" + suffix_inp,
         prefix_out + "bd = ac, ac = bd"),
    ]
    ctx = compiler_test_ctx()
    label_map = reverse_dict(ctx.label_map)
    print("testing annihilate_bin:")
    indent()
    lhs = Port.top(1)
    rhs = Port.top(2)
    # lhs is upside down, order is left -> right,
    # so a and b are swapped
    b = Port.lhs(1)
    a = Port.rhs(1)
    c = Port.lhs(2)
    d = Port.rhs(2)
    ats = [(v, v) for v in [lhs, rhs, a, b, c, d]]
    for i, (before, expect) in enumerate(cases):
        print(f"case {i}:")
        indent()
        print("before:", before)
        before_net = compiler.Compiler(
            before, ctx=deepcopy(ctx)).compile()
        print(before_net.show(label_map=label_map))

        print("expect:", expect)
        expect_net = compiler.Compiler(
            expect, ctx=deepcopy(ctx)).compile()
        print(expect_net.show(label_map=label_map))

        print("result:")
        result_net = before_net
        result_net.annihilate_bin(lhs, rhs)
        print(result_net.show(label_map=label_map))
        for at in ats:
            res, err = result_net.compare(expect_net, at=at)
            if not res:
                # dedent(by=2)
                raise AssertionError(err)
        dedent()
    dedent()

@test
def test_net_distribution():
    raise NotImplementedError("not implemented yet")

@test
def test_net_commutation():
    raise NotImplementedError("not implemented yet")

if __name__ == "__main__":
    run_tests(skip_not_implemented=False)
    print("Done.")
