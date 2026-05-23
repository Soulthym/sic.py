from dataclasses import dataclass
from typing import Callable
from typing import Iterable
from typing import Literal
from typing import Protocol
from typing import Self
import re
from .utils import *

def pos_to_line_col(src: str, pos: Pos) -> tuple[int, int]:
    start = pos.start
    line = src.count("\n", 0, start) + 1
    col = start - src.rfind("\n", 0, start)
    return line, col

def repr_pos(src: str, pos: Pos, filename: str) -> str:
    line, col = pos_to_line_col(src, pos)
    str_line = src.splitlines()[line - 1]
    return f"{filename}:{line}:{col}\n{str_line}:\n{' ' * (col - 1)}^"

class HasPos(Protocol):
    def pos(self) -> Pos: ...

@dataclass
class Pos(HasPos):
    start: int
    end: int
    def pos(self):
        return self
    def combine(self, other: Self) -> Self:
        start = min(self.start, other.start)
        end = max(self.end, other.end)
        return type(self)(start, end)
    def __repr__(self):
        return f"{self.start}-{self.end}"

no_pos = Pos(0, 0)

type TokenTy = Literal["tag", "label", "port", "lpar", "rpar", "eq"]

@dataclass
class Token(HasPos):
    ty: str
    value: str
    _pos: Pos
    def __repr__(self):
        return f"{self.value!r}:{self.ty}@{self.pos()}"

    def pos(self):
        return self._pos

type Tokens = list[Token]

lower_pat = r"[a-z_][a-z0-9_]*"
# no leading "_" to avoid tokenization overlap with lower_pat
# Labels do not really need it as they are non-linear resources,
# if we add support for leading "_" in labels, we can either
# - coalesce overlapping port/label tokens
# - use regex instead of re
# - use lookahead in re to disambiguate
upper_pat = r"[A-Z][A-Z0-9_]*"
tag_pat = r"[φεδγ]"
label_pat = upper_pat
port_pat = lower_pat
lpar_pat = r"\("
rpar_pat = r"\)"
eq_pat = r"="
named = lambda name, pat: f"(?P<{name}>{pat})"
token_pat = "|".join([
    named("tag", tag_pat),
    named("label", label_pat),
    named("port", port_pat),
    named("lpar", lpar_pat),
    named("rpar", rpar_pat),
    named("eq", eq_pat),
])
token_re = re.compile(token_pat)

def tokenize(src):
    tokens = []
    for m in token_re.finditer(src):
        matches = list((k, v) for k, v in m.groupdict().items() if v is not None)
        assert len(matches) <= 1, f"Overlapping token patterns, got more than one match: {matches}"
        start = m.start()
        end = m.end()
        pos = Pos(start, end)
        assert len(matches) > 0, f"Failed to match any token at position {pos}"
        ty, val = matches[0]
        tokens.append(Token(ty, val, pos))
    return tokens

class Ast(HasPos): ...
@dataclass
class Tag(Ast):
    token: Token
    def pos(self):
        return self.token.pos()
@dataclass
class Label(Ast):
    token: Token
    def pos(self):
        return self.token.pos()

no_label = Label(Token("label", "", no_pos))
@dataclass
class Info(Ast):
    tag: Tag
    label: Label
    def pos(self):
        return self.tag.pos().combine(self.label.pos())
@dataclass
class Port(Ast):
    token: Token
    def pos(self):
        return self.token.pos()
@dataclass
class Aux(Ast):
    lpar: Token
    lhs: "Value"
    rhs: "Value"
    rpar: Token
    def pos(self):
        return self.lpar.pos().combine(self.rpar.pos())
@dataclass
class Node(Ast):
    info: Info
    aux: Aux | None
    def pos(self):
        if self.aux is None:
            return self.info.pos()
        return self.info.pos().combine(self.aux.pos())
@dataclass
class Value(Ast):
    val: Port | Node
    def pos(self):
        return self.val.pos()
@dataclass
class Eq(Ast):
    lhs: Value
    eq: Token
    rhs: Value
    def pos(self):
        return self.lhs.pos().combine(self.rhs.pos())

class ParseError(Exception):
    def __init__(self, message: str, src: str, pos: Pos, filename: str = "<input>"):
        super().__init__(message)
        self.pos = pos
        self.src = src
        self.filename = filename
    def __str__(self):
        pos_repr = repr_pos(self.src, self.pos, self.filename)
        return f"{super().__str__()}\n{pos_repr}"

def hide_parser(obj):
    if isinstance(obj, Parser):
        tok = obj.peek_token()
        if tok is None:
            return "Parser(None)"
        return f"Parser({tok!r}...)"

@dataclass(init=False)
class Parser:
    tokens: Tokens
    """A recursive descent parser for the following grammar:
    tag   : "φ" | "γ" | "δ" | "ε"
    label : /[A-Z][A-Z0-9_]*/
    info  : tag
          | tag label
    port  : /[a-z_][a-z0-9_]*/
    aux   : "(" value value ")"
    node  : info       where info.tag in ("φ", "ε")
          | info aux   where info.tag in ("γ", "δ")
    value : port
          | node
    eq    : value "=" value
    src : eq*
    """
    def __init__(self, src: str, filename: str = "<input>"):
        self.src = src
        self.filename = filename
        self.tokens = tokenize(src)
        self.tokens.reverse()

    def try_parse[T](self, parser: Callable[[], T]) -> T | None:
        tokens = self.tokens.copy()
        indent = get_indent()
        try:
            return parser()
        except ParseError:
            self.tokens = tokens
            set_indent(indent)
            return None

    def error(self, message: str, pos: Pos):
        raise ParseError(message, self.src, pos)

    def peek_token(self) -> Token | None:
        if self.tokens:
            return self.tokens[-1]

    def next_token(self) -> Token:
        if not self.tokens:
            l = len(self.src)
            self.error("Unexpected end of input", Pos(l, l))
        return self.tokens.pop()

    def parse_token(self, expected_type: TokenTy) -> Token:
        token = self.next_token()
        if token.ty != expected_type:
            self.error(f"Expected token of type '{expected_type}', but got '{token.ty}'", token.pos())
        token = token
        return token

    def parse_tag(self) -> Tag:
        """Syntax:
        tag : "φ" | "γ" | "δ" | "ε"
        """
        token = self.parse_token("tag")
        return Tag(token)

    def parse_label(self) -> Label:
        """Syntax:
        label : /[A-Z][A-Z0-9_]*/
        """
        token = self.parse_token("label")
        return Label(token)

    def parse_info(self) -> Info:
        """Syntax:
        info : tag
             | tag label
        """
        tag = self.parse_tag()
        label = self.try_parse(self.parse_label) or no_label
        return Info(tag, label)

    def parse_port(self) -> Port:
        """Syntax:
        port : /[a-z_][a-z0-9_]*/
        """
        token = self.parse_token("port")
        return Port(token)

    def parse_aux(self) -> Aux:
        """Syntax:
        aux : "(" value value ")"
        """
        lpar = self.parse_token("lpar")
        lhs = self.parse_value()
        rhs = self.parse_value()
        rpar = self.parse_token("rpar")
        return Aux(lpar, lhs, rhs, rpar)

    def parse_node(self) -> Node:
        """Syntax:
        node : info       where info.tag in ("φ", "ε")
             | info aux   where info.tag in ("γ", "δ")
        """
        info = self.parse_info()
        tag = info.tag.token.value
        aux = self.parse_aux() if tag in ("γ", "δ") else None
        return Node(info, aux)

    def parse_value(self) -> Value:
        """Syntax:
        value : port
              | node
        """
        val = Value(self.try_parse(self.parse_port) or self.parse_node())
        return val

    def parse_eq(self) -> Eq:
        """Syntax:
        eq : value "=" value
        """
        lhs = self.parse_value()
        eq = self.parse_token("eq")
        rhs = self.parse_value()
        return Eq(lhs, eq, rhs)

    def parse_iter(self) -> Iterable[Ast]:
        """Syntax:
        program : eq*
        """
        while self.tokens:
            expr = self.parse_eq()
            yield expr

    def parse(self) -> list[Ast]:
        """Syntax:
        program : eq*
        """
        asts = []
        for expr in self.parse_iter():
            asts.append(expr)
        return asts

@test
def test_tokenize():
    src = "b = φA(c, d)"
    tokens = tokenize(src)
    expected = [
        Token("port", "b", Pos(0, 1)),
        Token("eq", "=", Pos(2, 3)),
        Token("tag", "φ", Pos(4, 5)),
        Token("label", "A", Pos(5, 6)),
        Token("lpar", "(", Pos(6, 7)),
        Token("port", "c", Pos(7, 8)),
        Token("port", "d", Pos(10, 11)),
        Token("rpar", ")", Pos(11, 12)),
    ]
    expect_eq(tokens, expected)

@test
def test_parse_tag():
    src = "φ γ δ ε"
    parser = Parser(src)
    expect_eq(parser.parse_tag(), Tag(Token("tag", "φ", Pos(0, 1))))
    expect_eq(parser.parse_tag(), Tag(Token("tag", "γ", Pos(2, 3))))
    expect_eq(parser.parse_tag(), Tag(Token("tag", "δ", Pos(4, 5))))
    expect_eq(parser.parse_tag(), Tag(Token("tag", "ε", Pos(6, 7))))
    expect_eq(parser.tokens, [])

@test
def test_parse_label():
    src = "A B C D"
    parser = Parser(src)
    expect_eq(parser.parse_label(), Label(Token("label", "A", Pos(0, 1))))
    expect_eq(parser.parse_label(), Label(Token("label", "B", Pos(2, 3))))
    expect_eq(parser.parse_label(), Label(Token("label", "C", Pos(4, 5))))
    expect_eq(parser.parse_label(), Label(Token("label", "D", Pos(6, 7))))
    expect_eq(parser.tokens, [])

@test
def test_parse_info():
    src = "φA γB δ"
    parser = Parser(src)
    expect_eq(parser.parse_info(), Info(Tag(Token("tag", "φ", Pos(0, 1))), Label(Token("label", "A", Pos(1, 2)))))
    expect_eq(parser.parse_info(), Info(Tag(Token("tag", "γ", Pos(3, 4))), Label(Token("label", "B", Pos(4, 5)))))
    expect_eq(parser.parse_info(), Info(Tag(Token("tag", "δ", Pos(6, 7))), no_label))
    expect_eq(parser.tokens, [])

@test
def test_parse_port():
    src = "a b_ _c1 d4z_a"
    parser = Parser(src)
    expect_eq(parser.parse_port(), Port(Token("port", "a", Pos(0, 1))))
    expect_eq(parser.parse_port(), Port(Token("port", "b_", Pos(2, 4))))
    expect_eq(parser.parse_port(), Port(Token("port", "_c1", Pos(5, 8))))
    expect_eq(parser.parse_port(), Port(Token("port", "d4z_a", Pos(9, 14))))
    expect_eq(parser.tokens, [])


@test
def test_parse_aux():
    src = "(a b_c1)(d4z _a) (_a1 _b)"
    parser = Parser(src)
    expect_eq(parser.parse_aux(), Aux(
        lpar=Token("lpar", "(", Pos(0, 1)),
        lhs=Value(Port(Token("port", "a", Pos(1, 2)))),
        rhs=Value(Port(Token("port", "b_c1", Pos(3, 7)))),
        rpar=Token("rpar", ")", Pos(7, 8)),
    ))
    expect_eq(parser.parse_aux(), Aux(
        lpar=Token("lpar", "(", Pos(8, 9)),
        lhs=Value(Port(Token("port", "d4z", Pos(9, 12)))),
        rhs=Value(Port(Token("port", "_a", Pos(13, 15)))),
        rpar=Token("rpar", ")", Pos(15, 16)),
    ))
    expect_eq(parser.parse_aux(), Aux(
        lpar=Token("lpar", "(", Pos(17, 18)),
        lhs=Value(Port(Token("port", "_a1", Pos(18, 21)))),
        rhs=Value(Port(Token("port", "_b", Pos(22, 24)))),
        rpar=Token("rpar", ")", Pos(24, 25)),
    ))
    expect_eq(parser.tokens, [])

@test
def test_parse_node():
    src = "γA(c d) φB δ(e f) ε"
    parser = Parser(src)
    expect_eq(parser.parse_node(), Node(
        info=Info(Tag(Token("tag", "γ", Pos(0, 1))), Label(Token("label", "A", Pos(1, 2)))),
        aux=Aux(
            lpar=Token("lpar", "(", Pos(2, 3)),
            lhs=Value(Port(Token("port", "c", Pos(3, 4)))),
            rhs=Value(Port(Token("port", "d", Pos(5, 6)))),
            rpar=Token("rpar", ")", Pos(6, 7)),
        ),
    ))
    expect_eq(parser.parse_node(), Node(
        info=Info(Tag(Token("tag", "φ", Pos(8, 9))), Label(Token("label", "B", Pos(9, 10)))),
        aux=None,
    ))
    expect_eq(parser.parse_node(), Node(
        info=Info(Tag(Token("tag", "δ", Pos(11, 12))), no_label),
        aux=Aux(
            lpar=Token("lpar", "(", Pos(12, 13)),
            lhs=Value(Port(Token("port", "e", Pos(13, 14)))),
            rhs=Value(Port(Token("port", "f", Pos(15, 16)))),
            rpar=Token("rpar", ")", Pos(16, 17)),
        ),
    ))
    expect_eq(parser.parse_node(), Node(
        info=Info(Tag(Token("tag", "ε", Pos(18, 19))), no_label),
        aux=None,
    ))
    expect_eq(parser.tokens, [])

@test
def test_parse_value():
    src = "a γA(c d)"
    parser = Parser(src)
    expect_eq(parser.parse_value(), Value(Port(Token("port", "a", Pos(0, 1)))))
    expect_eq(parser.parse_value(), Value(Node(
        info=Info(Tag(Token("tag", "γ", Pos(2, 3))), Label(Token("label", "A", Pos(3, 4)))),
        aux=Aux(
            lpar=Token("lpar", "(", Pos(4, 5)),
            lhs=Value(Port(Token("port", "c", Pos(5, 6)))),
            rhs=Value(Port(Token("port", "d", Pos(7, 8)))),
            rpar=Token("rpar", ")", Pos(8, 9)),
        ),
    )))
    expect_eq(parser.tokens, [])

@test
def test_parse_eq():
    src = "a = b d = γA(b c) ε = δ(a c)"
    parser = Parser(src)
    expect_eq(parser.parse_eq(), Eq(
        lhs=Value(Port(Token("port", "a", Pos(0, 1)))),
        eq=Token("eq", "=", Pos(2, 3)),
        rhs=Value(Port(Token("port", "b", Pos(4, 5)))),
    ))
    expect_eq(parser.parse_eq(), Eq(
        lhs=Value(Port(Token("port", "d", Pos(6, 7)))),
        eq=Token("eq", "=", Pos(8, 9)),
        rhs=Value(Node(
            info=Info(Tag(Token("tag", "γ", Pos(10, 11))), Label(Token("label", "A", Pos(11, 12)))),
            aux=Aux(
                lpar=Token("lpar", "(", Pos(12, 13)),
                lhs=Value(Port(Token("port", "b", Pos(13, 14)))),
                rhs=Value(Port(Token("port", "c", Pos(15, 16)))),
                rpar=Token("rpar", ")", Pos(16, 17)),
            ),
        )),
    ))
    expect_eq(parser.parse_eq(), Eq(
        lhs=Value(Node(
            info=Info(Tag(Token("tag", "ε", Pos(18, 19))), no_label),
            aux=None,
        )),
        eq=Token("eq", "=", Pos(20, 21)),
        rhs=Value(Node(
            info=Info(Tag(Token("tag", "δ", Pos(22, 23))), no_label),
            aux=Aux(
                lpar=Token("lpar", "(", Pos(23, 24)),
                lhs=Value(Port(Token("port", "a", Pos(24, 25)))),
                rhs=Value(Port(Token("port", "c", Pos(26, 27)))),
                rpar=Token("rpar", ")", Pos(27, 28)),
            ),
        )),
    ))

@test
def test_parse():
    src = "a = b d = γA(b c) ε = δ(a c)"
    parser = Parser(src)
    expect_eq(parser.parse(), [
        Eq(
            lhs=Value(Port(Token("port", "a", Pos(0, 1)))),
            eq=Token("eq", "=", Pos(2, 3)),
            rhs=Value(Port(Token("port", "b", Pos(4, 5)))),
        ),
        Eq(
            lhs=Value(Port(Token("port", "d", Pos(6, 7)))),
            eq=Token("eq", "=", Pos(8, 9)),
            rhs=Value(Node(
                info=Info(Tag(Token("tag", "γ", Pos(10, 11))), Label(Token("label", "A", Pos(11, 12)))),
                aux=Aux(
                    lpar=Token("lpar", "(", Pos(12, 13)),
                    lhs=Value(Port(Token("port", "b", Pos(13, 14)))),
                    rhs=Value(Port(Token("port", "c", Pos(15, 16)))),
                    rpar=Token("rpar", ")", Pos(16, 17)),
                ),
            )),
        ),
        Eq(
            lhs=Value(Node(
                info=Info(Tag(Token("tag", "ε", Pos(18, 19))), no_label),
                aux=None,
            )),
            eq=Token("eq", "=", Pos(20, 21)),
            rhs=Value(Node(
                info=Info(Tag(Token("tag", "δ", Pos(22, 23))), no_label),
                aux=Aux(
                    lpar=Token("lpar", "(", Pos(23, 24)),
                    lhs=Value(Port(Token("port", "a", Pos(24, 25)))),
                    rhs=Value(Port(Token("port", "c", Pos(26, 27)))),
                    rpar=Token("rpar", ")", Pos(27, 28)),
                ),
            )),
        )])

if __name__ == "__main__":
    run_tests()
