from io import StringIO
from pprint import pformat
from functools import wraps
from functools import partial
import inspect
import textwrap as tw

pf = partial(pformat, compact=True, width=1, sort_dicts=True)

_print = print
INDENT_LEVEL = 0
def indent(by: int = 1):
    global INDENT_LEVEL
    INDENT_LEVEL += by
def dedent(by: int = 1):
    global INDENT_LEVEL
    INDENT_LEVEL -= by
def get_indent():
    global INDENT_LEVEL
    return INDENT_LEVEL
def set_indent(level):
    global INDENT_LEVEL
    INDENT_LEVEL = level
def print(*args, end="\n", **kwargs):
    s = StringIO()
    _print(*args, file=s, end=end, **kwargs)
    out = s.getvalue()
    indented = tw.indent(out, "  " * INDENT_LEVEL)
    return _print(indented, end="", **kwargs)

def debug_arg(arg, repr_arg=None):
    out = repr_arg(arg) if repr_arg else arg
    if out is not None:
        return pf(out)
    if callable(arg):
        return f"{arg.__qualname__}"
    return repr(arg)

def debug(f=None, *, repr_arg=None):
    if f is None:
        return lambda f: debug(f, repr_arg=repr_arg)
    @wraps(f)
    def wrapper(*args, **kwargs):
        sig = inspect.signature(f)
        bound = sig.bind(*args, **kwargs)
        args_repr = [f"{k}={debug_arg(v, repr_arg)}" for k, v in bound.arguments.items()]
        print(f"{f.__name__}(")
        indent()
        print(*args_repr, sep=",\n", end=",\n")
        dedent()
        print("):")
        indent()
        result = f(*args, **kwargs)
        dedent()
        print(f"-> {result!r}")
        if "self" in sig.parameters:
            print("self=", debug_arg(bound.arguments["self"], repr_arg), sep="")
        return result
    return wrapper

def debug_cls(cls=None, *, ignore=None, **kwargs):
    if ignore is None:
        ignore = set()
    if cls is None:
        return lambda cls, **kw: debug_cls(cls, ignore=ignore, **kwargs, **kw)
    for attr_name in dir(cls):
        if attr_name in ignore:
            continue
        attr = getattr(cls, attr_name)
        if callable(attr) and not attr_name.startswith("__"):
            setattr(cls, attr_name, debug(attr, **kwargs))
    return cls

_tests = []
def test(f):
    name = f.__name__
    _tests.append(f)
    return f

def run_tests(skip_not_implemented=True):
    for f in _tests:
        name = f.__qualname__
        print(f"running: {name}...")
        indent()
        try:
            f()
            print("ok")
        except NotImplementedError as e:
            if not skip_not_implemented:
                print(f"failed: {name}: not implemented")
                raise e
            print(f"skipped: {name}: {e!r}")
            # exit(1)
        except Exception as e:
            print(f"failed: {name}: {e!r}")
            raise e
        finally:
            dedent()
    print(f"All tests passed!")

def expect_eq(got, expected):
    assert got == expected, f"\nexpected:\n{pf(expected)},\nbut got:\n{pf(got)}"

def reverse_dict[K, V](d: dict[K, V]) -> dict[V, K]:
    r = {}
    for k, v in d.items():
        if v in r:
            raise KeyError(f"Irreversible dict: Collision for {v}, dict: {d}")
        r[v] = k
    return r
