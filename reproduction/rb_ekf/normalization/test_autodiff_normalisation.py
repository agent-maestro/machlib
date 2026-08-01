"""`autodiff._normalise` must not change the function — the independent check ABOVE the AST.

This file exists because of the project's two-layer verification rule, applied to its first new
client. `_normalise` (`sp.cancel`) rewrites derivatives before they become AST. Everything
downstream -- the fixed-point golden, the bit-exact RTL comparison -- evaluates the *normalised*
AST, so none of it can see a mistake made here: golden and RTL would agree, on the wrong Jacobian.
That is the `x1*r` failure shape one layer up.

So the check has to be independent and exact:

    layer            check                                   catches
    source -> AST    THIS FILE: simplify(raw - normalised)   a bad cancellation
    AST    -> RTL    bit-exact golden vs simulated RTL       emission bugs

`_normalise` also self-validates at compile time (high-precision numeric agreement, falling back to
the un-normalised derivative on disagreement). These tests are the stronger symbolic version, run
over the derivative families that actually reach the backend.

THE DOMAIN SUBTLETY, pinned below rather than left implicit: cancellation legitimately WIDENS the
domain. `-x1/(x0^2 (1 + x1^2/x0^2))` is undefined at `x0 = 0`; its reduced form `-x1/(x0^2 + x1^2)`
is not. Equality is therefore asserted where BOTH forms are defined -- which is the contract the
hardware needs, since the reduced form is what gets emitted and it is defined strictly more often.
"""
from __future__ import annotations

import sympy as sp

from lang.optimizer.autodiff import _agrees_numerically, _normalise, jacobian_matrix
from lang.parser import parse_source
from lang.parser.ast_nodes import NodeKind

x0, x1 = sp.symbols("x0 x1", real=True)

# the derivative families that reach the backend, plus rational shapes with real cancellation
_EXPRS = [
    sp.diff(sp.sqrt(x0**2 + x1**2), x0),
    sp.diff(sp.sqrt(x0**2 + x1**2), x1),
    sp.diff(sp.atan(x1 / x0), x0),
    sp.diff(sp.atan(x1 / x0), x1),
    sp.diff(x0**2 - x1**2, x0),
    sp.diff(2 * x0 * x1, x1),
    (x0**2 - x1**2) / (x0 - x1),
    x1 / (x0**2 * (1 + x1**2 / x0**2)),
]


def test_normalise_preserves_the_function_symbolically():
    """Exact check: raw - normalised simplifies to zero."""
    for e in _EXPRS:
        d = sp.simplify(e - _normalise(e))
        assert d == 0, f"normalisation changed the function:\n  {e}\n  -> {_normalise(e)}\n  diff {d}"


def test_normalise_actually_reduces_the_range_bearing_jacobian():
    """Non-vacuity: if `cancel` stopped reducing anything, the tests above would still pass while
    the DSP win silently disappeared. Count negative powers -- the things that become reciprocals."""
    def npow(e):
        return sum(1 for a in sp.preorder_traversal(e) if a.is_Pow and a.exp.is_negative)

    raw = [sp.diff(o, v) for o in (sp.sqrt(x0**2 + x1**2), sp.atan(x1 / x0)) for v in (x0, x1)]
    assert sum(npow(e) for e in raw) > sum(npow(_normalise(e)) for e in raw), (
        "normalisation is no longer reducing the Jacobian -- the 242->200 DSP result depended on it")


def test_agreement_checker_rejects_a_wrong_rewrite():
    """The guard inside `_normalise` must be able to fail, or the fallback never triggers."""
    assert _agrees_numerically(x0 * x1, x1 * x0)
    assert not _agrees_numerically(x0 * x1, x0 + x1)
    assert not _agrees_numerically(sp.sqrt(x0**2 + x1**2), x0 + x1)


def test_cancellation_only_widens_the_domain_it_never_narrows_it():
    """The one semantic change normalisation is allowed to make.

    `cancel` removes a common factor, so the reduced form can be DEFINED where the raw one is not
    (x0 = 0 for the atan derivative). That direction is safe for emission -- the hardware evaluates
    the reduced form, which is total on strictly more inputs. The direction that would be unsafe is
    the reverse, and this pins that it does not happen: every point where the RAW form is defined,
    the reduced one is too, and they agree.
    """
    raw = sp.diff(sp.atan(x1 / x0), x0)
    red = _normalise(raw)
    for a, b in [(3, 4), (-2, 5), (7, -1), sp.Rational(1, 3).as_numer_denom()]:
        subs = {x0: sp.Integer(a), x1: sp.Integer(b)}
        rv, dv = raw.subs(subs), red.subs(subs)
        assert rv.is_finite and dv.is_finite
        assert sp.simplify(rv - dv) == 0, (a, b, rv, dv)
    # and the widening is real, not hypothetical
    assert not sp.diff(sp.atan(x1 / x0), x0).subs({x0: 0, x1: 1}).is_finite
    assert red.subs({x0: 0, x1: 1}).is_finite


def test_emitted_jacobian_ast_matches_the_unnormalised_derivative():
    """End-to-end at the AST boundary: what `jacobian_matrix` hands the backend is still the
    derivative, after normalisation."""
    fn = parse_source(
        "module t;\nfn h(x0: Real, x1: Real) -> (Real, Real) "
        "{ (sqrt(x0*x0 + x1*x1), atan(x1/x0)) }", "<t>").functions[0]
    J = jacobian_matrix(fn)

    def to_sympy(node):
        k = node.kind
        if k == NodeKind.LITERAL:
            return sp.Rational(str(node.value))
        if k == NodeKind.VAR:
            return sp.Symbol(str(node.value), real=True)
        if k == NodeKind.UNARYOP and node.value == "-":
            return -to_sympy(node.children[0])
        if k == NodeKind.SQRT:
            return sp.sqrt(to_sympy(node.children[0]))
        if k == NodeKind.ATAN:
            return sp.atan(to_sympy(node.children[0]))
        if k == NodeKind.POW:
            return to_sympy(node.children[0]) ** to_sympy(node.children[1])
        if k == NodeKind.BINOP:
            a, b = (to_sympy(c) for c in node.children)
            return {"+": a + b, "-": a - b, "*": a * b, "/": a / b}[node.value]
        raise AssertionError(k)

    h = [sp.sqrt(x0**2 + x1**2), sp.atan(x1 / x0)]
    for i, out in enumerate(h):
        for j, v in enumerate((x0, x1)):
            got = to_sympy(J[i][j])
            assert sp.simplify(got - sp.diff(out, v)) == 0, (i, j, got, sp.diff(out, v))
