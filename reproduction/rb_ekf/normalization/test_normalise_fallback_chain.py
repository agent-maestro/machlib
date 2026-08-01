"""FORCED-FAILURE SPECIMEN for the normalisation fallback -- the whole chain, not just the assert.

WHY THE CHAIN AND NOT THE ASSERT. `assert_normalised_cleanly` is the least likely link to be broken;
it is four lines. The failures this project has actually shipped were always one link over:

  * the ROM gate fired INVERTED -- FAIL on good data, `value-mismatches = 0`
  * the sorry-audit canary NEVER FIRED -- it landed outside the `MachLib` namespace the walk filters
  * and here, found while writing this test: **`assert_normalised_cleanly` is called by NOTHING.**
    Two documents call it "the gate"; the shipping path does not invoke it. A build that forgets to
    call it emits the expensive form and publishes the cheap number.

So the test injects at the top and asserts every link down to the process exit code.

THE INJECTION IS PLAUSIBLE-WRONG, NOT GARBAGE. `cancel` is replaced by something that returns a
well-formed expression which is *not* equal to its input -- wrong in a way only the numeric
validator can catch. Garbage would be caught by SymPy itself and would prove nothing about the
validator.

TWO SPECIMENS FOR ONE INJECTION: this is also the first observed firing of `_agrees_numerically`,
which has likewise never been seen to reject anything.
"""
from __future__ import annotations

import subprocess
import sys
import warnings
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lang.optimizer import autodiff  # noqa: E402

FORGE = Path(__file__).resolve().parents[1]


def _plausible_wrong(e):
    """A well-formed expression that is NOT equal to `e`. Only the numeric check can tell."""
    syms = sorted(e.free_symbols, key=str)
    if not syms:
        return e + sp.Integer(1)
    # perturb one symbol's coefficient: structurally sane, numerically wrong
    return e.subs(syms[0], syms[0] * sp.Rational(1000001, 1000000))


@pytest.fixture(autouse=True)
def _clean_fallbacks():
    autodiff.NORMALISE_FALLBACKS.clear()
    yield
    autodiff.NORMALISE_FALLBACKS.clear()


def test_link1_validator_actually_rejects_a_plausible_wrong_rewrite():
    """SPECIMEN for `_agrees_numerically` -- never before observed rejecting anything."""
    x, y = sp.symbols("x y", positive=True)
    good = -y / (x**2 + y**2)
    assert autodiff._agrees_numerically(good, good), "validator must accept an identity"
    assert not autodiff._agrees_numerically(good, _plausible_wrong(good)), \
        "validator must REJECT a plausible-but-wrong rewrite -- this is the firing specimen"


def test_link2_to_4_fallback_reverts_warns_and_records(monkeypatch):
    """The rewrite is refused, the un-normalised form is returned, it warns, and it is recorded."""
    x, y = sp.symbols("x y", positive=True)
    raw = sp.diff(sp.atan(y / x), x)
    monkeypatch.setattr(autodiff.sp, "cancel", _plausible_wrong)

    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        out = autodiff._normalise(raw)

    assert out == raw, "link 2: must REVERT to the un-normalised derivative"
    assert autodiff.NORMALISE_FALLBACKS, "link 3: must be RECORDED in NORMALISE_FALLBACKS"
    assert any("UN-NORMALISED" in str(w.message) for w in caught), "link 4: must WARN"
    assert any(str(raw)[:12] in str(w.message) for w in caught), \
        "link 4: the warning must NAME the derivative, not just complain"


def test_link5_assert_raises_once_a_fallback_is_recorded():
    autodiff.NORMALISE_FALLBACKS.append(("d/dx atan(y/x)", "injected"))
    with pytest.raises(autodiff.AutodiffError):
        autodiff.assert_normalised_cleanly()


def test_link6_the_shipping_path_exits_nonzero():
    """THE LINK THE AUDIT CANARY TEACHES YOU TO DISTRUST.

    An assert that exists but is never CALLED on the path that publishes resource numbers is not a
    gate. This drives the real CLI in a subprocess with `cancel` broken and requires a non-zero exit.
    """
    inject = (
        "import sympy, sys; import lang.optimizer.autodiff as ad;"
        "_pw=lambda e:(e if not e.free_symbols else"
        " e.subs(sorted(e.free_symbols,key=str)[0],"
        " sorted(e.free_symbols,key=str)[0]*sympy.Rational(1000001,1000000)));"
        "sympy.cancel=_pw; ad.sp.cancel=_pw;"
        "sys.argv=['eml-compile','examples/ekf_range_bearing.eml','--target','verilog'];"
        "import tools.cli.main as m; sys.exit(m.main())"
    )
    r = subprocess.run([sys.executable, "-c", inject], cwd=FORGE, capture_output=True,
                       text=True, timeout=900, env={"PYTHONPATH": str(FORGE), "PATH": "/usr/bin:/bin"})
    assert r.returncode != 0, (
        "SHIPPING PATH DID NOT FAIL with normalisation broken. The emitted design is the EXPENSIVE "
        "form while every published DSP number describes the cheap one. "
        f"exit={r.returncode}\nstdout tail:\n{r.stdout[-400:]}\nstderr tail:\n{r.stderr[-600:]}"
    )
