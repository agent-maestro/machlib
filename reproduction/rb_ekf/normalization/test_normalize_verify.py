"""`normalize` — the first WHOLE-vector predicate verified end-to-end.

`ensures (dot(result, result) == 1.0)` is a claim about the ENTIRE result
vector (its squared norm is 1), not a per-component bound. One source:
  * C / WGSL: `v / sqrt(dot(v,v))` per component (WGSL division is native);
  * Lean: the goal `Σ (result i)² = 1` is discharged by MachLib
    `norm3_of_s` (Mathlib-free: div_def + mul_inv + mach_mpoly), proven
    sorryAx-free through the real `--check-lean` runner.

The proof that a `normalize` kernel produces a unit vector — the deepest
vector item, now real rather than staged.
"""

from __future__ import annotations

import ctypes
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

from lang.parser.ast_nodes import NodeKind
from lang.parser.parser import parse_source
from software.backends.c_backend import CBackend
from software.backends.wgsl_backend import WGSLBackend
from software.verification.lean.LeanBackend import LeanBackend

def _norm(n: int) -> str:
    return (
        '@verify(lean, theorem = "normalize_unit")\n'
        f"fn normalize(v: Vec<{n}>) -> Vec<{n}>\n"
        "  requires (dot(v, v) > 0.0)\n"
        "  ensures (dot(result, result) == 1.0)\n"
        "{ v / sqrt(dot(v, v)) }\n"
    )


_NORM = _norm(3)


def test_normalize_parses_as_vector_division() -> None:
    fn = parse_source(_NORM).functions[0]
    body = fn.body.children[-1]
    assert body.kind == NodeKind.BINOP and body.value == "/"
    # the ensures is the whole-vector unit-norm predicate
    assert LeanBackend._is_unit_norm_ensures(fn.ensures[0])


def test_normalize_lean_emits_unit_norm_proof() -> None:
    ln = LeanBackend().compile_module(parse_source(_NORM))
    assert "import MachLib.VectorError" in ln
    assert "noncomputable def normalize (v : (Fin 3 → Real)) : Fin 3 → Real" in ln
    assert "= (1 : Real) := by" in ln  # a whole-vector equation, not ∀ i
    # the inlined norm-of-s proof: div_def + mach_mpoly + mul_inv
    assert "sqrt_sq_nonneg" in ln and "sqrt_pos" in ln
    assert "mul_inv" in ln and "mach_mpoly" in ln


@pytest.mark.parametrize("n", [2, 4, 5])
def test_normalize_generalizes_beyond_3(n: int) -> None:
    """The proof is inlined + parameterised by N (mach_mpoly absorbs the
    arity), so normalize verifies at ANY dimension — not just 3."""
    ln = LeanBackend().compile_module(parse_source(_norm(n)))
    assert f"noncomputable def normalize (v : (Fin {n} → Real))" in ln
    # N distinct `div_def` rewrites, one per component
    assert ln.count("div_def (v ") == n
    assert "mach_mpoly" in ln


def test_normalize_c_and_wgsl_emit_division() -> None:
    c = CBackend().compile(parse_source(_NORM))
    assert "mg_vec3_t normalize(const double* v)" in c
    assert "v[0] / mg_sqrt(" in c
    w = WGSLBackend().compile(parse_source(_NORM))
    assert "-> vec3<f32>" in w
    assert "(v / sqrt(" in w  # WGSL vec3/scalar division is native


@pytest.mark.skipif(shutil.which("cc") is None, reason="needs a C compiler")
def test_normalize_c_runs_to_unit_vector() -> None:
    c = CBackend().compile(parse_source(_NORM))
    with tempfile.TemporaryDirectory() as d:
        src = Path(d) / "n.c"
        src.write_text(
            c
            + "\n#include <stdio.h>\n"
            "int main(void){ double v[3]={3.0,4.0,0.0};"
            " mg_vec3_t r = normalize(v);"
            " double sq = r.e[0]*r.e[0]+r.e[1]*r.e[1]+r.e[2]*r.e[2];"
            ' printf("%.10f %.10f %.10f\\n", r.e[0], r.e[1], sq); return 0; }\n'
        )
        exe = Path(d) / "n"
        inc = Path(__file__).resolve().parents[1] / "software" / "runtime" / "c"
        subprocess.run(
            ["cc", "-O2", f"-I{inc}", str(src), "-o", str(exe), "-lm"],
            check=True,
        )
        out = subprocess.run([str(exe)], capture_output=True, text=True, check=True)
        x, y, sq = (float(t) for t in out.stdout.split())
        assert abs(x - 0.6) < 1e-9 and abs(y - 0.8) < 1e-9
        assert abs(sq - 1.0) < 1e-9  # |normalize([3,4,0])|² = 1


@pytest.mark.skipif(shutil.which("lean") is None, reason="needs lean + MachLib")
@pytest.mark.parametrize("n", [2, 3, 4])
def test_normalize_unit_proves_sorry_free(n: int) -> None:
    """The unit-norm proof holds sorryAx-free at multiple dimensions —
    the ∀N generalisation, verified through the real --check-lean runner."""
    from tools.equivalence.lean_runner import LeanRunner, lake_available

    if not lake_available():
        pytest.skip("no lake/MachLib toolchain")
    res = LeanRunner(parse_source(_norm(n)), full_build=True).check("normalize")
    if not res.full_build_attempted:
        pytest.skip("full build not attempted")
    assert not res.has_sorry, res.error
    assert res.full_build_ok, res.error
