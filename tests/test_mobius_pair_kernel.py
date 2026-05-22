import json
import subprocess
import sys

import pytest

from tools.mobius_pair_kernel import (
    DomainError,
    alpha,
    alpha_mobius,
    beta,
    beta_mobius,
    event_volume,
    identity_product,
    mu_geo,
    mu_inv,
    shift,
)


def test_shift_works():
    assert shift(4) == 11


def test_alpha_valid():
    assert alpha(1) == pytest.approx(1 / 5)


def test_beta_valid():
    assert beta(1) == pytest.approx(5)


def test_identity_product_valid_samples():
    for value in [-10, -5, -2, -1, -0.5, 0.5, 1, 2, 5, 10]:
        assert identity_product(value) == pytest.approx(1)


def test_beta_guard_zero():
    with pytest.raises(DomainError):
        beta(0)


def test_alpha_guard_minus_three_halves():
    with pytest.raises(DomainError):
        alpha(-1.5)


def test_product_guard_zero():
    with pytest.raises(DomainError):
        identity_product(0)


def test_product_guard_minus_three_halves():
    with pytest.raises(DomainError):
        identity_product(-1.5)


def test_beta_mobius_form():
    assert beta_mobius(3) == pytest.approx(2 + 3 / 3)


def test_alpha_mobius_reciprocal_form():
    z = 3
    assert alpha_mobius(z) == pytest.approx(1 / (2 + 3 / z))


def test_mobius_guards():
    for fn, value in [(beta_mobius, 0), (alpha_mobius, 0), (alpha_mobius, -1.5)]:
        with pytest.raises(DomainError):
            fn(value)


def test_event_volume():
    assert event_volume(2) == {"k": 2, "m": 7, "n": 14}


def test_mu_geo():
    assert mu_geo(10) == 5


def test_mu_inv():
    assert mu_inv(10) == pytest.approx(1 / 20)


def test_mu_inv_guard():
    with pytest.raises(DomainError):
        mu_inv(0)


def test_cli_sample_output(tmp_path):
    subprocess.run([sys.executable, "tools/mobius_pair_kernel.py", "--out-dir", str(tmp_path), "--strict"], check=True)
    samples = json.loads((tmp_path / "mobius_pair_samples_2026_05_21.json").read_text())
    assert any(row["status"] == "PASS" for row in samples["samples"])


def test_cli_singularity_output(tmp_path):
    subprocess.run([sys.executable, "tools/mobius_pair_kernel.py", "--out-dir", str(tmp_path), "--strict"], check=True)
    guards = json.loads((tmp_path / "mobius_pair_singularity_guards_2026_05_21.json").read_text())
    assert guards["guard_status"] == "PASS"


def test_cli_limit_output(tmp_path):
    subprocess.run([sys.executable, "tools/mobius_pair_kernel.py", "--out-dir", str(tmp_path), "--strict"], check=True)
    limits = json.loads((tmp_path / "mobius_pair_limits_2026_05_21.json").read_text())
    assert limits["rows"][-1]["alpha_error_from_half"] < limits["rows"][0]["alpha_error_from_half"]
    assert limits["rows"][-1]["beta_error_from_two"] < limits["rows"][0]["beta_error_from_two"]


def test_strict_output_has_no_public_claims(tmp_path):
    subprocess.run([sys.executable, "tools/mobius_pair_kernel.py", "--out-dir", str(tmp_path), "--strict"], check=True)
    spec = json.loads((tmp_path / "mobius_pair_spec_2026_05_21.json").read_text())
    for key in ["public_ready", "theorem_proof_claim", "physics_claim", "certified_safety_claim"]:
        assert spec[key] is False
