import json
import math
from pathlib import Path

import pytest

from tools.operator_senses_factory import (
    DomainError,
    Kernel,
    alpha,
    alpha_mobius,
    beta,
    beta_mobius,
    event_volume,
    generate_kernels,
    identity_product,
    mu_geo,
    mu_inv,
    run,
    sample_kernel,
    shift,
)


def test_affine_shift():
    assert shift(Kernel("k", 2, 3), 4) == 11


@pytest.mark.parametrize("kernel", generate_kernels(25))
def test_identity_product(kernel):
    assert identity_product(kernel, 11) == pytest.approx(1.0)


@pytest.mark.parametrize("kernel", generate_kernels(25))
def test_x_zero_guard(kernel):
    with pytest.raises(DomainError):
        beta(kernel, 0)


@pytest.mark.parametrize("kernel", generate_kernels(25))
def test_shift_singularity_guard(kernel):
    with pytest.raises(DomainError):
        alpha(kernel, kernel.singularity)


@pytest.mark.parametrize("kernel", generate_kernels(25)[:8])
def test_mobius_beta(kernel):
    assert beta_mobius(kernel, 7) == pytest.approx(kernel.a + kernel.b / 7)


@pytest.mark.parametrize("kernel", generate_kernels(25)[:8])
def test_mobius_alpha(kernel):
    assert alpha_mobius(kernel, 7) == pytest.approx(1 / (kernel.a + kernel.b / 7))


@pytest.mark.parametrize("kernel", generate_kernels(25)[:8])
def test_limit_numeric_behavior(kernel):
    assert alpha(kernel, 10000) == pytest.approx(1 / kernel.a, rel=1e-3)
    assert beta(kernel, 10000) == pytest.approx(kernel.a, rel=1e-3)


def test_event_volume():
    assert event_volume(Kernel("k", 3, -2), 5) == {"k": 5, "m": 13, "n": 65}


def test_gauges():
    kernel = Kernel("k", 2, 3)
    assert mu_geo(kernel, 8) == 4
    assert mu_inv(kernel, 4) == 0.125


def test_mu_inv_guard():
    with pytest.raises(DomainError):
        mu_inv(Kernel("k", 2, 3), 0)


def test_catalog_includes_seed():
    kernels = generate_kernels(25)
    assert any(k.a == 2 and k.b == 3 for k in kernels)


def test_negative_a_kernels_present():
    assert any(k.a < 0 for k in generate_kernels(25))


def test_negative_b_kernels_present():
    assert any(k.b < 0 for k in generate_kernels(25))


def test_sample_kernel_counts():
    samples, guards, limits, events = sample_kernel(Kernel("k", 2, 3))
    assert len(samples) >= 20
    assert len(guards) == 4
    assert len(limits) == 4
    assert len(events) >= 20


def test_run_outputs(tmp_path):
    result = run(tmp_path / "out", 25, Path("."))
    assert result["kernel_count"] >= 25
    assert result["sample_check_count"] >= 500
    assert result["guard_check_count"] >= 100
    assert result["status"] == "PASS"


def test_execution_json_no_public_claims(tmp_path):
    run(tmp_path / "out", 25, Path("."))
    data = json.loads((tmp_path / "out/operator_kernel_execution_result_2026_05_21.json").read_text())
    assert data["theorem_proof_claim"] is False
    assert data["physics_claim"] is False
    assert data["public_claim"] is False
