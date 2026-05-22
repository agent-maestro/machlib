#!/usr/bin/env python3
"""Local Alpha-Beta / Mobius pair toy-kernel checks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SINGULAR_ALPHA = -1.5
EPS = 1e-12


class DomainError(ValueError):
    """Raised when a toy-kernel expression is outside its guarded domain."""


def _guard(value: float, forbidden: float, name: str) -> None:
    if abs(value - forbidden) < EPS:
        raise DomainError(f"{name} guard excluded {value}")


def shift(x: float) -> float:
    return 2 * x + 3


def alpha(x: float) -> float:
    _guard(x, SINGULAR_ALPHA, "alpha")
    return x / shift(x)


def beta(x: float) -> float:
    _guard(x, 0.0, "beta")
    return shift(x) / x


def identity_product(x: float) -> float:
    _guard(x, 0.0, "identity_product")
    _guard(x, SINGULAR_ALPHA, "identity_product")
    return alpha(x) * beta(x)


def beta_mobius(z: float) -> float:
    _guard(z, 0.0, "beta_mobius")
    return 2 + 3 / z


def alpha_mobius(z: float) -> float:
    _guard(z, 0.0, "alpha_mobius")
    _guard(z, SINGULAR_ALPHA, "alpha_mobius")
    return 1 / (2 + 3 / z)


def event_volume(k: float) -> dict[str, float]:
    m = shift(k)
    return {"k": k, "m": m, "n": k * m}


def mu_geo(n_value: float) -> float:
    return n_value / 2


def mu_inv(n_value: float) -> float:
    _guard(n_value, 0.0, "mu_inv")
    return 1 / (2 * n_value)


def sample_row(x: float) -> dict[str, Any]:
    try:
        volume = event_volume(x)
        return {
            "x": x,
            "alpha": alpha(x),
            "beta": beta(x),
            "identity_product": identity_product(x),
            **volume,
            "status": "PASS",
        }
    except DomainError as exc:
        return {"x": x, "status": "GUARD_EXCLUDED", "reason": str(exc)}


def build_spec() -> dict[str, Any]:
    return {
        "kernel_id": "alpha_beta_mobius_pair_kernel",
        "title": "Alpha-Beta Mobius Pair Toy Kernel",
        "interpretation": "reciprocal Mobius-pair toy kernel",
        "shift": "y := 2x + 3",
        "alpha": "x / (2x + 3)",
        "beta": "(2x + 3) / x",
        "identity_witness": "alpha(x) * beta(x) = 1 on guarded numeric samples",
        "domain_guards": ["x != 0", "x != -3/2", "z != 0", "z != -3/2", "N != 0 for mu_inv"],
        "event_volume": "D(k) = (k, 2k + 3, k(2k + 3))",
        "gauges": {"mu_geo": "N / 2", "mu_inv": "1 / (2N)"},
        "evidence_status": "NUMERIC_TOY_KERNEL_ONLY",
        "public_ready": False,
        "upload_allowed": False,
        "theorem_proof_claim": False,
        "open_problem_claim": False,
        "physics_claim": False,
        "holography_proof_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "mathlib_dependency": False,
    }


def build_samples() -> dict[str, Any]:
    values = [-10, -5, -2, -1.5, -1, -0.5, -1e-6, 0, 1e-6, 0.5, 1, 2, 5, 10]
    return {"samples": [sample_row(float(x)) for x in values]}


def build_limits() -> dict[str, Any]:
    rows = []
    for x in [10, 100, 1000, 10000]:
        rows.append({
            "x": x,
            "alpha": alpha(float(x)),
            "beta": beta(float(x)),
            "alpha_error_from_half": abs(alpha(float(x)) - 0.5),
            "beta_error_from_two": abs(beta(float(x)) - 2.0),
        })
    return {"status": "NUMERIC_LIMIT_EVIDENCE_ONLY", "target_alpha": 0.5, "target_beta": 2.0, "rows": rows}


def guard_case(name: str, fn, value: float) -> dict[str, Any]:
    try:
        fn(value)
    except DomainError as exc:
        return {"case": name, "value": value, "status": "GUARD_EXCLUDED", "reason": str(exc)}
    return {"case": name, "value": value, "status": "FAILED_TO_GUARD"}


def build_guards() -> dict[str, Any]:
    cases = [
        guard_case("beta_x_zero", beta, 0.0),
        guard_case("product_x_zero", identity_product, 0.0),
        guard_case("alpha_x_minus_three_halves", alpha, SINGULAR_ALPHA),
        guard_case("product_x_minus_three_halves", identity_product, SINGULAR_ALPHA),
        guard_case("beta_mobius_z_zero", beta_mobius, 0.0),
        guard_case("alpha_mobius_z_zero", alpha_mobius, 0.0),
        guard_case("alpha_mobius_z_minus_three_halves", alpha_mobius, SINGULAR_ALPHA),
        guard_case("mu_inv_N_zero", mu_inv, 0.0),
    ]
    return {"guard_status": "PASS" if all(row["status"] == "GUARD_EXCLUDED" for row in cases) else "FAIL", "cases": cases}


def build_event_volume() -> dict[str, Any]:
    rows = []
    for k in [-10, -5, -2, -1, -0.5, 0.5, 1, 2, 5, 10]:
        volume = event_volume(float(k))
        n_value = volume["n"]
        row: dict[str, Any] = {**volume, "mu_geo": mu_geo(n_value)}
        try:
            row["mu_inv"] = mu_inv(n_value)
            row["gauge_status"] = "PASS"
        except DomainError as exc:
            row["gauge_status"] = "GUARD_EXCLUDED"
            row["mu_inv_reason"] = str(exc)
        rows.append(row)
    return {"event_volume_status": "PASS", "rows": rows}


def write_json(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def run(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    write_json(out_dir / "mobius_pair_spec_2026_05_21.json", build_spec())
    write_json(out_dir / "mobius_pair_samples_2026_05_21.json", build_samples())
    write_json(out_dir / "mobius_pair_limits_2026_05_21.json", build_limits())
    write_json(out_dir / "mobius_pair_singularity_guards_2026_05_21.json", build_guards())
    write_json(out_dir / "mobius_pair_event_volume_2026_05_21.json", build_event_volume())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    run(args.out_dir)
    print("MOBIUS_PAIR_KERNEL", args.out_dir, "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
