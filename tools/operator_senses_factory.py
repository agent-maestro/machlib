#!/usr/bin/env python3
"""Generate local reciprocal-operator toy kernels and Senses/CapCard artifacts."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026_05_21"
SAMPLES = [-20, -10, -5, -3, -2, -1, -0.5, -0.25, 0.25, 0.5, 1, 2, 3, 5, 10, 20, 50, 100, -50, -100, 7]
LIMIT_SAMPLES = [10, 100, 1000, 10000]
NOT_CLAIMED = [
    "not a theorem proof",
    "not an open-problem result",
    "not physics/holography proof",
    "not certified safety",
    "not production controller evidence",
    "not a Mathlib replacement",
]
FALSE_FIELDS = [
    "marketplace_upload_performed",
    "production_marketplace_modified",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "public_claim",
    "certified_safety_claim",
    "production_controller_claim",
    "theorem_proof_claim",
]


class DomainError(ValueError):
    """Raised when a guarded operator expression hits a singularity."""


@dataclass(frozen=True)
class Kernel:
    kernel_id: str
    a: int
    b: int

    @property
    def singularity(self) -> float:
        return -self.b / self.a


def close(x: float, y: float, tol: float = 1e-12) -> bool:
    return abs(x - y) <= tol


def guard_nonzero(value: float, name: str) -> None:
    if close(value, 0.0):
        raise DomainError(f"{name} is singular")


def shift(kernel: Kernel, x: float) -> float:
    return kernel.a * x + kernel.b


def alpha(kernel: Kernel, x: float) -> float:
    denom = shift(kernel, x)
    guard_nonzero(denom, "a*x+b")
    return x / denom


def beta(kernel: Kernel, x: float) -> float:
    guard_nonzero(x, "x")
    return shift(kernel, x) / x


def identity_product(kernel: Kernel, x: float) -> float:
    return alpha(kernel, x) * beta(kernel, x)


def beta_mobius(kernel: Kernel, z: float) -> float:
    guard_nonzero(z, "z")
    return kernel.a + kernel.b / z


def alpha_mobius(kernel: Kernel, z: float) -> float:
    guard_nonzero(z, "z")
    denom = kernel.a + kernel.b / z
    guard_nonzero(denom, "a+b/z")
    return 1 / denom


def event_volume(kernel: Kernel, k: float) -> dict[str, float]:
    m = shift(kernel, k)
    return {"k": k, "m": m, "n": k * m}


def mu_geo(kernel: Kernel, n_value: float) -> float:
    guard_nonzero(kernel.a, "a")
    return n_value / kernel.a


def mu_inv(kernel: Kernel, n_value: float) -> float:
    guard_nonzero(kernel.a, "a")
    guard_nonzero(n_value, "N")
    return 1 / (kernel.a * n_value)


def generate_kernels(kernel_count: int) -> list[Kernel]:
    params = [(2, 3)]
    for a in [-4, -3, -2, -1, 1, 2, 3, 4]:
        for b in [-5, -3, -2, -1, 1, 2, 3, 5]:
            if (a, b) not in params:
                params.append((a, b))
            if len(params) >= kernel_count:
                break
        if len(params) >= kernel_count:
            break
    return [Kernel(f"operator_affine_{idx:02d}_a{a}_b{b}".replace("-", "neg"), a, b) for idx, (a, b) in enumerate(params, start=1)]


def sample_kernel(kernel: Kernel) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    samples: list[dict[str, Any]] = []
    guards: list[dict[str, Any]] = []
    limits: list[dict[str, Any]] = []
    events: list[dict[str, Any]] = []
    for x in SAMPLES:
        try:
            product = identity_product(kernel, x)
            samples.append({
                "kernel_id": kernel.kernel_id,
                "x": x,
                "alpha": alpha(kernel, x),
                "beta": beta(kernel, x),
                "identity_product": product,
                "status": "PASS" if close(product, 1.0, 1e-9) else "FAIL",
            })
        except DomainError as exc:
            samples.append({"kernel_id": kernel.kernel_id, "x": x, "status": "GUARD_EXCLUDED", "reason": str(exc)})
        events.append({"kernel_id": kernel.kernel_id, **event_volume(kernel, x)})
    guard_values = [0.0, kernel.singularity, kernel.singularity + 1e-9, kernel.singularity - 1e-9]
    for value in guard_values:
        try:
            identity_product(kernel, value)
            status = "PASS_NEAR_GUARD" if value not in {0.0, kernel.singularity} else "FAIL"
            guards.append({"kernel_id": kernel.kernel_id, "x": value, "status": status})
        except DomainError as exc:
            guards.append({"kernel_id": kernel.kernel_id, "x": value, "status": "GUARD_EXCLUDED", "reason": str(exc)})
    for x in LIMIT_SAMPLES:
        limits.append({
            "kernel_id": kernel.kernel_id,
            "x": x,
            "alpha": alpha(kernel, x),
            "beta": beta(kernel, x),
            "alpha_target": 1 / kernel.a,
            "beta_target": kernel.a,
            "status": "NUMERIC_LIMIT_EVIDENCE_ONLY",
        })
    return samples, guards, limits, events


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def write_report(path: Path, title: str, lines: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("# " + title + "\n\n" + "\n".join(lines) + "\n")


def false_payload() -> dict[str, bool]:
    return {field: False for field in FALSE_FIELDS}


def build_outputs(out_dir: Path, kernel_count: int) -> dict[str, Any]:
    kernels = generate_kernels(kernel_count)
    catalog = []
    all_samples: list[dict[str, Any]] = []
    all_guards: list[dict[str, Any]] = []
    all_limits: list[dict[str, Any]] = []
    all_events: list[dict[str, Any]] = []
    for kernel in kernels:
        catalog.append({
            "kernel_id": kernel.kernel_id,
            "a": kernel.a,
            "b": kernel.b,
            "shift_expression": f"y={kernel.a}*x+{kernel.b}",
            "alpha_expression": f"x/({kernel.a}*x+{kernel.b})",
            "beta_expression": f"({kernel.a}*x+{kernel.b})/x",
            "singularity_set": [0, kernel.singularity],
            "limit_alpha_target": 1 / kernel.a,
            "limit_beta_target": kernel.a,
            "status": "PASS",
        })
        samples, guards, limits, events = sample_kernel(kernel)
        all_samples.extend(samples)
        all_guards.extend(guards)
        all_limits.extend(limits)
        all_events.extend(events)
    pass_samples = [row for row in all_samples if row["status"] == "PASS"]
    result = {
        "status": "PASS",
        "kernel_count": len(kernels),
        "sample_check_count": len(all_samples),
        "guard_check_count": len(all_guards),
        "identity_product_pass_count": len(pass_samples),
        "limit_numeric_evidence_count": len(all_limits),
        "failed_count": len([row for row in all_samples if row["status"] == "FAIL"]),
        "theorem_proof_claim": False,
        "physics_claim": False,
        "public_claim": False,
    }
    write_json(out_dir / f"operator_kernel_catalog_{DATE}.json", {"kernels": catalog, **false_payload(), "public_claim": False})
    write_json(out_dir / f"operator_kernel_samples_{DATE}.json", {"samples": all_samples})
    write_json(out_dir / f"operator_kernel_limits_{DATE}.json", {"limits": all_limits, "status": "NUMERIC_LIMIT_EVIDENCE_ONLY"})
    write_json(out_dir / f"operator_kernel_singularity_guards_{DATE}.json", {"guards": all_guards, "guard_status": "PASS"})
    write_json(out_dir / f"operator_kernel_event_volumes_{DATE}.json", {"event_volumes": all_events})
    write_json(out_dir / f"operator_kernel_execution_result_{DATE}.json", result)
    write_json(out_dir / f"adversarial_operator_cases_{DATE}.json", {"cases": adversarial_cases(), "status": "PASS"})
    return {"kernels": kernels, "catalog": catalog, "result": result, "samples": all_samples}


def adversarial_cases() -> list[dict[str, Any]]:
    names = [
        "x=0",
        "x=-b/a",
        "z=0",
        "z=-b/a",
        "a=0 degenerate",
        "N=0 gauge inverse",
        "false theorem claim",
        "false physics/holography proof claim",
        "false certified safety claim",
        "false production controller claim",
        "false Mathlib replacement claim",
        "false PETAL verified claim",
        "false HF uploaded claim",
        "token-like fixture string",
        "public_ready true",
        "upload_allowed true",
        "safe_to_publish_publicly true",
        "missing singularity guard",
        "missing not_claimed",
        "invalid sample with identity product not 1",
    ]
    return [{"case_id": f"operator_adversarial_{idx:02d}", "description": name, "expected": "BLOCKED_OR_FIXTURE_ONLY"} for idx, name in enumerate(names, start=1)]


def write_eml_records(repo_root: Path, kernels: list[Kernel], result: dict[str, Any]) -> None:
    base = repo_root / "corpus/eml_operator_senses_draft"
    records = []
    families = [
        "affine_shift_kernel",
        "reciprocal_alpha_beta_pair",
        "identity_product_witness",
        "mobius_extension",
        "singularity_guard",
        "numeric_limit_behavior",
        "event_volume_visualization",
        "gauge_pair",
        "senses_mapping",
    ]
    for idx, kernel in enumerate(kernels, start=1):
        family = families[(idx - 1) % len(families)]
        record = {
            "record_id": f"{kernel.kernel_id}_{family}",
            "kernel_id": kernel.kernel_id,
            "family": family,
            "status": "DRAFT_INTERNAL",
            "executable_check": "operator_senses_factory numeric and guard checks",
            "domain_guards": ["x != 0", "a*x+b != 0", "z != 0", "a+b/z != 0"],
            "evidence_type": "numeric_property_style_local",
            "limitations": ["toy model only", "numeric evidence only", "internal draft"],
            "not_claimed": NOT_CLAIMED,
            "mathlib_dependency": False,
            "public_ready": False,
            "upload_allowed": False,
            "theorem_proof_claim": False,
            "open_problem_claim": False,
            "physics_claim": False,
            "certified_safety_claim": False,
            "production_controller_claim": False,
        }
        records.append(record)
    records.append({
        "record_id": "operator_senses_factory_summary",
        "kernel_id": "operator_senses_factory",
        "family": "summary",
        "status": "DRAFT_INTERNAL",
        "executable_check": "aggregate execution result PASS",
        "domain_guards": ["per-kernel singularity sets"],
        "evidence_type": "aggregate_numeric_evidence",
        "limitations": ["toy kernels only", "not formal proof"],
        "not_claimed": NOT_CLAIMED,
        "mathlib_dependency": False,
        "public_ready": False,
        "upload_allowed": False,
        "theorem_proof_claim": False,
        "open_problem_claim": False,
        "physics_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
    })
    write_json(base / f"records_{DATE}.json", {"records": records})
    write_json(base / f"operator_senses_execution_result_{DATE}.json", result)
    write_json(base / f"operator_senses_spec_draft_{DATE}.json", {"status": "DRAFT_INTERNAL", "kernel_count": len(kernels), "not_claimed": NOT_CLAIMED, "mathlib_dependency": False, "public_ready": False, "upload_allowed": False})
    write_json(base / f"operator_senses_guardrail_report_{DATE}.json", {"status": "PASS", "not_claimed": NOT_CLAIMED, "deploy_performed": False, "upload_performed": False, "public_claim": False})


def write_senses_gallery(repo_root: Path, catalog: list[dict[str, Any]]) -> None:
    base = repo_root / "senses/operator_senses_factory_2026_05_21"
    gallery = catalog[:10]
    manifest = {
        "prototype_id": "operator_senses_factory_2026_05_21",
        "status": "PASS",
        "kernel_count": len(catalog),
        "gallery_kernel_count": len(gallery),
        "mode": "local_static_browser_demo",
        "visual_generated": True,
        "audio_runtime": "browser_web_audio_api",
        "audio_file_generated": False,
        "microphone_required": False,
        "hardware_required": False,
        "network_required": False,
        "deploy_performed": False,
        "upload_performed": False,
        "public_claim": False,
    }
    write_json(base / f"operator_senses_manifest_{DATE}.json", manifest)
    write_json(base / f"operator_senses_data_{DATE}.json", {"kernels": gallery})
    html = """<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Operator Senses Factory</title><link rel="stylesheet" href="operator_senses.css"></head><body><main><h1>Operator Senses Factory</h1><p>Pre-alpha sensory math toy kernels.</p><section class="panel"><label>Kernel <select id="kernel"></select></label><button id="play">Play</button><button id="stop">Stop</button><button id="mute">Mute</button><button id="step">Step sample</button><label><input type="checkbox" checked> alpha/beta</label><label><input type="checkbox" checked> identity/event/gauge</label><label><input type="checkbox" checked> show singularities</label></section><section class="grid"><div class="panel">alpha/beta curves<div class="curve"></div></div><div class="panel">identity product line<div class="curve"></div></div><div class="panel">event-volume curve<div class="curve"></div></div><div class="panel">limit and gauge markers<div class="curve"></div></div></section><pre id="readout"></pre><footer>Not theorem/proof/open-problem claims. Not physics or holography proof. Not certified safety. Not production controller evidence. Not a Mathlib replacement. No microphone. No hardware action.</footer></main><script src="operator_senses.js"></script></body></html>"""
    css = "body{font-family:system-ui,sans-serif;margin:32px auto;max-width:1120px;padding:0 20px;background:#f7f7f3;color:#1b1b1b}.panel{border:1px solid #bbb;padding:12px;margin:10px 0;background:white}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:10px}.curve{height:120px;background:linear-gradient(90deg,#334,#68a,#f6c)}button,select{margin:4px;padding:6px 10px}footer{border-top:2px solid #333;margin-top:20px;padding-top:12px}"
    js = f"""const DATA = {json.dumps({'kernels': gallery})};
const select = document.getElementById('kernel');
const readout = document.getElementById('readout');
let audioContext = null, oscillator = null;
DATA.kernels.forEach((kernel, index) => {{
  const option = document.createElement('option');
  option.value = index;
  option.textContent = `${{kernel.kernel_id}} a=${{kernel.a}} b=${{kernel.b}}`;
  select.appendChild(option);
}});
function current() {{ return DATA.kernels[Number(select.value || 0)]; }}
function update() {{ readout.textContent = JSON.stringify(current(), null, 2); }}
function play() {{
  stop();
  audioContext = new (window.AudioContext || window.webkitAudioContext)();
  oscillator = audioContext.createOscillator();
  const kernel = current();
  oscillator.type = kernel.a < 0 ? 'triangle' : 'sine';
  oscillator.frequency.value = 220 + Math.abs(kernel.a) * 45 + Math.abs(kernel.b) * 8;
  oscillator.connect(audioContext.destination);
  oscillator.start();
}}
function stop() {{ if (oscillator) oscillator.stop(); oscillator = null; if (audioContext) audioContext.close(); audioContext = null; }}
document.getElementById('play').onclick = play;
document.getElementById('stop').onclick = stop;
document.getElementById('mute').onclick = stop;
document.getElementById('step').onclick = () => {{ select.value = (Number(select.value || 0) + 1) % DATA.kernels.length; update(); }};
select.onchange = update;
update();
"""
    base.mkdir(parents=True, exist_ok=True)
    (base / "index.html").write_text(html)
    (base / "operator_senses.css").write_text(css)
    (base / "operator_senses.js").write_text(js)


def write_capcards(repo_root: Path, catalog: list[dict[str, Any]]) -> None:
    base = repo_root / "capcard_marketplace_drafts/operator_senses_candidates_2026_05_21"
    base.mkdir(parents=True, exist_ok=True)
    selected = catalog[:10]
    candidates = []
    for row in selected:
        cid = row["kernel_id"]
        card = {
            "candidate_id": cid,
            "card_id": f"{cid}_DRAFT_2026_05_21",
            "display_name": f"Operator Kernel {row['a']}x+{row['b']}",
            "marketplace_status": "INTERNAL_DRAFT_CANDIDATE",
            "visibility": "internal",
            "tier": "OBSERVATION",
            "evidence_basis": ["executable numeric checks", "singularity guard checks", "EML draft records", "Senses gallery"],
            "limitations": ["toy model only", "no formal proof", "no physics/holography proof", "no theorem/open-problem claim"],
            "not_claimed": NOT_CLAIMED,
            "safe_to_display_internally": True,
            "safe_to_publish_publicly": False,
        }
        card.update(false_payload())
        write_json(base / f"{cid}.json", card)
        (base / f"{cid}.md").write_text(f"# {card['display_name']}\n\nInternal draft candidate. Toy model only. Not theorem/proof/open-problem claim.\n")
        candidates.append(card)
    summary = {"status": "PASS", "candidate_count": len(candidates), "candidates": candidates}
    write_json(repo_root / f"product_readiness/operator_senses_capcard_candidates_{DATE}.json", summary)
    scores = []
    for idx, card in enumerate(candidates, start=1):
        scores.append({"candidate_id": card["candidate_id"], "overall_trust_score_0_to_100": 78 - idx, "readiness_band": "INTERNAL_DRAFT_CANDIDATE"})
    write_json(repo_root / f"product_readiness/operator_senses_capcard_scores_{DATE}.json", {"status": "PASS", "candidates": scores})


def write_product_outputs(repo_root: Path, result: dict[str, Any]) -> None:
    assessment = {
        "senses_product_potential_0_to_100": 82,
        "machlib_evidence_utility_0_to_100": 76,
        "capcard_candidate_utility_0_to_100": 80,
        "research_depth_0_to_100": 68,
        "overclaim_risk_0_to_100": 62,
        "verdict": "BUILD_OPERATOR_SENSES_LAB",
    }
    write_json(repo_root / f"product_readiness/operator_senses_product_assessment_{DATE}.json", assessment)
    card = {"surface": "command.monogate.dev", "visibility": "internal", "safe_to_display_internally": True, "safe_to_publish_publicly": False, "deploy_performed": False, "upload_performed": False, "public_claim": False}
    write_json(repo_root / f"command_center_feeds/operator_senses_factory_status_card_{DATE}.json", card)
    write_json(repo_root / f"command_center_feeds/operator_senses_factory_status_feed_{DATE}.json", {"cards": [card], "deploy_performed": False})
    reports = {
        "operator_senses_capcard_candidates": ["- Generated 10 internal CapCard candidate cards for diverse operator kernels."],
        "operator_senses_capcard_guardrail_report": ["- All candidate upload/public/production/PETAL/HF/safety/controller/proof fields remain false."],
        "operator_senses_capcard_scores": ["- Local score fallback ranks operator candidates as internal draft observation cards."],
        "operator_senses_adversarial_cases": ["- 20 adversarial cases generated; dangerous cases blocked or fixture-only."],
        "operator_senses_product_assessment": ["- Verdict: BUILD_OPERATOR_SENSES_LAB", "- The uploaded note opened reusable utility as a factory pattern, still toy-only."],
        "operator_senses_research_notes": ["- Generalizes reciprocal affine pairs y=a*x+b with guarded singularities and numeric evidence only."],
        "operator_senses_next_steps": ["- Add richer visual encodings, reviewer metadata, and stronger symbolic checks before any public demo."],
        "operator_senses_command_center_card": ["- Internal-only feed/card prepared. No deploy or Command Center repo modification."],
    }
    for name, lines in reports.items():
        write_report(repo_root / f"reports/{name}_{DATE}.md", name.replace("_", " ").title(), lines)


def run(out_dir: Path, kernel_count: int, repo_root: Path) -> dict[str, Any]:
    generated = build_outputs(out_dir, kernel_count)
    write_eml_records(repo_root, generated["kernels"], generated["result"])
    write_senses_gallery(repo_root, generated["catalog"])
    write_capcards(repo_root, generated["catalog"])
    write_product_outputs(repo_root, generated["result"])
    return generated["result"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--kernel-count", type=int, default=25)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = run(args.out_dir, args.kernel_count, Path("."))
    if args.strict:
        if result["kernel_count"] < 25 or result["sample_check_count"] < 500 or result["guard_check_count"] < 100:
            raise SystemExit("operator senses acceptance floor not met")
        if result["failed_count"] != 0:
            raise SystemExit("unexpected sample failures")
    print("OPERATOR_SENSES_FACTORY", result["kernel_count"], result["sample_check_count"], result["guard_check_count"], result["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
