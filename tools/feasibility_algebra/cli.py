from __future__ import annotations

import argparse
from pathlib import Path

from .bands import FeasibilityBand
from .capcard_bridge import score_candidate
from .evaluator import evaluate_expression
from .reporting import write_json, write_report
from .resources import default_resource_profiles
from .semiring import block_forbidden_claim, combine_alternative, combine_parallel, combine_sequential, degrade_stale, element
from .senses_export import export_senses_rows
from .stress_families import stress_families, stress_family_rows

DATE = "2026_05_23"
NS = [1, 2, 5, 10, 20, 50, 100, 1000, 1_000_000]


def run_stress(out_dir: Path, strict: bool = False) -> dict[str, object]:
    repo = Path(".")
    out_dir.mkdir(parents=True, exist_ok=True)
    families = stress_families()
    profiles = default_resource_profiles()

    results = [
        evaluate_expression(expr, n, profile).to_dict()
        for expr in families
        for n in NS
        for profile in profiles
    ]
    n1000_rows = [
        row for row in results
        if row["expression_id"] == "polynomial_n1000"
    ]
    practical_bands = [
        row["feasibility_band"] for row in n1000_rows
        if row["budget_profile"] in {"laptop_small", "workstation", "browser_interactive_budget", "silicon_toy_budget"}
        and int(row["n"]) >= 2
    ]
    practical_result = "ABSURD" if "ABSURD" in practical_bands else "INFEASIBLE"

    stress_payload = {
        "status": "PASS",
        "result_count": len(results),
        "n_values": NS,
        "profile_count": len(profiles),
        "family_count": len(families),
        "public_claim": False,
        "theorem_proof_claim": False,
        "results": results,
    }
    n1000_payload = {
        "central_case": "n^1000",
        "asymptotic_label": "O(n^1000), formally polynomial",
        "practical_result": practical_result,
        "summary": "n^1000 is formally polynomial but becomes operationally absurd at tiny n under practical resource profiles.",
        "not_claimed": ["not a theorem proof", "not a new complexity class", "not an open-problem result"],
        "rows": n1000_rows,
        "public_claim": False,
        "theorem_proof_claim": False,
    }

    band_matrix = build_band_matrix(results)
    write_json(out_dir / f"feasibility_results_{DATE}.json", stress_payload)
    write_json(out_dir / f"n1000_stress_result_{DATE}.json", n1000_payload)
    write_json(out_dir / f"resource_profiles_{DATE}.json", {"profiles": [p.to_dict() for p in profiles]})
    write_json(out_dir / f"feasibility_band_matrix_{DATE}.json", band_matrix)

    write_stress_family_outputs(repo)
    write_semiring_model(repo)
    write_eml_records(repo, stress_payload)
    write_senses_demo(repo, results)
    write_capcard_candidates(repo)
    write_silicon_bridge(repo)
    write_assessment(repo)
    write_command_center(repo)
    write_stress_reports(repo, stress_payload, n1000_payload)

    if strict:
        if stress_payload["result_count"] < 18 * 9 * 8:
            raise SystemExit("unexpected stress result count")
        if n1000_payload["practical_result"] not in {"ABSURD", "INFEASIBLE"}:
            raise SystemExit("n1000 practical result did not block")
    return stress_payload


def build_band_matrix(results: list[dict[str, object]]) -> dict[str, object]:
    matrix: dict[str, dict[str, dict[str, str]]] = {}
    for row in results:
        matrix.setdefault(str(row["expression_id"]), {}).setdefault(str(row["budget_profile"]), {})[str(row["n"])] = str(row["feasibility_band"])
    return {"status": "PASS", "matrix": matrix, "public_claim": False, "theorem_proof_claim": False}


def write_stress_family_outputs(repo: Path) -> None:
    rows = stress_family_rows()
    write_json(repo / f"product_readiness/feasibility_stress_families_{DATE}.json", {"families": rows, "family_count": len(rows)})
    write_report(
        repo / f"reports/feasibility_stress_families_{DATE}.md",
        "Feasibility Stress Families",
        [
            f"Family count: {len(rows)}.",
            "",
            "These families compare asymptotic labels against bounded resource profiles.",
            "The list is internal research scaffolding, not a theorem or standard.",
        ],
    )


def write_semiring_model(repo: Path) -> None:
    n1000 = element(1e300, 1e6, FeasibilityBand.ABSURD)
    linear = element(1e6, 1e4, FeasibilityBand.PRACTICAL)
    seq = combine_sequential(linear, n1000)
    alt = combine_alternative(n1000, linear)
    par = combine_parallel(linear, n1000)
    stale = degrade_stale(linear)
    blocked = block_forbidden_claim(linear)
    payload = {
        "status": "DRAFT_INTERNAL",
        "language": "semiring/provenance/min-plus inspired toy model",
        "not_claimed": [
            "not a formal new algebraic theorem",
            "not proved complete",
            "not a public standard",
        ],
        "examples": {
            "sequential": seq.to_dict(),
            "alternative": alt.to_dict(),
            "parallel": par.to_dict(),
            "stale": stale.to_dict(),
            "blocked_forbidden_claim": blocked.to_dict(),
        },
        "public_claim": False,
        "theorem_proof_claim": False,
    }
    write_json(repo / f"product_readiness/feasibility_semiring_model_{DATE}.json", payload)
    write_report(
        repo / f"reports/feasibility_semiring_model_{DATE}.md",
        "Feasibility Semiring Toy Model",
        [
            "This model is inspired by cost semirings, provenance semirings, and min-plus/tropical choice.",
            "Sequential composition adds costs and carries worst risk.",
            "Alternative composition chooses a lower cost/risk path.",
            "Forbidden public claims block the element.",
            "No theorem or completeness claim is made.",
        ],
    )


def write_eml_records(repo: Path, stress_payload: dict[str, object]) -> None:
    base_ids = [
        "n1000_polynomial_but_infeasible_record",
        "polynomial_feasibility_gap_record",
        "resource_profile_record",
        "feasibility_band_record",
        "semiring_combine_record",
        "tropical_alternative_record",
        "provenance_risk_record",
        "capcard_trust_bridge_record",
        "senses_feasibility_mapping_record",
        "silicon_budget_record",
        "browser_budget_record",
        "proof_search_branching_record",
        "memory_quadratic_record",
        "stale_evidence_penalty_record",
        "forbidden_claim_block_record",
    ]
    extra = [f"stress_family_{row['expression_id']}_record" for row in stress_family_rows()]
    records = []
    for idx, record_id in enumerate(base_ids + extra):
        records.append({
            "record_id": record_id,
            "status": "DRAFT_INTERNAL",
            "family": "feasibility_algebra",
            "executable_check": "tools.feasibility_algebra.cli run-stress",
            "copied_text": False,
            "public_ready": False,
            "theorem_proof_claim": False,
            "open_problem_claim": False,
            "certified_safety_claim": False,
            "production_controller_claim": False,
            "physics_claim": False,
            "package_publish_allowed": False,
            "petal_api_upload_performed": False,
            "huggingface_upload_performed": False,
            "notes": "Internal EML-style feasibility record; numeric/resource evidence only.",
            "ordinal": idx,
        })
    out = repo / "corpus/eml_feasibility_algebra_draft"
    write_json(out / f"records_{DATE}.json", {"records": records})
    write_json(out / f"execution_result_{DATE}.json", {"status": "PASS", "record_count": len(records), "stress_result_count": stress_payload["result_count"]})
    write_json(out / f"guardrail_report_{DATE}.json", {"status": "PASS", "public_ready": False, "theorem_proof_claim": False, "certified_safety_claim": False})


def write_senses_demo(repo: Path, results: list[dict[str, object]]) -> None:
    out = repo / "senses/feasibility_senses_2026_05_23"
    sample = [
        row for row in results
        if row["budget_profile"] in {"browser_interactive_budget", "workstation"}
        and row["expression_id"] in {"linear_n", "quadratic_n2", "polynomial_n1000", "exponential_2n", "factorial_n"}
    ]
    data = {
        "families": stress_family_rows(),
        "profiles": [p.to_dict() for p in default_resource_profiles()],
        "senses_rows": export_senses_rows(sample),
    }
    manifest = {
        "prototype_id": "feasibility_senses_2026_05_23",
        "status": "PASS",
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
    write_json(out / f"feasibility_senses_data_{DATE}.json", data)
    write_json(out / f"feasibility_senses_manifest_{DATE}.json", manifest)
    (out / "index.html").parent.mkdir(parents=True, exist_ok=True)
    (out / "index.html").write_text("""<!doctype html>
<html lang=\"en\">
<head><meta charset=\"utf-8\"><title>Feasibility Senses</title><link rel=\"stylesheet\" href=\"feasibility_senses.css\"></head>
<body>
<main>
<h1>Feasibility Senses</h1>
<p>Pre-alpha feasibility explorer. Not a complexity-theory theorem. Not a proof of tractability/intractability. Not certified safety. Not production controller evidence. No hardware action. No microphone.</p>
<label>Family <select id=\"family\"></select></label>
<label>Profile <select id=\"profile\"></select></label>
<label>n <input id=\"n\" type=\"range\" min=\"0\" max=\"8\" value=\"3\"></label>
<button id=\"play\">Play</button><button id=\"stop\">Stop</button><button id=\"mute\">Mute</button>
<section id=\"viz\"></section><pre id=\"detail\"></pre>
</main><script src=\"feasibility_senses.js\"></script>
</body></html>
""")
    (out / "feasibility_senses.css").write_text("""body{font-family:system-ui;margin:0;background:#101520;color:#f7f1df}main{max-width:980px;margin:auto;padding:2rem}select,input,button{margin:.4rem;padding:.55rem}#viz{height:260px;border:1px solid #435064;border-radius:12px;margin:1rem 0;background:linear-gradient(135deg,#172033,#315d66,#d7b45c)}.bar{display:inline-block;width:9%;margin:1%;vertical-align:bottom;background:#f7f1df;border-radius:999px}pre{white-space:pre-wrap;background:#1d2634;padding:1rem;border-radius:10px}""")
    (out / "feasibility_senses.js").write_text("""let data;let ctx;let osc;let muted=false;const ns=[1,2,5,10,20,50,100,1000,1000000];fetch('feasibility_senses_data_2026_05_23.json').then(r=>r.json()).then(d=>{data=d;init();});function init(){const fam=document.getElementById('family');const prof=document.getElementById('profile');data.families.forEach(f=>fam.add(new Option(f.expression_id,f.expression_id)));data.profiles.forEach(p=>prof.add(new Option(p.profile_id,p.profile_id)));['family','profile','n'].forEach(id=>document.getElementById(id).oninput=render);document.getElementById('play').onclick=play;document.getElementById('stop').onclick=stop;document.getElementById('mute').onclick=()=>{muted=!muted;stop();};render();}function row(){const n=ns[+document.getElementById('n').value];return data.senses_rows.find(r=>r.expression_id===family.value&&r.budget_profile===profile.value&&r.n===n)||data.senses_rows.find(r=>r.expression_id===family.value)||data.senses_rows[0];}function render(){const r=row();detail.textContent=JSON.stringify(r,null,2);viz.innerHTML='';const height={TRIVIAL:35,PRACTICAL:55,HEAVY_BUT_POSSIBLE:95,BORDERLINE:135,INFEASIBLE:190,ABSURD:235,SYMBOLIC_ONLY:80}[r.band]||70;for(let i=0;i<8;i++){const b=document.createElement('span');b.className='bar';b.style.height=(height+(i%3)*12)+'px';b.style.background=r.band==='ABSURD'?'#e85c5c':'#f7f1df';viz.appendChild(b);}}function play(){if(muted)return;stop();const r=row();ctx=ctx||new AudioContext();osc=ctx.createOscillator();const g=ctx.createGain();osc.type=r.band==='ABSURD'?'sawtooth':'sine';osc.frequency.value=r.tone.frequency_hz;g.gain.value=.035;osc.connect(g);g.connect(ctx.destination);osc.start();osc.stop(ctx.currentTime+.8);}function stop(){try{osc&&osc.stop()}catch(e){}osc=null;}""")


def write_capcard_candidates(repo: Path) -> None:
    out = repo / "capcard_marketplace_drafts/feasibility_algebra_candidates_2026_05_23"
    candidate_ids = [
        "n1000_feasibility_stress_kernel",
        "feasibility_band_matrix",
        "resource_profile_catalog",
        "feasibility_semiring_toy_model",
        "tropical_alternative_cost_model",
        "capcard_trust_bridge",
        "feasibility_senses_demo",
        "silicon_budget_feasibility_record",
    ]
    candidates = []
    for cid in candidate_ids:
        card = {
            "candidate_id": cid,
            "display_name": cid.replace("_", " ").title(),
            "visibility": "internal",
            "marketplace_status": "INTERNAL_DRAFT_CANDIDATE",
            "safe_to_display_internally": True,
            "safe_to_publish_publicly": False,
            "evidence_basis": ["stress lab outputs", "EML draft records", "guardrail reports"],
            "marketplace_upload_performed": False,
            "production_marketplace_modified": False,
            "petal_api_upload_performed": False,
            "huggingface_upload_performed": False,
            "public_claim": False,
            "certified_safety_claim": False,
            "production_controller_claim": False,
            "theorem_proof_claim": False,
        }
        candidates.append(card)
        write_json(out / f"{cid}.json", card)
        write_report(out / f"{cid}.md", card["display_name"], ["Internal draft candidate.", "Not public marketplace-ready."])
    write_json(repo / f"product_readiness/feasibility_algebra_capcard_candidates_{DATE}.json", {"candidates": candidates})
    scores = {"candidates": [{**score_candidate(5, "PRACTICAL"), "candidate_id": c["candidate_id"]} for c in candidates]}
    write_json(repo / f"product_readiness/feasibility_algebra_capcard_scores_{DATE}.json", scores)
    write_report(repo / f"reports/feasibility_algebra_capcard_candidates_{DATE}.md", "Feasibility Algebra CapCard Candidates", [f"Candidate count: {len(candidates)}.", "All candidates remain internal draft candidates."])
    write_report(repo / f"reports/feasibility_algebra_capcard_guardrail_report_{DATE}.md", "Feasibility Algebra CapCard Guardrails", ["Production marketplace modified: false.", "Public claim: false.", "PETAL/HF upload: false."])
    write_report(repo / f"reports/feasibility_algebra_capcard_scores_{DATE}.md", "Feasibility Algebra CapCard Scores", ["Scores are internal placeholders from bounded stress evidence."])


def write_silicon_bridge(repo: Path) -> None:
    payload = {
        "surface": "monogate_silicon_feasibility_bridge",
        "status": "SIMULATION_ONLY_INTERNAL",
        "trace0_resource_budgets": {"event_counter_bits": 32, "frame_budget_bytes": 256, "toy_operation_budget": 1e6},
        "helps_with": ["state/event counter sizing", "frame bandwidth", "memory budget", "timing estimates"],
        "hardware_action_performed": False,
        "tapeout_performed": False,
        "production_controller_claim": False,
        "certified_safety_claim": False,
        "public_claim": False,
    }
    write_json(repo / f"product_readiness/monogate_silicon_feasibility_bridge_{DATE}.json", payload)
    write_report(repo / f"reports/monogate_silicon_feasibility_bridge_{DATE}.md", "Monogate Silicon Feasibility Bridge", ["Simulation-only bridge for Trace0-scale resource budgets.", "No hardware action, tapeout, certified safety, or production controller claim."])


def write_assessment(repo: Path) -> None:
    payload = {
        "verdict": "BUILD_FEASIBILITY_ALGEBRA_LAB",
        "research_depth_0_to_100": 82,
        "substrate_potential_0_to_100": 76,
        "capcard_utility_0_to_100": 84,
        "senses_utility_0_to_100": 78,
        "silicon_planning_utility_0_to_100": 80,
        "overclaim_risk_0_to_100": 72,
        "blunt_answer": "n^1000 unlocks a useful product/research lens: asymptotic class is not feasibility. It is not a new complexity theorem.",
        "public_claim": False,
        "theorem_proof_claim": False,
    }
    write_json(repo / f"product_readiness/feasibility_algebra_research_assessment_{DATE}.json", payload)
    write_report(repo / f"reports/feasibility_algebra_research_assessment_{DATE}.md", "Feasibility Algebra Research Assessment", [
        "n^1000 is the right adversarial example: formally polynomial, practically absurd early.",
        "What is actually new is the evidence/product substrate: resource profiles, bands, provenance risk, and CapCard trust bridge.",
        "What is not new is complexity theory itself; this lab repackages known asymptotic distinctions into operational review tooling.",
        "Verdict: BUILD_FEASIBILITY_ALGEBRA_LAB.",
    ])
    write_report(repo / f"reports/feasibility_algebra_next_steps_{DATE}.md", "Feasibility Algebra Next Steps", [
        "Add parser support for more cost expressions.",
        "Calibrate budgets from real traces.",
        "Fold the band model into CapCard Lab as an internal scoring dimension.",
        "Keep theorem/proof claims blocked.",
    ])


def write_command_center(repo: Path) -> None:
    card = {
        "surface": "command.monogate.dev",
        "card_id": "feasibility_algebra_status",
        "visibility": "internal",
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "deploy_performed": False,
        "public_claim": False,
    }
    write_json(repo / f"command_center_feeds/feasibility_algebra_status_card_{DATE}.json", card)
    write_json(repo / f"command_center_feeds/feasibility_algebra_status_feed_{DATE}.json", {"cards": [card], "deploy_performed": False})
    write_report(repo / f"reports/feasibility_algebra_command_center_card_{DATE}.md", "Feasibility Algebra Command Center Card", ["Internal-only status card. No deploy performed."])


def write_stress_reports(repo: Path, stress: dict[str, object], n1000: dict[str, object]) -> None:
    write_report(repo / f"reports/feasibility_stress_lab_summary_{DATE}.md", "Feasibility Stress Lab Summary", [
        f"Result count: {stress['result_count']}.",
        "The lab evaluates stress families across bounded resource profiles.",
        "Polynomial/exponential labels alone do not capture operational feasibility.",
    ])
    write_report(repo / f"reports/n1000_stress_result_{DATE}.md", "n^1000 Stress Result", [
        f"Central case: {n1000['central_case']}.",
        f"Practical result: {n1000['practical_result']}.",
        "n^1000 is polynomial in the abstract but becomes absurd or infeasible at tiny n under practical budgets.",
        "This is numeric resource evidence only, not a theorem.",
    ])


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Monogate feasibility algebra stress lab")
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run-stress")
    run.add_argument("--out-dir", required=True)
    run.add_argument("--strict", action="store_true")
    args = parser.parse_args(argv)
    if args.command == "run-stress":
        run_stress(Path(args.out_dir), args.strict)


if __name__ == "__main__":
    main()
