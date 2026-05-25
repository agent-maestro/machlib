"""Schema-conformance tests across the entire corpus.

Every canonical theorem JSON file under ``corpus/`` must:

  * be valid JSON,
  * carry the eight required top-level sections,
  * have an `id` that matches the filename,
  * declare a known domain and lane,
  * reference at least one proof.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
CORPUS = REPO_ROOT / "corpus"


_REQUIRED_TOP_LEVEL = {
    "schema_version",
    "theorem",
    "proofs",
    "difficulty",
    "common_mistakes",
    "tactic_trace",
    "structural_profile",
    "relationships",
    "metadata",
}

_KNOWN_DOMAINS = {
    "eml", "analysis", "algebra",
    "chemistry", "physics", "finance", "engineering",
    "forge_mined",
}

_KNOWN_LANES = {1, 2, 3, 4, 5, 6}


def _all_records() -> list[tuple[Path, dict]]:
    out: list[tuple[Path, dict]] = []
    for path in CORPUS.rglob("*.json"):
        data = json.loads(path.read_text(encoding="utf-8"))
        if (
            isinstance(data, dict)
            and "schema_version" in data
            and isinstance(data.get("theorem"), dict)
        ):
            out.append((path, data))
    return out


def _is_draft_internal(record: dict) -> bool:
    metadata = record.get("metadata", {})
    return bool(metadata.get("draft_internal")) or str(
        record.get("schema_version", "")
    ).endswith("-draft-eml-lane")


# Collected once, parametrised across every record.
_ALL = _all_records()
_IDS = [str(p.relative_to(REPO_ROOT)) for p, _ in _ALL]


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_has_required_sections(path: Path, record: dict) -> None:
    missing = _REQUIRED_TOP_LEVEL - set(record.keys())
    assert not missing, f"{path}: missing top-level sections: {sorted(missing)}"


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_id_matches_filename(path: Path, record: dict) -> None:
    expected_id = path.stem
    actual_id = record["theorem"]["id"]
    assert actual_id == expected_id, (
        f"{path}: theorem.id={actual_id!r} != filename {expected_id!r}"
    )


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_has_known_domain(path: Path, record: dict) -> None:
    domain = record["theorem"]["domain"]
    assert domain in _KNOWN_DOMAINS, f"{path}: unknown domain {domain!r}"


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_has_valid_lane(path: Path, record: dict) -> None:
    lane = record["theorem"]["lane"]
    assert lane in _KNOWN_LANES, f"{path}: unknown lane {lane!r}"


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_has_at_least_one_proof(path: Path, record: dict) -> None:
    # forge_mined records are sorry stubs awaiting Phase B (BFS engine
    # + RL agent). They legitimately ship with zero proofs until the
    # discovery loop fills them in.
    if record["theorem"]["domain"] == "forge_mined" or _is_draft_internal(record):
        return
    proofs = record.get("proofs", [])
    assert len(proofs) >= 1, f"{path}: zero proofs"


@pytest.mark.parametrize("path,record", _ALL, ids=_IDS)
def test_record_has_exactly_one_optimal_proof(
    path: Path, record: dict
) -> None:
    # forge_mined records ship with empty proofs -- the BFS engine
    # marks an optimal proof once it lands one. Skip until then.
    if record["theorem"]["domain"] == "forge_mined" or _is_draft_internal(record):
        return
    proofs = record.get("proofs", [])
    optimals = [p for p in proofs if p.get("is_optimal")]
    assert len(optimals) == 1, (
        f"{path}: expected exactly one is_optimal=true proof, got {len(optimals)}"
    )


def test_corpus_is_nonempty() -> None:
    assert len(_ALL) > 0, "no corpus records found"
