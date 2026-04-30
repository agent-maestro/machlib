"""Three exporters for verified synthetic variants.

  * **JSONL** — one record per line; the canonical format for
    retrieval / RAG pipelines and HuggingFace's ``json`` loader.

  * **HuggingFace Dataset** — push-to-hub-ready
    ``datasets.Dataset``. Soft dep on ``datasets``; raises an
    explicit ImportError when the package is missing.

  * **Tactic Zoo** — JSON keyed by tactic identifier. Each entry
    records frequency, contexts (per-theorem), and a sample of
    example proofs. Ready for any LLM that wants to load
    "which tactics work where" as a single JSON file.
"""
from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

from .verifier import VerifiedVariant


__all__ = [
    "TacticTraceExporter",
]


class TacticTraceExporter:
    """Render a list of verified variants in three formats."""

    def __init__(self, variants: Iterable[VerifiedVariant]) -> None:
        self.variants = list(variants)

    # ── JSONL ─────────────────────────────────────────────────────

    def to_jsonl(self, path: str | Path) -> int:
        """Write one JSON record per line. Returns count written."""
        out_path = Path(path)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            for v in self.variants:
                f.write(json.dumps(self._jsonl_record(v), ensure_ascii=False))
                f.write("\n")
        return len(self.variants)

    def _jsonl_record(self, v: VerifiedVariant) -> dict:
        return {
            "theorem_id": v.theorem_id,
            "base_theorem_id": v.base_theorem_id,
            "strategy": v.strategy,
            "statement_lean4": v.statement_lean4,
            "proof_lean4": v.proof_lean4,
            "natural_language": v.natural_language,
            "tactic_trace": list(v.tactic_trace),
            "chain_order": v.chain_order,
            "node_count": v.node_count,
            "cost_class": v.cost_class,
            "build_time_seconds": v.build_time_seconds,
            "verified_at": v.verified_at,
            "metadata": dict(v.metadata),
        }

    # ── HuggingFace ───────────────────────────────────────────────

    def to_huggingface(self, repo_id: str, *, private: bool = False):
        """Push the records to the HuggingFace Hub.

        Returns the resulting :class:`datasets.Dataset` so the caller
        can inspect it. Soft-dep on ``datasets`` — raises a clear
        ImportError when not installed.
        """
        try:
            from datasets import Dataset  # type: ignore[import-not-found]
        except ImportError as exc:
            raise ImportError(
                "to_huggingface requires the `datasets` package. "
                "Install with: pip install datasets"
            ) from exc
        records = [self._jsonl_record(v) for v in self.variants]
        ds = Dataset.from_list(records)
        ds.push_to_hub(repo_id, private=private)
        return ds

    def to_huggingface_local(self, path: str | Path):
        """Save as a local Arrow dataset (no network).

        Useful for testing the HuggingFace export without uploading.
        """
        try:
            from datasets import Dataset  # type: ignore[import-not-found]
        except ImportError as exc:
            raise ImportError(
                "to_huggingface_local requires the `datasets` package. "
                "Install with: pip install datasets"
            ) from exc
        records = [self._jsonl_record(v) for v in self.variants]
        ds = Dataset.from_list(records)
        ds.save_to_disk(str(path))
        return ds

    # ── Tactic Zoo ────────────────────────────────────────────────

    def to_tactic_zoo(self, path: str | Path, *, max_examples: int = 8) -> dict:
        """Build the EML-tactic-zoo JSON keyed by tactic name.

        Schema::

            {
              "<tactic>": {
                "frequency": <total occurrences across all proofs>,
                "theorems": [<list of theorem_ids using this tactic>],
                "strategies": {<strategy>: <count>},
                "examples": [{<theorem_id>, <proof_excerpt>}, ...]
              },
              ...
            }
        """
        zoo: dict[str, dict] = {}
        for v in self.variants:
            for tactic in v.tactic_trace:
                entry = zoo.setdefault(tactic, {
                    "frequency": 0,
                    "theorems": [],
                    "strategies": Counter(),
                    "examples": [],
                })
                entry["frequency"] += 1
                if v.theorem_id not in entry["theorems"]:
                    entry["theorems"].append(v.theorem_id)
                entry["strategies"][v.strategy] += 1
                if len(entry["examples"]) < max_examples:
                    entry["examples"].append({
                        "theorem_id": v.theorem_id,
                        "proof_excerpt": v.proof_lean4[:200],
                    })

        # Convert Counters to plain dicts for JSON.
        out = {
            tac: {
                "frequency": e["frequency"],
                "theorems": e["theorems"],
                "strategies": dict(e["strategies"]),
                "examples": e["examples"],
            }
            for tac, e in zoo.items()
        }
        # Sort keys by descending frequency so the JSON is human-readable.
        out_sorted = dict(
            sorted(out.items(), key=lambda kv: -kv[1]["frequency"])
        )

        out_path = Path(path)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(
            json.dumps(out_sorted, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        return out_sorted

    # ── Summary ───────────────────────────────────────────────────

    def summary(self) -> dict:
        """Counts useful for the CLI / blog post."""
        if not self.variants:
            return {
                "verified_count": 0,
                "by_strategy": {},
                "by_base_theorem": {},
                "tactics": {},
            }
        by_strategy = Counter(v.strategy for v in self.variants)
        by_base = Counter(v.base_theorem_id for v in self.variants)
        tactic_freq: Counter = Counter()
        for v in self.variants:
            tactic_freq.update(v.tactic_trace)
        return {
            "verified_count": len(self.variants),
            "by_strategy": dict(by_strategy),
            "by_base_theorem": dict(by_base.most_common()),
            "tactics": dict(tactic_freq.most_common()),
        }
