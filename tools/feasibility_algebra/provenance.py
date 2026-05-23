from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ProvenanceRecord:
    record_id: str
    source: str
    freshness_days: int
    direct: bool
    risk: float

    def score(self) -> float:
        direct_bonus = 0.25 if self.direct else 0.0
        freshness_penalty = min(0.5, self.freshness_days / 3650)
        return max(0.0, min(1.0, 1.0 - self.risk - freshness_penalty + direct_bonus))


def combine_provenance(records: list[ProvenanceRecord]) -> dict[str, object]:
    if not records:
        return {"score": 0.0, "direct_count": 0, "record_count": 0}
    return {
        "score": sum(record.score() for record in records) / len(records),
        "direct_count": sum(1 for record in records if record.direct),
        "record_count": len(records),
    }
