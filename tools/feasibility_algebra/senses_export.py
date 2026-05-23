from __future__ import annotations


def band_tone(band: str) -> dict[str, object]:
    mapping = {
        "TRIVIAL": (180, "smooth"),
        "PRACTICAL": (240, "smooth"),
        "HEAVY_BUT_POSSIBLE": (320, "pulsed"),
        "BORDERLINE": (420, "tense"),
        "INFEASIBLE": (90, "stutter"),
        "ABSURD": (55, "muted harsh"),
        "SYMBOLIC_ONLY": (120, "thin"),
        "BLOCKED": (40, "blocked"),
    }
    frequency, texture = mapping.get(band, (100, "unknown"))
    return {"frequency_hz": frequency, "texture": texture}


def export_senses_rows(results: list[dict[str, object]]) -> list[dict[str, object]]:
    rows = []
    for result in results:
        band = str(result["feasibility_band"])
        rows.append({
            "expression_id": result["expression_id"],
            "n": result["n"],
            "budget_profile": result["budget_profile"],
            "band": band,
            "tone": band_tone(band),
        })
    return rows
