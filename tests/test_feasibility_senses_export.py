from tools.feasibility_algebra.senses_export import band_tone, export_senses_rows


def test_band_tone_absurd_low_frequency():
    assert band_tone("ABSURD")["frequency_hz"] < band_tone("PRACTICAL")["frequency_hz"]


def test_band_tone_has_texture():
    assert band_tone("BORDERLINE")["texture"]


def test_export_senses_rows_maps_result():
    rows = export_senses_rows([
        {"expression_id": "x", "n": 1, "budget_profile": "p", "feasibility_band": "PRACTICAL"}
    ])
    assert rows[0]["tone"]["frequency_hz"] > 0
    assert rows[0]["band"] == "PRACTICAL"


def test_export_senses_rows_empty_ok():
    assert export_senses_rows([]) == []
