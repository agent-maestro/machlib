from tools.feasibility_algebra.stress_families import stress_families, stress_family_rows


def test_stress_family_count_at_least_18():
    assert len(stress_families()) >= 18


def test_stress_families_include_n1000():
    assert "polynomial_n1000" in {item.expression_id for item in stress_families()}


def test_stress_family_rows_have_not_claimed():
    for row in stress_family_rows():
        assert row["not_claimed"]


def test_all_family_rows_have_asymptotic_class():
    for row in stress_family_rows():
        assert row["asymptotic_class"]


def test_constant_huge_family_is_constant_label_but_huge():
    rows = {row["expression_id"]: row for row in stress_family_rows()}
    assert rows["constant_but_huge_hidden_factor"]["asymptotic_class"] == "O(1)"
