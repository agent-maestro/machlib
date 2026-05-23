from tools.feasibility_algebra.resources import ResourceProfile, default_resource_profiles


def test_default_profiles_include_required_ids():
    ids = {profile.profile_id for profile in default_resource_profiles()}
    assert {
        "laptop_small",
        "workstation",
        "gpu_box",
        "cluster_small",
        "hypothetical_large_cluster",
        "silicon_toy_budget",
        "browser_interactive_budget",
        "capcard_review_budget",
    } <= ids


def test_profile_to_dict_has_budget_fields():
    profile = default_resource_profiles()[0].to_dict()
    assert profile["operation_budget"] > 0
    assert profile["memory_budget_bytes"] > 0
    assert profile["time_budget_seconds"] > 0


def test_resource_profile_dataclass_roundtrip():
    profile = ResourceProfile("x", "X", 1, 2, 3, None, "note")
    assert profile.to_dict()["profile_id"] == "x"


def test_browser_budget_smaller_than_workstation():
    profiles = {p.profile_id: p for p in default_resource_profiles()}
    assert profiles["browser_interactive_budget"].operation_budget < profiles["workstation"].operation_budget


def test_silicon_budget_memory_is_tiny():
    profiles = {p.profile_id: p for p in default_resource_profiles()}
    assert profiles["silicon_toy_budget"].memory_budget_bytes < profiles["laptop_small"].memory_budget_bytes


def test_all_profiles_have_notes():
    for profile in default_resource_profiles():
        assert profile.notes


def test_all_profiles_have_positive_operation_budget():
    for profile in default_resource_profiles():
        assert profile.operation_budget > 0
