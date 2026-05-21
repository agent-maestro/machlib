from machlib.boundaries import boundary_lines
from machlib.summary import package_summary, toolchain


def test_package_summary_is_minimal_pre_alpha() -> None:
    summary = package_summary()
    assert summary["package_name"] == "machlib"
    assert summary["version"] == "0.0.1"
    assert summary["status"] == "pre-alpha"
    assert "not the full MachLib repository" in summary["boundary"]


def test_toolchain_lists_public_related_packages() -> None:
    names = {row["package_name"] for row in toolchain()}
    assert names == {
        "zero-mathlib-checker",
        "claim-boundary",
        "eml-records",
        "review-branch-packet",
    }


def test_boundaries_include_no_go_claims() -> None:
    text = "\n".join(boundary_lines())
    assert "not a theorem prover" in text
    assert "not a replacement for Mathlib" in text
    assert "not safety certification" in text
    assert "not production controller evidence" in text
    assert "does not upload, publish, push, deploy, or call remote APIs" in text
