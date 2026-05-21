"""Public no-go boundaries for the minimal MachLib package."""

BOUNDARIES = [
    "not a theorem prover",
    "not a replacement for Mathlib",
    "not a public proof system",
    "not an open-problem solver",
    "not safety certification",
    "not production controller evidence",
    "not a Command Center deploy tool",
    "not a Hugging Face, PETAL, or CapCard certification tool",
    "does not upload, publish, push, deploy, or call remote APIs",
    "does not include the full MachLib repository, corpus, reports, or feed drafts",
]


def boundary_lines() -> list[str]:
    """Return the public package boundary lines."""
    return list(BOUNDARIES)
