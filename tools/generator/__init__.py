"""machlib.tools.generator — synthetic variant generation.

Five template-based strategies that take a base record and emit
candidate variants:

  * ``constant_swap``     — replace numeric literals with parametrised inputs
  * ``domain_change``     — broaden / narrow input bounds
  * ``operator_swap``     — substitute among the SuperBEST sister operators
  * ``composition_depth`` — wrap the body in additional eml-layer compositions
  * ``negation``          — flip strict / non-strict inequality directions

Generation is purely structural — no Lean is invoked at this stage.
Use the verifier (planned for Phase 1.5, after the legacy theorems
are ported to MachLib foundations) to gate verified-vs-candidate.
"""
from __future__ import annotations

from .strategies import (
    EMLTheoremGenerator,
    GeneratedVariant,
    VARIATION_TYPES,
)

__all__ = [
    "EMLTheoremGenerator",
    "GeneratedVariant",
    "VARIATION_TYPES",
]
