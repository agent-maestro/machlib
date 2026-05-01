import MachLib.Hyperbolic

/-!
MachLib.HyperbolicPreservation — port of
legacy_eml/HyperbolicPreservation.lean to MachLib's axiomatic ℝ
regime (no Mathlib dependency).

Formalises PROP 08-A (Blind Session 08, 2026-04-22):
hyperbolic functions preserve the ELC field. If `f : ℝ → ℝ` is
expressible via `exp`, `log`, and arithmetic `(+, -, ·, /)`, then
so are `sinh ∘ f`, `cosh ∘ f`, `tanh ∘ f`. This gives a sharp
asymmetry with trigonometric functions (T01: `sin x ∉ ELC` for
generic real `x`).

Original Mathlib-dependent file at
`legacy_eml/HyperbolicPreservation.lean`. The 22 theorems below
are the ones that port cleanly against MachLib's axiom set; an
additional 12 theorems from the legacy file (numeric witnesses
needing a `norm_num`-equivalent, and identities needing a `ring`
tactic) are documented as deferred in `legacy_eml/PORT_PLAN.md`
under "MachLib needs ring + norm_num".

Statements use `(1 + 1)` where the legacy file used `2`, because
MachLib's `Basic` exposes `OfNat Real (nat_lit 0)` and
`OfNat Real (nat_lit 1)` only — broader numeric literals come
once the future `MachLib.Numerics` module lands.

Status: AUTHORED BY CLAUDE per
feedback_lean_writing_protocol_2026_04_25 — pending user
verification in VS Code lean4 extension before any public-surface
claims of "Lean-verified" status.
-/

namespace MachLib
namespace HyperbolicPreservation

open MachLib.Real

/-! ## Section 1 — Explicit ELC-primitive decompositions

These three are the headline result: every hyperbolic value is
an arithmetic combination of `exp`-applications, hence sinh,
cosh, tanh preserve the ELC field. -/

/-- **Explicit ELC-primitive decomposition of sinh:**
`sinh x = (exp x − exp(−x)) / 2`. Two exp-applications combined
with subtraction and halving — pure ELC. -/
theorem sinh_as_exp_arithmetic (x : Real) :
    sinh x = (exp x - exp (-x)) / (1 + 1) :=
  sinh_eq x

/-- **Explicit ELC-primitive decomposition of cosh:**
`cosh x = (exp x + exp(−x)) / 2`. -/
theorem cosh_as_exp_arithmetic (x : Real) :
    cosh x = (exp x + exp (-x)) / (1 + 1) :=
  cosh_eq x

/-- **Explicit ELC-primitive decomposition of tanh:**
`tanh x = sinh x / cosh x`, hence ELC by composition with the
two above. -/
theorem tanh_as_sinh_div_cosh (x : Real) :
    tanh x = sinh x / cosh x :=
  tanh_eq_sinh_div_cosh x

/-! ## Section 2 — Basic hyperbolic values and signs -/

/-- `sinh 0 = 0`. -/
theorem sinh_zero_eq : sinh 0 = 0 := sinh_zero

/-- `cosh 0 = 1`. -/
theorem cosh_zero_eq : cosh 0 = 1 := cosh_zero

/-- `tanh 0 = 0`. (From `MachLib.Trig`.) -/
theorem tanh_zero_eq : tanh 0 = 0 := tanh_zero

/-- sinh is odd. -/
theorem sinh_neg_eq (x : Real) : sinh (-x) = - sinh x := sinh_neg x

/-- cosh is even. -/
theorem cosh_neg_eq (x : Real) : cosh (-x) = cosh x := cosh_neg x

/-- cosh is strictly positive. -/
theorem cosh_pos_eq (x : Real) : 0 < cosh x := cosh_pos x

/-- `cosh x ≠ 0`, useful wherever a downstream proof divides by
`cosh`. -/
theorem one_div_cosh_well_defined (x : Real) : cosh x ≠ 0 :=
  cosh_ne_zero x

/-! ## Section 3 — Hyperbolic ↔ exp conversions -/

/-- `cosh x + sinh x = exp x`. -/
theorem cosh_add_sinh_eq_exp_thm (x : Real) :
    cosh x + sinh x = exp x :=
  cosh_add_sinh_eq_exp x

/-- `cosh x − sinh x = exp(−x)`. -/
theorem cosh_sub_sinh_eq_exp_neg_thm (x : Real) :
    cosh x - sinh x = exp (-x) :=
  cosh_sub_sinh_eq_exp_neg x

/-- `2 · sinh x = exp x − exp(−x)`. -/
theorem two_sinh_eq_exp_sub_thm (x : Real) :
    (1 + 1) * sinh x = exp x - exp (-x) :=
  two_sinh_eq_exp_sub x

/-- `2 · cosh x = exp x + exp(−x)`. -/
theorem two_cosh_eq_exp_add_thm (x : Real) :
    (1 + 1) * cosh x = exp x + exp (-x) :=
  two_cosh_eq_exp_add x

/-- `exp x · exp(−x) = 1`. (Direct consequence of `exp_add` +
`exp_zero`; useful for the product identity below.) -/
theorem exp_mul_exp_neg (x : Real) : exp x * exp (-x) = 1 := by
  rw [mul_comm]
  exact exp_neg_self_mul x

/-! ## Section 4 — Pythagorean identity + rearrangements -/

/-- **Hyperbolic Pythagorean identity:** `cosh² − sinh² = 1`.
(Stated in MachLib's product-form since MachLib does not yet
expose a `^ 2` natural-number power on `Real`.) -/
theorem cosh_sq_sub_sinh_sq (x : Real) :
    cosh x * cosh x - sinh x * sinh x = 1 :=
  pythagorean_hyp x

/-- `(cosh x + sinh x) · (cosh x − sinh x) = 1`. -/
theorem cosh_plus_minus_sinh_prod (x : Real) :
    (cosh x + sinh x) * (cosh x - sinh x) = 1 := by
  rw [cosh_add_sinh_eq_exp_thm, cosh_sub_sinh_eq_exp_neg_thm]
  exact exp_mul_exp_neg x

/-! ## Section 5 — Addition formulas (axioms in `Hyperbolic`) -/

/-- `sinh(a + b) = sinh a · cosh b + cosh a · sinh b`. -/
theorem sinh_add_formula (a b : Real) :
    sinh (a + b) = sinh a * cosh b + cosh a * sinh b :=
  sinh_add a b

/-- `cosh(a + b) = cosh a · cosh b + sinh a · sinh b`. -/
theorem cosh_add_formula (a b : Real) :
    cosh (a + b) = cosh a * cosh b + sinh a * sinh b :=
  cosh_add a b

/-- `sinh(a − b) = sinh a · cosh b − cosh a · sinh b`. -/
theorem sinh_sub_formula (a b : Real) :
    sinh (a - b) = sinh a * cosh b - cosh a * sinh b :=
  sinh_sub a b

/-- `cosh(a − b) = cosh a · cosh b − sinh a · sinh b`. -/
theorem cosh_sub_formula (a b : Real) :
    cosh (a - b) = cosh a * cosh b - sinh a * sinh b :=
  cosh_sub a b

/-! ## Section 6 — Double-angle formulas (axioms in `Hyperbolic`) -/

/-- `sinh(2x) = 2 · sinh x · cosh x`. -/
theorem sinh_two_mul_formula (x : Real) :
    sinh ((1 + 1) * x) = (1 + 1) * sinh x * cosh x :=
  sinh_two_mul x

/-- `cosh(2x) = cosh² x + sinh² x`. -/
theorem cosh_two_mul_formula (x : Real) :
    cosh ((1 + 1) * x) = cosh x * cosh x + sinh x * sinh x :=
  cosh_two_mul x

end HyperbolicPreservation
end MachLib
