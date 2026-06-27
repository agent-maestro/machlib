import MachLib.Hyperbolic
import MachLib.Ring
import MachLib.MPolyRing

/-!
# Hyperbolic identities — derived consequences (2026-06-27 audit)

`Hyperbolic.lean` sits *upstream* of `Ring`/`MPolyRing` (because `Ring` imports
`Forge` imports `Hyperbolic`), so it has no ring tactic — which is why a batch of
its identities were stated as axioms even though they follow algebraically from
the addition/negation generators. This module sits downstream of both
`Hyperbolic` and the ring tactics, so it PROVES them and the upstream axioms are
removed. (Their sole consumer, `HyperbolicPreservation`, imports this.)

Each derives only from axioms that REMAIN primitive in `Hyperbolic`
(`sinh_add`/`cosh_add`/`sinh_neg`/`cosh_neg`, the `cosh±sinh = exp(±x)` forms,
`exp_add`/`exp_zero`) — no circularity.

`sorryAx`-free.
-/

namespace MachLib
namespace Real

/-- `sinh (2x) = 2 · sinh x · cosh x`. From `sinh_add x x`. -/
theorem sinh_two_mul (x : Real) : sinh ((1 + 1) * x) = (1 + 1) * sinh x * cosh x := by
  have e : (1 + 1) * x = x + x := by mach_mpoly [x]
  rw [e, sinh_add]; mach_ring

/-- `cosh (2x) = cosh²x + sinh²x`. From `cosh_add x x`. -/
theorem cosh_two_mul (x : Real) : cosh ((1 + 1) * x) = cosh x * cosh x + sinh x * sinh x := by
  have e : (1 + 1) * x = x + x := by mach_mpoly [x]
  rw [e, cosh_add]

/-- `sinh (x − y) = sinh x cosh y − cosh x sinh y`. From `sinh_add x (−y)` + odd/even. -/
theorem sinh_sub (x y : Real) : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  rw [sub_def, sinh_add, sinh_neg, cosh_neg]
  show sinh x * cosh y + cosh x * (-(sinh y)) = sinh x * cosh y - cosh x * sinh y
  mach_mpoly [sinh x, cosh x, sinh y, cosh y]

/-- `cosh (x − y) = cosh x cosh y − sinh x sinh y`. From `cosh_add x (−y)` + odd/even. -/
theorem cosh_sub (x y : Real) : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  rw [sub_def, cosh_add, sinh_neg, cosh_neg]
  show cosh x * cosh y + sinh x * (-(sinh y)) = cosh x * cosh y - sinh x * sinh y
  mach_mpoly [sinh x, cosh x, sinh y, cosh y]

/-- **Hyperbolic Pythagorean** `cosh²x − sinh²x = 1`. From the difference of squares
`(cosh+sinh)(cosh−sinh) = exp x · exp(−x) = exp 0 = 1`. -/
theorem pythagorean_hyp (x : Real) : cosh x * cosh x - sinh x * sinh x = 1 := by
  have h1 := cosh_add_sinh_eq_exp x
  have h2 := cosh_sub_sinh_eq_exp_neg x
  have hprod : (cosh x + sinh x) * (cosh x - sinh x) = exp x * exp (-x) := by rw [h1, h2]
  have hexp : exp x * exp (-x) = 1 := by
    rw [← exp_add, show x + (-x) = 0 from by mach_ring, exp_zero]
  have hdiff : (cosh x + sinh x) * (cosh x - sinh x) = cosh x * cosh x - sinh x * sinh x := by
    mach_mpoly [cosh x, sinh x]
  rw [hdiff, hexp] at hprod; exact hprod

end Real
end MachLib
