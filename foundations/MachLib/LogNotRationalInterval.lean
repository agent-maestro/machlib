/-
# The consumer `no_rational_logarithm` never had

`(gc)` recorded a specific risk rather than a general worry: the `k = 1` corollary
`no_rational_logarithm` was quoted by docstrings and **applied by nothing**, and the witness audit —
built precisely to catch capstones nobody instantiates — cannot see it, because a theorem concluding
`False` is excluded from that audit by design.

This module closes that. `log_not_rational_on_interval` applies it, so the corollary is consumed and
the risk named in `(gc)` is discharged by construction rather than by argument.

`hchar` does not appear as a hypothesis: `derivCoprime_of_irred` `(fy)` discharges it inline from
`PIrred q`. What the caller supplies is structural (`q` irreducible, the numerator coprime to it, the
denominator's exact multiplicity) or non-vanishing on the interval — no tail, no growth premise.
-/
import MachLib.LogRatDerivInterval
import MachLib.PolyDerivNonzero
import MachLib.PolyLogDeriv

namespace MachLib

open Real

/-- **`log` of a rational function is not rational on any interval.**

The consumer `no_rational_logarithm` never had. `(gc)` recorded that the `k = 1` corollary was quoted
by docstrings and applied by nothing, and that the witness audit cannot see this theorem class
because it concludes `False`.

`hchar` is discharged inline from `PIrred q` by `derivCoprime_of_irred`, so it is not a hypothesis
here. Everything the caller supplies is either structural (`q` irreducible, in lowest terms, the
denominator's exact multiplicity) or a non-vanishing condition on the interval. -/
theorem log_not_rational_on_interval {P Q N D q Qt : List Real} {r : Nat} {a b : Real}
    (hab : a < b) (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    (hQfac : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hDne : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q N)
    (hQ0 : ∀ x : Real, a < x → x < b → pev Q x ≠ 0)
    (hD0 : ∀ x : Real, a < x → x < b → pev D x ≠ 0)
    (hP0 : ∀ x : Real, a < x → x < b → pev P x ≠ 0)
    (hpos : ∀ x : Real, a < x → x < b → 0 < pev P x / pev Q x)
    (hlog : ∀ x : Real, a < x → x < b → log (pev P x / pev Q x) = pev N x / pev D x) :
    False := by
  refine no_rational_logarithm hq (derivCoprime_of_irred hq) hPd hPn hNn hQfac hQtd hDne hlow ?_
  exact PEq.trans (peq_pmul (PEq.refl _) (peq_pmul_comm P Q))
    (PEq.symm (hident_of_log_rational_on_interval hab hQ0 hD0 hP0 hpos hlog))

end MachLib
