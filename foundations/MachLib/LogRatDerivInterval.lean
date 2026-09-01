/-
# The differentiation step, on an interval

`(ga)` showed the log junction is interval-local except for the lift, and supplied the lift. One step
upstream was still ray-shaped: `logRat_deriv_eq` consumes `deriv_eq_of_eq_on_ray`, so the identity it
produces was only available on `[X, ∞)`.

This module supplies both twins. The ray version takes `δ = x − X`, the distance to its **one**
boundary; an interval has two, so `δ` must be a positive number below both. `exists_pos_le_both`
produces one by trichotomy rather than by a `min` GLB lemma the corpus does not carry.

Nothing else in the proof moves: `div_hasDerivAt`, `logComp_hasDerivAt` and `hasDerivAt_pev` are all
pointwise already. That is the same pattern `(ga)` found — the arc's machinery was local throughout,
and the ray appeared only where a *lemma about locality* had been stated for a ray.

`deriv_eq_of_eq_on_interval` belongs beside `deriv_eq_of_eq_on_ray` in `GermDerivFbasis`; it is here
so this arc does not edit a 560-line module for two theorems. Move it if a second consumer appears.
-/
import MachLib.GermDerivFbasis
import MachLib.FPModel
import MachLib.LogRatDeriv
import MachLib.PolyIntervalIdentity

namespace MachLib

open Real


open Real

/-- A positive lower bound below two positive reals, without a `min` GLB lemma. -/
private theorem exists_pos_le_both {p q : Real} (hp : 0 < p) (hq : 0 < q) :
    ∃ d : Real, 0 < d ∧ d ≤ p ∧ d ≤ q := by
  rcases lt_total p q with h | h | h
  · exact ⟨p, hp, le_refl p, le_of_lt h⟩
  · exact ⟨p, hp, le_refl p, le_of_eq h⟩
  · exact ⟨q, hq, le_of_lt h, le_refl q⟩

/-- **The interval twin of `deriv_eq_of_eq_on_ray`.**

The ray version takes `δ = x − X`, the distance to its one boundary. An interval has two, so `δ` is
a positive number below both — and `exists_pos_le_both` supplies one by trichotomy rather than by a
`min` GLB lemma the corpus does not carry. Everything else, including `HasDerivAt_congr`'s two-sided
`|y − x| < δ`, is unchanged: a derivative is local, and an interior point of an interval is interior
for exactly the reason an interior point of a ray is. -/
theorem deriv_eq_of_eq_on_interval {f g : Real → Real} {a b x u v : Real}
    (hax : a < x) (hxb : x < b) (heq : ∀ y : Real, a < y → y < b → f y = g y)
    (hf : HasDerivAt f u x) (hg : HasDerivAt g v x) : u = v := by
  obtain ⟨d, hd, hda, hdb⟩ := exists_pos_le_both (sub_pos_of_lt hax) (sub_pos_of_lt hxb)
  have hagree : ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y = g y := by
    refine ⟨d, hd, fun y hy => heq y ?_ ?_⟩
    · -- a < y : from  -(y-x) ≤ |y-x| < d ≤ x-a
      have hA : -(y - x) < d := lt_of_le_of_lt (neg_le_abs (y - x)) hy
      have hB : -(y - x) < x - a := lt_of_lt_of_le hA hda
      have hC := add_lt_add_left hB (y - x + a)
      have l : y - x + a + -(y - x) = a := by mach_mpoly [a, x, y]
      have r : y - x + a + (x - a) = y := by mach_mpoly [a, x, y]
      rw [l, r] at hC
      exact hC
    · -- y < b : from  y-x ≤ |y-x| < d ≤ b-x
      have hA : y - x < d := lt_of_le_of_lt (le_abs_self (y - x)) hy
      have hB : y - x < b - x := lt_of_lt_of_le hA hdb
      have hC := add_lt_add_left hB x
      have l : x + (y - x) = y := by mach_mpoly [b, x, y]
      have r : x + (b - x) = b := by mach_mpoly [b, x, y]
      rw [l, r] at hC
      exact hC
  exact HasDerivAt_unique g u v x (HasDerivAt_congr f g u x hagree hf) hg

/-- **`logRat_deriv_eq` on an interval.** The ray proof verbatim, with the ray's one-sided
hypothesis replaced by two-sided bounds and `deriv_eq_of_eq_on_ray` swapped for the twin above.
Nothing else moves — `div_hasDerivAt`, `logComp_hasDerivAt` and `hasDerivAt_pev` are all pointwise
already. -/
theorem logRat_deriv_eq_on_interval {P Q N D : List Real} {a b : Real}
    (hQ : ∀ x : Real, a < x → x < b → pev Q x ≠ 0)
    (hD : ∀ x : Real, a < x → x < b → pev D x ≠ 0)
    (hpos : ∀ x : Real, a < x → x < b → 0 < pev P x / pev Q x)
    (hlog : ∀ x : Real, a < x → x < b → log (pev P x / pev Q x) = pev N x / pev D x) :
    ∀ x : Real, a < x → x < b →
      ((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x))
          / (pev P x / pev Q x)
        = (pev (pderiv N) x * pev D x - pev N x * pev (pderiv D) x) / (pev D x * pev D x) := by
  intro x hax hxb
  have hSder : HasDerivAt (fun t => pev P t / pev Q t)
      ((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x)) x :=
    div_hasDerivAt (hasDerivAt_pev P x) (hasDerivAt_pev Q x) (hQ x hax hxb)
  have hL : HasDerivAt (fun t => log (pev P t / pev Q t))
      (((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x))
        / (pev P x / pev Q x)) x :=
    logComp_hasDerivAt hSder (hpos x hax hxb)
  have hR : HasDerivAt (fun t => pev N t / pev D t)
      ((pev (pderiv N) x * pev D x - pev N x * pev (pderiv D) x) / (pev D x * pev D x)) x :=
    div_hasDerivAt (hasDerivAt_pev N x) (hasDerivAt_pev D x) (hD x hax hxb)
  exact deriv_eq_of_eq_on_interval hax hxb hlog hL hR

/-! ## The composition, written

`(gb)` recorded that the four pieces "line up by shape" and stopped there, because a chain that type-
checks in prose is not a theorem. Written out below, it is three lines: differentiate on the interval,
clear denominators pointwise, lift.

What it does **not** do is show the hypotheses are jointly satisfiable for an actual germ. A theorem
whose hypotheses nothing can instantiate is vacuous and every gate still passes — this project has
paid for that lesson once, and the witness audit exists because of it.
-/

/-- **`hident` from an interval-local hypothesis.** The composition `(gb)` said lined up by shape,
written out: differentiate on the interval, clear denominators pointwise, lift to `PEq`.

This is `no_rational_logarithm`'s tenth hypothesis produced from "`log (P/Q)` agrees with `N/D` on an
open interval" — no tail, no growth premise, nothing eventual. -/
theorem hident_of_log_rational_on_interval {P Q N D : List Real} {a b : Real} (hab : a < b)
    (hQ : ∀ x : Real, a < x → x < b → pev Q x ≠ 0)
    (hD : ∀ x : Real, a < x → x < b → pev D x ≠ 0)
    (hP : ∀ x : Real, a < x → x < b → pev P x ≠ 0)
    (hpos : ∀ x : Real, a < x → x < b → 0 < pev P x / pev Q x)
    (hlog : ∀ x : Real, a < x → x < b → log (pev P x / pev Q x) = pev N x / pev D x) :
    PEq (pmul (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (pmul D D))
        (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul Q P)) := by
  refine peq_of_eq_on_interval (a := a) (b := b) hab ?_
  intro x h1 h2
  have hcross := logRat_cross_identity (hQ x h1 h2) (hD x h1 h2) (hP x h1 h2)
    (logRat_deriv_eq_on_interval hQ hD hpos hlog x h1 h2)
  simpa [pev_pmul, pev_psub] using hcross

end MachLib
