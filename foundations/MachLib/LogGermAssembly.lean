import MachLib.LogDerivCleared
import MachLib.DerivQuotientLog
import MachLib.GermDerivFbasis
import MachLib.GermClearedSpecimen
import MachLib.PolyConstDvd

/-!
# Route `(fm)`, assembled: a rational germ's logarithm is not a rational germ

The three legs were proved separately and this file composes them. Nothing here is new
mathematics — every step below already existed — which is the point: the remaining work on
`(fm)` was an assembly, and an assembly is not a theorem until it typechecks.

    leg 1  differentiate the germ identity   deriv_eq_of_eq_on_ray   (GermDerivFbasis)
           the two derivative rules          logComp_hasDerivAt,
                                             div_hasDerivAt          (DerivQuotientLog)
    leg 2  clear denominators                logderiv_count_composes (LogDerivCleared)
    leg 3  pointwise → PEq                   peq_of_ev_eq            (PevEvEq, inside leg 2)

## The one genuinely missing step was arithmetic, not analysis

`logComp_hasDerivAt` yields the derivative as `s / S x` — the quotient of `S`'s derivative by `S`
itself — while the `q`-adic count wants a single fraction over `P·Q`. With `S = P/Q` and
`s = (P'Q − PQ')/(Q·Q)` those are the same number, and `logderiv_normalise` is the cancellation
that says so. It is the only lemma this file adds.

## Scope, stated at the width the count actually has

`no_rational_logarithm` needs a **genuine pole**: an irreducible `q` with `q^(r+1) ‖ Q` and
`q ∤ P`. So this covers a rational germ whose denominator really has a pole, and **not** the
polynomial case — `S = x` has `Q = 1`, no irreducible divides it, and the count is silent. The
usual repair is to run the argument on `1/S` instead (`log (1/S) = −log S`, and `1/S = Q/P` has a
pole wherever `P` vanishes), but that needs `P` non-constant and is a separate step; it is not
claimed here.

**The ledger does not move.** `BoundedGermTranscendence` consumes `not RatGerm (log ∘ S)` through
further steps that are not this file, and the obligation stays open. What changed is that the
route's last unproved leg is proved and the composition is machine-checked rather than asserted.
-/

namespace MachLib
open Real

/-- `p/q ≠ 0` for `p, q ≠ 0`. -/
theorem div_ne_zero' {p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) : p / q ≠ 0 := by
  rw [div_def p q hq]
  exact mul_ne_zero hp (one_div_ne_zero hq)

/-- **The logarithmic-derivative normalisation.** `(u/(q·q)) / (p/q) = u/(p·q)`.

This is the whole arithmetic content of the assembly: `logComp_hasDerivAt` hands back `S'/S` as a
quotient of quotients, and the `q`-adic count wants one fraction over `P·Q`. Proved by cancelling
`p·q`, which turns the goal into a single `mach_mpoly` identity over the reciprocals as atoms —
the same shape `div_hasDerivAt` uses one module over. -/
theorem logderiv_normalise {u p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) :
    (u / (q * q)) / (p / q) = u / (p * q) := by
  have hqq : q * q ≠ 0 := mul_ne_zero hq hq
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  have hpdq : p / q ≠ 0 := div_ne_zero' hp hq
  have key : (1 / (q * q)) * (1 / (p / q)) = 1 / (p * q) := by
    refine mul_left_cancel hpq ?_
    rw [mul_inv (p * q) hpq]
    have h1 : (p / q) * (1 / (p / q)) = 1 := mul_inv (p / q) hpdq
    have h2 : (q * q) * (1 / (q * q)) = 1 := mul_inv (q * q) hqq
    have h3 : q * (1 / q) = 1 := mul_inv q hq
    have e : ((p / q) * (1 / (p / q))) * ((q * q) * (1 / (q * q)))
           = ((p * q) * ((1 / (q * q)) * (1 / (p / q)))) * (q * (1 / q)) := by
      rw [div_def p q hq]
      mach_mpoly [p, q, 1 / q, 1 / (q * q), 1 / (p / q)]
    rw [h1, h2, h3] at e
    rw [show (1 : Real) * 1 = 1 from by mach_ring] at e
    rw [mul_one_ax ((p * q) * ((1 / (q * q)) * (1 / (p / q))))] at e
    exact e.symm
  rw [div_def (u / (q * q)) (p / q) hpdq, div_def u (q * q) hqq, div_def u (p * q) hpq,
      mul_assoc, key]

/-- **Route `(fm)`, assembled.** A rational germ `S = P/Q` that is positive on a ray, whose
denominator has a genuine pole at the irreducible `q`, has no rational germ for `log ∘ S`.

Every step is cited, none is new: the two derivative rules (`DerivQuotientLog`), the ray step
(`GermDerivFbasis`), the cleared identity and the `q`-adic count (`LogDerivCleared`, `PolyLogDeriv`).
The only arithmetic added is `logderiv_normalise`.

The ray is opened by one: leg 1 needs a two-sided neighbourhood, so the derivative identity holds
on `X < x` and the count is fed from `X + 1` — a derivative is local, and the endpoint of `[X, ∞)`
has no interior. -/
theorem no_rational_log_germ {q P Q Qt N D : List Real} {X : Real}
    (hq : PIrred q) (hchar : ∀ rr : Nat, DerivCoprime q (rr + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    {r : Nat} (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hDnorm : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q N)
    (hX : 1 ≤ X)
    (hQne : ∀ x : Real, X ≤ x → pev Q x ≠ 0)
    (hPne : ∀ x : Real, X ≤ x → pev P x ≠ 0)
    (hDne : ∀ x : Real, X ≤ x → pev D x ≠ 0)
    (hSpos : ∀ x : Real, X ≤ x → 0 < pev P x / pev Q x)
    (hlog : ∀ x : Real, X ≤ x → log (pev P x / pev Q x) = pev N x / pev D x) :
    False := by
  have hX1 : (1 : Real) ≤ X + 1 := le_trans hX (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))
  have hstep : ∀ x : Real, X + 1 ≤ x → X ≤ x ∧ X < x := by
    intro x hx
    have hlt : X < X + 1 := lt_add_of_pos_right zero_lt_one_ax
    exact ⟨le_of_lt (lt_of_lt_of_le hlt hx), lt_of_lt_of_le hlt hx⟩
  refine logderiv_count_composes (q := q) (Qt := Qt) hX1 hq hchar hPd hPn hNn hQ hQtd
    hDnorm hlow ?_ ?_ ?_
  · intro x hx
    rw [pev_pmul]
    exact mul_ne_zero (hPne x (hstep x hx).1) (hQne x (hstep x hx).1)
  · intro x hx
    rw [pev_pmul]
    exact mul_ne_zero (hDne x (hstep x hx).1) (hDne x (hstep x hx).1)
  · intro x hx
    obtain ⟨hxle, hxlt⟩ := hstep x hx
    -- leg 1: both sides are differentiable at `x`, and they agree on the ray
    have hSd := div_hasDerivAt (hasDerivAt_pev P x) (hasDerivAt_pev Q x) (hQne x hxle)
    have hLd := logComp_hasDerivAt hSd (hSpos x hxle)
    have hRd := div_hasDerivAt (hasDerivAt_pev N x) (hasDerivAt_pev D x) (hDne x hxle)
    have heq := deriv_eq_of_eq_on_ray hxlt hlog hLd hRd
    -- the quotient-of-quotients is one fraction over `P·Q`
    rw [logderiv_normalise (hPne x hxle) (hQne x hxle)] at heq
    rw [pev_psub, pev_pmul, pev_pmul, pev_pmul, pev_psub, pev_pmul, pev_pmul, pev_pmul]
    exact heq

private theorem not_evZeroF_pev_one' : ¬ EvZeroF (pev ([1] : List Real)) := by
  intro ⟨Y, hY, h⟩
  have hz := h Y (le_refl Y)
  rw [pev_one] at hz
  exact zero_ne_one_ax hz.symm

private theorem pnorm_one_ne_nil' : pnorm ([1] : List Real) ≠ [] :=
  pnorm_ne_nil_of_not_evZero not_evZeroF_pev_one'

private theorem pNormal_one' : PNormal ([1] : List Real) := by
  intro c hc
  have h1 : (1 : Real) = c := by simpa using hc
  rw [← h1]
  exact fun h => zero_ne_one_ax h.symm

private theorem len_one_le : ([1] : List Real).length ≤ 1 := Nat.le_refl 1

private theorem peq_Q_specimen :
    PEq ([0, 1] : List Real) (pmul (ppow ([0, 1] : List Real) (0 + 1)) [1]) := by
  refine peq_of_ev_eq (le_refl (1 : Real)) (fun y _ => ?_)
  show pev ([0, 1] : List Real) y
       = pev (pmul (pmul ([0, 1] : List Real) [1]) [1]) y
  rw [pev_pmul, pev_pmul, pev_one, mul_one_ax, mul_one_ax]

/-! ### The specimen — because `witness_audit` is structurally blind here

`no_rational_log_germ` concludes `False`, so it falls in the audit's *"refutation theorem(s) NOT
APPLICABLE"* bucket: a green `WITNESS-AUDIT OK` says nothing whatever about it. That is the exact
shape `positive_branch_impossible` had when it was vacuous for weeks with every gate green, so the
check has to be made by hand.

A full specimen is impossible on purpose — discharging `hlog` too would prove `False`. What must be
shown is that **every OTHER hypothesis is jointly satisfiable**, so that the theorem's content is
"and therefore `hlog` is false" rather than "these premises are contradictory for some unrelated
reason". `S = 1/x` does it: `q = x` is irreducible, `Q = q¹·1` is a genuine pole, and `1/x > 0` on
`[1, ∞)`. -/
theorem no_rational_log_germ_specimen
    (hlog : ∀ x : Real, (1 : Real) ≤ x →
        log (pev ([1] : List Real) x / pev ([0, 1] : List Real) x)
          = pev ([1] : List Real) x / pev ([1] : List Real) x) : False := by
  refine no_rational_log_germ (q := [0, 1]) (P := [1]) (Q := [0, 1]) (Qt := [1])
    (N := [1]) (D := [1]) (X := 1) (r := 0)
    pIrred_X derivCoprime_X ?_ ?_ ?_ ?_ ?_ ?_ ?_ (le_refl 1) ?_ ?_ ?_ ?_ hlog
  · exact not_Pdvd_const pIrred_X pnorm_one_ne_nil' len_one_le
  · exact pNormal_one'
  · exact pNormal_one'
  · exact peq_Q_specimen
  · exact not_Pdvd_const pIrred_X pnorm_one_ne_nil' len_one_le
  · exact pnorm_one_ne_nil'
  · intro h; exact absurd h (not_Pdvd_const pIrred_X pnorm_one_ne_nil' len_one_le)
  · intro x hx; rw [pev_X]; exact ne_of_gt (lt_of_lt_of_le zero_lt_one_ax hx)
  · intro x hx; rw [pev_one]; exact ne_of_gt zero_lt_one_ax
  · intro x hx; rw [pev_one]; exact ne_of_gt zero_lt_one_ax
  · intro x hx
    rw [pev_one, pev_X]
    exact div_pos_of_pos_pos zero_lt_one_ax (lt_of_lt_of_le zero_lt_one_ax hx)

end MachLib
