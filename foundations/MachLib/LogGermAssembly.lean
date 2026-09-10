import MachLib.LogDerivCleared
import MachLib.DerivQuotientLog
import MachLib.GermDerivFbasis
import MachLib.GermClearedSpecimen
import MachLib.PolyConstDvd
import MachLib.OperatorBasisComplete

/-!
# Route `(fm)`, assembled: a rational germ's logarithm is not a rational germ

The three legs were proved separately and this file composes them. Nothing here is new
mathematics — every step below already existed — which is the point: the remaining work on
`(fm)` was an assembly, and an assembly is not a theorem until it typechecks.

    leg 1  differentiate the germ identity   deriv_eq_of_eq_on_ray   (GermDerivFbasis)
           the two derivative rules          logComp_hasDerivAt,
                                             div_hasDerivAt          (DerivQuotientLog)
    leg 2  clear denominators                logRat_cross_identity   (LogRatDeriv)
                                             peq_of_ev_eq promotion  (LogDerivCleared)
    leg 3  pointwise → PEq                   peq_of_ev_eq            (PevEvEq, inside leg 2)

## The one genuinely missing step was arithmetic, not analysis

`logComp_hasDerivAt` yields the derivative as `s / S x` — the quotient of `S`'s derivative by `S`
itself — while the `q`-adic count wants a single fraction over `P·Q`. With `S = P/Q` and
`s = (P'Q − PQ')/(Q·Q)` those are the same number. A first version of this file proved that
cancellation itself; `LogRatDeriv.logRat_cross_identity` already did it, in one step and with a
better argument (multiply through by `Q·Q`, which cancels the left quotient outright), and is cited
instead.

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

/-- **Route `(fm)`, assembled.** A rational germ `S = P/Q` that is positive on a ray, whose
denominator has a genuine pole at the irreducible `q`, has no rational germ for `log ∘ S`.

Every step is cited, none is new: the two derivative rules (`DerivQuotientLog`), the ray step
(`GermDerivFbasis`), the cleared identity and the `q`-adic count (`LogDerivCleared`, `PolyLogDeriv`).
The only genuinely new content is the germ-level packaging, the numerator-pole case, and the specimen.

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
    -- leg 1, ALREADY COMPOSED in `LogRatDeriv`: the derivatives agree on the OPEN ray
    have heq := logRat_deriv_eq hQne hDne hSpos hlog x hxlt
    -- and `LogRatDeriv` already clears it in one step, by multiplying through by `Q·Q`
    have hcross := logRat_cross_identity (hQne x hxle) (hDne x hxle) (hPne x hxle) heq
    have hcomm : pev Q x * pev P x = pev P x * pev Q x := by mach_ring
    rw [hcomm] at hcross
    rw [pev_psub, pev_pmul, pev_pmul, pev_pmul, pev_psub, pev_pmul, pev_pmul, pev_pmul]
    exact div_eq_div_of_cross (mul_ne_zero (hPne x hxle) (hQne x hxle))
      (mul_ne_zero (hDne x hxle) (hDne x hxle)) hcross

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

/-! ### The numerator-pole case, via `1/S`

`no_rational_logarithm` needs the pole in the DENOMINATOR, so `no_rational_log_germ` is silent on a
germ like `S = x` where `Q` is constant. The repair is to run the argument on `1/S = Q/P`, which has
a pole wherever `P` vanishes, and the only germ-level content is that inverting `S` negates its
logarithm. Together the two cover every non-constant rational germ in lowest terms: `S` non-constant
means `P` or `Q` is non-constant, hence has an irreducible factor, and lowest terms says that factor
misses the other. -/

/-- `pscale` by a NON-ZERO scalar preserves `PNormal`: it multiplies the last coefficient, and a
product of non-zeros is non-zero. -/
theorem pNormal_pscale {r : Real} (hr : r ≠ 0) :
    ∀ {L : List Real}, PNormal L → PNormal (pscale r L)
  | [], _ => by intro c hc; exact absurd hc (by simp [pscale])
  | [a], h => by
      intro c hc
      have ha : a ≠ 0 := h a (by simp)
      have : c = r * a := by simpa [pscale] using hc.symm
      rw [this]; exact mul_ne_zero hr ha
  | a :: b :: L, h => by
      intro c hc
      have hrest : PNormal (b :: L) := by
        intro d hd; exact h d (by simpa using hd)
      exact pNormal_pscale hr hrest c (by simpa [pscale] using hc)

/-- **Inverting a rational germ negates its logarithm.** `log (Q/P) = (−N)/D` from
`log (P/Q) = N/D`, on a ray where `P` and `Q` are positive. `log_div` twice, then `neg_div`. -/
theorem log_recip_germ {P Q N D : List Real} {X : Real}
    (hPpos : ∀ x : Real, X ≤ x → 0 < pev P x)
    (hQpos : ∀ x : Real, X ≤ x → 0 < pev Q x)
    (hDne : ∀ x : Real, X ≤ x → pev D x ≠ 0)
    (h : ∀ x : Real, X ≤ x → log (pev P x / pev Q x) = pev N x / pev D x) :
    ∀ x : Real, X ≤ x →
      log (pev Q x / pev P x) = pev (pscale (0 - 1) N) x / pev D x := by
  intro x hx
  have hfwd : log (pev P x / pev Q x) = log (pev P x) - log (pev Q x) :=
    log_div (hPpos x hx) (hQpos x hx)
  have hbwd : log (pev Q x / pev P x) = log (pev Q x) - log (pev P x) :=
    log_div (hQpos x hx) (hPpos x hx)
  have hneg : log (pev Q x / pev P x) = -(log (pev P x / pev Q x)) := by
    rw [hfwd, hbwd]; mach_ring
  rw [hneg, h x hx, neg_div (hDne x hx), pev_pscale]
  have : (0 - 1) * pev N x = -(pev N x) := by mach_ring
  rw [this]

/-- `0 - 1 ≠ 0`, the scalar `pscale` negates by. -/
private theorem sub_one_ne_zero : (0 - 1 : Real) ≠ 0 := by
  have e : (0 - 1 : Real) = -(1 : Real) := by mach_ring
  rw [e]
  exact ne_of_lt (neg_neg_of_pos zero_lt_one_ax)

/-- **The numerator-pole case.** Same conclusion as `no_rational_log_germ` when the genuine pole
sits in `P` rather than `Q` — obtained by running that theorem on `1/S = Q/P`, whose logarithm is
`(−N)/D`. Nothing new is proved; the two together cover every non-constant rational germ in lowest
terms. -/
theorem no_rational_log_germ_num_pole {q P Pt Q N D : List Real} {X : Real}
    (hq : PIrred q) (hchar : ∀ rr : Nat, DerivCoprime q (rr + 1))
    (hQd : ¬ Pdvd q Q) (hQn : PNormal Q) (hNn : PNormal N)
    {r : Nat} (hP : PEq P (pmul (ppow q (r + 1)) Pt)) (hPtd : ¬ Pdvd q Pt)
    (hDnorm : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q (pscale (0 - 1) N))
    (hX : 1 ≤ X)
    (hPpos : ∀ x : Real, X ≤ x → 0 < pev P x)
    (hQpos : ∀ x : Real, X ≤ x → 0 < pev Q x)
    (hDne : ∀ x : Real, X ≤ x → pev D x ≠ 0)
    (hlog : ∀ x : Real, X ≤ x → log (pev P x / pev Q x) = pev N x / pev D x) :
    False :=
  no_rational_log_germ (q := q) (P := Q) (Q := P) (Qt := Pt)
    (N := pscale (0 - 1) N) (D := D)
    hq hchar hQd hQn (pNormal_pscale sub_one_ne_zero hNn) hP hPtd hDnorm hlow hX
    (fun x hx => ne_of_gt (hPpos x hx))
    (fun x hx => ne_of_gt (hQpos x hx))
    hDne
    (fun x hx => div_pos_of_pos_pos (hQpos x hx) (hPpos x hx))
    (log_recip_germ hPpos hQpos hDne hlog)

/-- `PEq` is `pnorm`-equality, so equal polynomials evaluate equally. -/
private theorem pev_of_peq {A B : List Real} (h : PEq A B) (x : Real) : pev A x = pev B x := by
  rw [← pev_pnorm A, h, pev_pnorm B]

/-- `Pdvd` only looks at `pnorm`, so it transfers back off a normalisation. -/
private theorem Pdvd_of_pnorm {q A : List Real} (h : Pdvd q (pnorm A)) : Pdvd q A := by
  obtain ⟨M, hM, hEq⟩ := h
  exact ⟨M, hM, by rw [← pnorm_idem A]; exact hEq⟩

/-! ### The germ-level form: no rational germ AT ALL, not just this one

`no_rational_log_germ` refutes a NAMED candidate primitive `N/D`. `¬ RatGerm (log ∘ S)` says no
candidate exists, and the gap between them is that `RatGerm` hands over an arbitrary `N`, `D` —
nothing says the fraction is in lowest terms at `q`, which `no_rational_logarithm`'s `q ∣ D` branch
needs. `CrossIdentities.exists_common_ord_split` closes it: it peels a common `q`-power off both and
returns exactly `Pdvd q N₁ → ¬ Pdvd q D₁`.

Two details that make the peel free rather than fiddly. The cancelled factor is never zero on the
ray — `pev D x = pev (qˢ) x · pev D₁ x` and `pev D x ≠ 0`, so both factors are non-zero, and no
root-counting is needed. And the degenerate `N ≡ 0` case is not a nuisance but a separate small
argument: it forces `log (P/Q) ≡ 0`, hence `P/Q ≡ 1` by `exp_log`, hence `PEq P Q`, hence `q ∣ P`
because `q ∣ Q` — contradicting the pole hypothesis directly. -/
theorem not_ratGerm_log_of_pole {q P Q Qt : List Real} {X : Real} {r : Nat}
    (hq : PIrred q) (hchar : ∀ rr : Nat, DerivCoprime q (rr + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hX : 1 ≤ X)
    (hPpos : ∀ x : Real, X ≤ x → 0 < pev P x)
    (hQpos : ∀ x : Real, X ≤ x → 0 < pev Q x) :
    ¬ RatGerm (fun x => log (pev P x / pev Q x)) := by
  rintro ⟨N, D, X', hX', hDne, hlog⟩
  obtain ⟨Y, hY1, hYX, hYX'⟩ := two_bounds' hX hX'
  have hPposY : ∀ x : Real, Y ≤ x → 0 < pev P x := fun x hx => hPpos x (le_trans hYX hx)
  have hQposY : ∀ x : Real, Y ≤ x → 0 < pev Q x := fun x hx => hQpos x (le_trans hYX hx)
  have hDneY : ∀ x : Real, Y ≤ x → pev D x ≠ 0 := fun x hx => hDne x (le_trans hYX' hx)
  have hlogY : ∀ x : Real, Y ≤ x → log (pev P x / pev Q x) = pev N x / pev D x :=
    fun x hx => hlog x (le_trans hYX' hx)
  -- `q ∣ Q`, from the pole factorisation. Used by the degenerate branch.
  have hqQ : Pdvd q Q := by
    refine Pdvd_of_peq (PEq.trans hQ ?_) (Pdvd_pmul_self q (pmul (ppow q r) Qt))
    show PEq (pmul (pmul q (ppow q r)) Qt) (pmul q (pmul (ppow q r) Qt))
    exact peq_pmul_assoc q (ppow q r) Qt
  rcases Classical.em (pnorm N = []) with hN0 | hN0
  · -- `N ≡ 0`: then `log (P/Q) ≡ 0`, so `P ≡ Q` on the ray, so `q ∣ P`.
    refine hPd (Pdvd_of_peq (peq_of_ev_eq hY1 (fun x hx => ?_)) hqQ)
    have h0 : log (pev P x / pev Q x) = 0 := by
      rw [hlogY x hx, pev_eq_zero_of_pnorm_nil hN0, zero_div]
    have hpos : 0 < pev P x / pev Q x := div_pos_of_pos_pos (hPposY x hx) (hQposY x hx)
    have h1 : pev P x / pev Q x = 1 := by
      rw [← exp_log hpos, h0, exp_zero]
    have := mul_div_cancel_left (ne_of_gt (hQposY x hx)) (a := pev P x)
    rw [h1, mul_one_ax] at this
    exact this.symm
  · -- the general case: peel the common `q`-power, then apply the named-candidate theorem
    have hDn0 : pnorm D ≠ [] := by
      refine pnorm_ne_nil_of_not_evZero ?_
      rintro ⟨Z, hZ, hz⟩
      obtain ⟨W, hW1, hWY, hWZ⟩ := two_bounds' hY1 hZ
      exact hDneY W hWY (hz W hWZ)
    obtain ⟨s, N₁, D₁, hNs, hDs, hsplit⟩ := exists_common_ord_split hq hN0 hDn0
    -- the peeled factor is non-zero on the ray because `pev D` is: a product is zero only if a
    -- factor is, so no root-counting is needed to justify the cancellation
    have hfac : ∀ x : Real, Y ≤ x → pev (ppow q s) x ≠ 0 ∧ pev D₁ x ≠ 0 := by
      intro x hx
      have hD : pev D x = pev (ppow q s) x * pev D₁ x := by
        rw [pev_of_peq hDs, pev_pmul]
      refine ⟨fun h => hDneY x hx ?_, fun h => hDneY x hx ?_⟩
      · rw [hD, h, zero_mul]
      · rw [hD, h, mul_zero]
    have hD₁ne : ∀ x : Real, Y ≤ x → pev D₁ x ≠ 0 := fun x hx => (hfac x hx).2
    have hD₁n : pnorm D₁ ≠ [] := by
      refine pnorm_ne_nil_of_not_evZero ?_
      rintro ⟨Z, hZ, hz⟩
      obtain ⟨W, hW1, hWY, hWZ⟩ := two_bounds' hY1 hZ
      exact hD₁ne W hWY (hz W hWZ)
    -- the germ identity, in the reduced fraction
    have hlog₁ : ∀ x : Real, Y ≤ x →
        log (pev P x / pev Q x) = pev (pnorm N₁) x / pev (pnorm D₁) x := by
      intro x hx
      rw [pev_pnorm, pev_pnorm, hlogY x hx, pev_of_peq hNs, pev_of_peq hDs, pev_pmul, pev_pmul]
      exact div_eq_div_of_cross (mul_ne_zero (hfac x hx).1 (hD₁ne x hx)) (hD₁ne x hx)
        (by mach_ring)
    refine no_rational_log_germ hq hchar hPd hPn (pnorm_normal N₁) hQ hQtd
      (by rw [pnorm_idem]; exact hD₁n) (fun hd => ?_) hY1
      (fun x hx => ne_of_gt (hQposY x hx)) (fun x hx => ne_of_gt (hPposY x hx))
      (fun x hx => by rw [pev_pnorm]; exact hD₁ne x hx)
      (fun x hx => div_pos_of_pos_pos (hPposY x hx) (hQposY x hx)) hlog₁
    -- `hlow`: `exists_common_ord_split` returns exactly this, modulo `pnorm`
    refine Pdvd_pnorm (fun hn => hsplit hn (Pdvd_of_pnorm hd))

/-! ### The separation — route A's remaining step

`subMul_summand_top_vanishes` establishes that the only `log`-carrying summand dies at the top
degree, so each proportionality equation reads `A(x) + B(x)·log (S x) ≡ 0` with `A`, `B` free of
`log`. This is what that shape buys once `log ∘ S` is known not to be a rational germ: **`B` is
eventually zero.**

The mathematics is one step; the care is in one hypothesis. "Not eventually zero" does NOT give a
zero-free tail for a general germ — it can dodge zero infinitely often — and the division below
needs one. That is exactly where `B` has to be a RATIONAL germ: it is `pev U / pev V`, and
`evNonvanish_pev` turns `¬ EvZeroF (pev U)` into a tail. On that tail `log (S x) = −A x / B x`, a
quotient of rational germs and so rational, contradicting the hypothesis. -/
theorem log_separation {S A B : Real → Real} {X : Real}
    (hnr : ¬ RatGerm (fun x => log (S x)))
    (hA : RatGerm A) (hB : RatGerm B) (hX : 1 ≤ X)
    (h : ∀ x : Real, X ≤ x → A x + B x * log (S x) = 0) :
    EvZeroF B := by
  -- `by_contra` does not exist here (CLAUDE.md; `by-contra-absent` in the absence registry) —
  -- the local idiom is an explicit `Classical.em` split.
  rcases Classical.em (EvZeroF B) with hgood | hB0
  · exact hgood
  exfalso
  obtain ⟨Ua, Va, Xa, hXa, hVa, hAdef⟩ := hA
  obtain ⟨Ub, Vb, Xb, hXb, hVb, hBdef⟩ := hB
  have hUb : ¬ EvZeroF (pev Ub) := by
    rintro ⟨Z, hZ, hz⟩
    obtain ⟨W, hW1, hWb, hWZ⟩ := two_bounds' hXb hZ
    exact hB0 ⟨W, hW1, fun x hx => by
      rw [hBdef x (le_trans hWb hx), hz x (le_trans hWZ hx), zero_div]⟩
  obtain ⟨Xn, hXn, hUbne⟩ := evNonvanish_pev hUb
  obtain ⟨Y1, hY1, hY1a, hY1b⟩ := two_bounds' hXa hXb
  obtain ⟨Y2, hY2, hY2n, hY2X⟩ := two_bounds' hXn hX
  obtain ⟨Y, hY, hYY1, hYY2⟩ := two_bounds' hY1 hY2
  have hva : ∀ x : Real, Y ≤ x → pev Va x ≠ 0 :=
    fun x hx => hVa x (le_trans (le_trans hY1a hYY1) hx)
  have hvb : ∀ x : Real, Y ≤ x → pev Vb x ≠ 0 :=
    fun x hx => hVb x (le_trans (le_trans hY1b hYY1) hx)
  have hub : ∀ x : Real, Y ≤ x → pev Ub x ≠ 0 :=
    fun x hx => hUbne x (le_trans (le_trans hY2n hYY2) hx)
  refine hnr ⟨pscale (0 - 1) (pmul Ua Vb), pmul Va Ub, Y, hY,
    (fun x hx => by rw [pev_pmul]; exact mul_ne_zero (hva x hx) (hub x hx)), fun x hx => ?_⟩
  have h0 := h x (le_trans (le_trans hY2X hYY2) hx)
  rw [hAdef x (le_trans (le_trans hY1a hYY1) hx),
      hBdef x (le_trans (le_trans hY1b hYY1) hx)] at h0
  -- clear both denominators by multiplying through by `va·vb`
  have hclear : pev Ua x * pev Vb x + (pev Va x * pev Ub x) * log (S x) = 0 := by
    have e2 := congrArg (fun z => (pev Va x * pev Vb x) * z) h0
    rw [show (pev Va x * pev Vb x)
          * (pev Ua x / pev Va x + (pev Ub x / pev Vb x) * log (S x))
        = pev Vb x * (pev Va x * (pev Ua x / pev Va x))
          + pev Va x * (pev Vb x * (pev Ub x / pev Vb x)) * log (S x) from by mach_ring,
        mul_div_cancel_left (hva x hx), mul_div_cancel_left (hvb x hx),
        show (pev Va x * pev Vb x) * (0 : Real) = 0 from by mach_ring] at e2
    rw [← e2]; mach_ring
  rw [pev_pscale, pev_pmul, pev_pmul]
  have hDen : pev Va x * pev Ub x ≠ 0 := mul_ne_zero (hva x hx) (hub x hx)
  -- NOT `rw [← hclear]`: the goal contains `0 - 1`, and that rewrite fires on ITS zero.
  have hLD : log (S x) * (pev Va x * pev Ub x) = (0 - 1) * (pev Ua x * pev Vb x) := by
    have e : (pev Va x * pev Ub x) * log (S x)
        = (0 - 1) * (pev Ua x * pev Vb x)
          + (pev Ua x * pev Vb x + (pev Va x * pev Ub x) * log (S x)) := by mach_ring
    rw [hclear, show (0 - 1) * (pev Ua x * pev Vb x) + 0
                   = (0 - 1) * (pev Ua x * pev Vb x) from by mach_ring] at e
    rw [show log (S x) * (pev Va x * pev Ub x)
           = (pev Va x * pev Ub x) * log (S x) from by mach_ring]
    exact e
  rw [div_def _ _ hDen, ← hLD,
      show log (S x) * (pev Va x * pev Ub x) * (1 / (pev Va x * pev Ub x))
         = log (S x) * ((pev Va x * pev Ub x) * (1 / (pev Va x * pev Ub x))) from by mach_ring,
      mul_inv _ hDen, mul_one_ax]

/-! ### WHERE `log_separation` ATTACHES — an open question, with the facts separated from the guess

Before wiring this into route A, settle which equation it applies to. There are two candidates and
they need DIFFERENT inputs, so guessing costs a session.

**Verified, by reading the sources:**

1. `fbasis_top_two_identity` (`GermDerivFbasis`) concludes over `exp (S x) + 1/S x`. Its statement
   contains **no `log`**. Separating it would be `A + B·exp (S x) ≡ 0`, needing
   `¬ RatGerm (exp ∘ S)`.
2. Every exclusion instrument here — `not_algebraic_of_dominates_exp`,
   `not_algebraic_of_dominated_by_exp`, and the `FS_not_algebraic_*` family — argues by GROWTH, and
   `BoundedGermEnvelope.polyEnvelope_of_Fbasis_floor` proves `F ∘ S` IS polynomially enveloped on
   the bounded branch. So `¬ RatGerm (exp ∘ S)` is not available there by any existing route.
3. `fbasis_relation_substituted` writes the multiplier as `s·u + s·(1/S − log S)`, so the
   SUBSTITUTED relation's coefficients carry `log` and are, coefficientwise,
   `A_j = es[j] + s·(gyd cs)[j−1] + s·(gyd cs)[j]/S` and `B_j = −s·(gyd cs)[j]`.
4. `fbasis_top_two_identity` has no consumer anywhere in `MachLib/`.

**RESOLVED — and it was checkable after all.** `top_two_multiplier_splits` (below) proves the
multiplier is `s·u + fbasisSubMul S s`. So in `A + B·log` form the top-two identity has `B` free of
`log` but `A` carrying `u = exp ∘ S + log ∘ S`, which by (2) is not a rational germ on this branch.
`log_separation` requires `RatGerm A`, so it does **not** apply to (1), and (3) is the only
remaining candidate.

**What the stopping rule bought.** The previous revision of this note recorded that as an INFERENCE
and refused to write it into CLAUDE.md as the route — three headers here asserted what was needed
and were wrong (`smoothstep_nonneg`, `GermDerivFbasis`, `LogRatDeriv`), each costing a wrong start.
Holding it as an inference for one step cost nothing and made the difference between recording a
guess and recording a theorem. The wiring itself is still open. -/

/-! ### The bridge to the obligation's own shape

`GEvRel`/`GProperRel` put NO rationality constraint on their coefficients — they are arbitrary
germs — so `log_separation`'s hypotheses do not come from the germ layer. They come from the
obligation, which supplies POLYNOMIAL coefficients (`bipevLead A Ls` in
`BoundedGermTranscendence`), and a polynomial is a rational germ with denominator `1`.

Small, and worth stating separately: the gap between "the shape is available" and "the route can
use it" is exactly this bridge, and it is easy to assume rather than write. -/

/-- `a / 1 = a`. -/
private theorem div_one' (a : Real) : a / 1 = a := by
  rw [div_def a 1 (ne_of_gt zero_lt_one_ax),
      show (1 : Real) / 1 = 1 * (1 / 1) from by rw [one_mul_thm],
      mul_inv 1 (ne_of_gt zero_lt_one_ax), mul_one_ax]

/-- **A polynomial is a rational germ**, with denominator `1`. -/
theorem ratGerm_pev (L : List Real) : RatGerm (fun x => pev L x) :=
  ⟨L, [1], 1, le_refl 1,
   fun x _ => by rw [pev_one]; exact ne_of_gt zero_lt_one_ax,
   fun x _ => by rw [pev_one, div_one']⟩

/-- **The separation at polynomial coefficients** — the form the obligation actually supplies. -/
theorem log_separation_pev {S : Real → Real} {A B : List Real} {X : Real}
    (hnr : ¬ RatGerm (fun x => log (S x))) (hX : 1 ≤ X)
    (h : ∀ x : Real, X ≤ x → pev A x + pev B x * log (S x) = 0) :
    EvZeroF (pev B) :=
  log_separation hnr (ratGerm_pev A) (ratGerm_pev B) hX h

/-! ### Settling the fork: the top-two identity is NOT in separable form

The note above left one step as an inference. It is now a theorem, and it decides the question.

`fbasis_top_two_identity`'s multiplier splits as `s·u + fbasisSubMul S s`, with `u = Fbasis ∘ S`.
Written in `A + B·log (S x)` form the identity therefore has

    B = −(m+1)·cd²·s          free of `log`
    A ∋ (m+1)·cd²·s·u         and `u x = exp (S x) + log (S x)`

so **`A` carries `u`, and `u` is not a rational germ** — on the bounded branch nothing can make it
one, since `polyEnvelope_of_Fbasis_floor` proves `F ∘ S` polynomially enveloped there and every
exclusion instrument argues by growth. `log_separation` requires `RatGerm A`. It therefore does NOT
apply to the top-two identity, and the substituted relation's coefficients are the only remaining
candidate.

That is now verified rather than guessed. What is still open is the wiring itself. -/

/-- **The chain-rule multiplier, split.** `(exp (S x) + 1/S x)·s x = s x·Fbasis (S x) + fbasisSubMul S s x`.

A ring identity in the atoms `exp (S x)`, `log (S x)`, `1/S x` — the `log`s cancel, which is exactly
why the split is available and why the residue `fbasisSubMul` is where the `log` ends up. -/
theorem top_two_multiplier_splits (S s : Real → Real) (x : Real) :
    (exp (S x) + 1 / S x) * s x = s x * Fbasis (S x) + fbasisSubMul S s x := by
  show (exp (S x) + 1 / S x) * s x
      = s x * (exp (S x) + log (S x)) + s x * (1 / S x - log (S x))
  mach_ring

/-! ### The wiring: each substituted coefficient IS an `A + B·log (S x)`

`top_two_multiplier_splits` settled that the separation attaches to the SUBSTITUTED relation, not to
the top-two identity. This performs the attachment at the level of a single coefficient, which is
where the descent compares them.

The `A` and `B` are exhibited, not merely asserted to exist, because the separation needs them to be
RATIONAL germs and that is a property of the exhibited expressions — `B = −s·(gyd cs)[j]` is rational
exactly when `s` and the relation's coefficients are, which is what the obligation's polynomial
`bipevLead A Ls` supplies and what `GEvRel` alone does not. -/

/-- **Each coefficient of the substituted relation splits as `A + B·log (S x)`.**

`A = es[j] + (s·(0 :: gyd cs))[j] + s·(1/S)·(gyd cs)[j]` and `B = −s·(gyd cs)[j]`, both free of
`log`. The only input is that `fbasisSubMul S s x = s x·(1/S x) + (0 − s x)·log (S x)`, a ring
identity — the same cancellation `top_two_multiplier_splits` runs on, one level down. -/
theorem substituted_coeff_splits {S s : Real → Real} {es cs : List (Real → Real)}
    {j : Nat} {p q r : Real → Real}
    (hp : es[j]? = some p)
    (hq : (gscale s ((fun _ => (0 : Real)) :: gyd cs))[j]? = some q)
    (hr : (gyd cs)[j]? = some r) :
    ∃ w : Real → Real,
      (gadd es (gadd (gscale s ((fun _ => (0 : Real)) :: gyd cs))
                     (gscale (fbasisSubMul S s) (gyd cs))))[j]? = some w
      ∧ ∀ x : Real,
          w x = (p x + q x + s x * (1 / S x) * r x)
                + ((0 - s x) * r x) * log (S x) := by
  refine ⟨_, gadd_getElem _ _ _ _ _ hp
      (gadd_getElem _ _ _ _ _ hq (gscale_getElem _ _ _ _ hr)), fun x => ?_⟩
  show p x + (q x + s x * (1 / S x - log (S x)) * r x)
      = (p x + q x + s x * (1 / S x) * r x) + ((0 - s x) * r x) * log (S x)
  mach_ring

/-! ### `RatGerm` is closed under the field operations

The instantiation step needs `RatGerm A` and `RatGerm B` for the `A`, `B` that
`substituted_coeff_splits` exhibits, and those are sums and products of the relation's
coefficients with `s` and `1/S`. **The corpus had no closure lemmas at all** — only
`ratGerm_sub_const`, which subtracts a constant. These are the general ones; they are reusable well
beyond this route, since `RatGerm` is the level-0 class the whole germ layer is stratified by. -/

/-- `(a·d + c·b)/(b·d) = a/b + c/d`. -/
private theorem div_add_div' {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a * d + c * b) / (b * d) = a / b + c / d := by
  refine div_of_eq_mul (mul_ne_zero hb hd) ?_
  rw [show (b * d) * (a / b + c / d) = d * (b * (a / b)) + b * (d * (c / d)) from by mach_ring,
      mul_div_cancel_left hb, mul_div_cancel_left hd]
  mach_ring

/-- `(a·c)/(b·d) = (a/b)·(c/d)`. -/
private theorem div_mul_div' {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a * c) / (b * d) = (a / b) * (c / d) := by
  refine div_of_eq_mul (mul_ne_zero hb hd) ?_
  rw [show (b * d) * ((a / b) * (c / d)) = (b * (a / b)) * (d * (c / d)) from by mach_ring,
      mul_div_cancel_left hb, mul_div_cancel_left hd]

/-- **`RatGerm` is closed under sum.** Common denominator `Qa·Qb`, on the merged ray. -/
theorem ratGerm_add {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x + g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨padd (pmul Pa Qb) (pmul Pb Qa), pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x + g x = _
    rw [pev_padd, pev_pmul, pev_pmul, pev_pmul,
        hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    exact (div_add_div' (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))).symm

/-- **`RatGerm` is closed under product.** -/
theorem ratGerm_mul {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x * g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨pmul Pa Pb, pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x * g x = _
    rw [pev_pmul, pev_pmul, hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    exact (div_mul_div' (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))).symm

/-- **`RatGerm` is closed under negation**, in the `0 − ·` form the corpus writes. -/
theorem ratGerm_neg {f : Real → Real} (hf : RatGerm f) :
    RatGerm (fun x => 0 - f x) := by
  obtain ⟨P, Q, X, hX, hQ, hfe⟩ := hf
  refine ⟨pscale (0 - 1) P, Q, X, hX, hQ, fun x hx => ?_⟩
  show (0 : Real) - f x = _
  rw [pev_pscale, hfe x hx]
  -- `neg_div` does not apply: the goal has `0 - _`, not `-(_)`, and `rw` matches syntactically
  refine (div_of_eq_mul (hQ x hx) ?_).symm
  rw [show pev Q x * (0 - pev P x / pev Q x) = 0 - pev Q x * (pev P x / pev Q x) from by mach_ring,
      mul_div_cancel_left (hQ x hx)]
  mach_ring

/-- **An explicit quotient of polynomials is a rational germ.** The definition, packaged — this is
what `S' = (P'Q − PQ')/Q²` and every other cleared derivative in the corpus already looks like. -/
theorem ratGerm_of_pev_div {N D : List Real} {X : Real} (hX : 1 ≤ X)
    (hD : ∀ x : Real, X ≤ x → pev D x ≠ 0) :
    RatGerm (fun x => pev N x / pev D x) :=
  ⟨N, D, X, hX, hD, fun _ _ => rfl⟩

/-- **The reciprocal of a non-vanishing rational germ is one**, `1/(P/Q) = Q/P`. Needs the
NUMERATOR non-vanishing too, which is exactly the `1/S` side condition route A carries. -/
theorem ratGerm_inv_of_pev {P Q : List Real} {X : Real} (hX : 1 ≤ X)
    (hP : ∀ x : Real, X ≤ x → pev P x ≠ 0)
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0) :
    RatGerm (fun x => 1 / (pev P x / pev Q x)) := by
  refine ⟨Q, P, X, hX, hP, fun x hx => ?_⟩
  show 1 / (pev P x / pev Q x) = pev Q x / pev P x
  refine div_eq_div_of_cross (div_ne_zero' (hP x hx) (hQ x hx)) (hP x hx) ?_
  rw [one_mul_thm, mul_div_cancel_left (hQ x hx)]

/-! ### Coefficientwise rationality is preserved by the list operations

`substituted_coeff_splits` exhibits `A` and `B` as combinations of `es`, `gyd cs`, `s` and `1/S`.
For `log_separation` those must be rational germs, so rationality has to survive `gadd`, `gscale`
and `gyd`. Stated over MEMBERSHIP rather than indices: `gadd`'s elements are heads, tails or sums,
which membership sees directly, whereas an index-based statement has to case on the two lists'
relative lengths at every step (`gadd_getElem` needs both, `gadd_getElem_left_none` the overhang). -/

/-- The zero germ is rational. -/
theorem ratGerm_zero : RatGerm (fun _ : Real => (0 : Real)) := by
  refine ⟨[], [1], 1, le_refl 1, fun x _ => by rw [pev_one]; exact ne_of_gt zero_lt_one_ax,
    fun x _ => ?_⟩
  show (0 : Real) = pev ([] : List Real) x / pev ([1] : List Real) x
  rw [pev_one, show pev ([] : List Real) x = 0 from rfl, zero_div]

/-- `gadd` preserves coefficientwise rationality. -/
theorem allRatGerm_gadd : ∀ (a b : List (Real → Real)),
    (∀ c ∈ a, RatGerm c) → (∀ c ∈ b, RatGerm c) → ∀ c ∈ gadd a b, RatGerm c := by
  intro a
  induction a with
  | nil => intro b _ hb c hc; exact hb c hc
  | cons d ds ih =>
      intro b ha hb c hc
      cases b with
      | nil => exact ha c hc
      | cons e es =>
          rcases List.mem_cons.mp hc with hhead | htail
          · rw [hhead]
            exact ratGerm_add (ha d (List.Mem.head _)) (hb e (List.Mem.head _))
          · exact ih es (fun z hz => ha z (List.Mem.tail _ hz))
              (fun z hz => hb z (List.Mem.tail _ hz)) c htail

/-- `gscale` preserves coefficientwise rationality, given a rational scalar. -/
theorem allRatGerm_gscale {v : Real → Real} (hv : RatGerm v) :
    ∀ (cs : List (Real → Real)), (∀ c ∈ cs, RatGerm c) → ∀ c ∈ gscale v cs, RatGerm c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; cases hc
  | cons d ds ih =>
      intro hcs c hc
      rcases List.mem_cons.mp hc with hhead | htail
      · rw [hhead]; exact ratGerm_mul hv (hcs d (List.Mem.head _))
      · exact ih (fun z hz => hcs z (List.Mem.tail _ hz)) c htail

/-- **`gyd` preserves coefficientwise rationality.** The formal `y`-derivative is built from `gadd`
and a zero-headed shift, so this is the two lemmas above plus `ratGerm_zero`. -/
theorem allRatGerm_gyd : ∀ (cs : List (Real → Real)),
    (∀ c ∈ cs, RatGerm c) → ∀ c ∈ gyd cs, RatGerm c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; cases hc
  | cons d ds ih =>
      intro hcs c hc
      have hds : ∀ z ∈ ds, RatGerm z := fun z hz => hcs z (List.Mem.tail _ hz)
      refine allRatGerm_gadd ds ((fun _ => (0 : Real)) :: gyd ds) hds ?_ c hc
      intro z hz
      rcases List.mem_cons.mp hz with hhead | htail
      · rw [hhead]; exact ratGerm_zero
      · exact ih hds z htail

/-! ### The composition: a vanishing substituted coefficient has a vanishing `log`-part

Every piece is now a theorem, so this is the assembly and nothing else. Given

  * `log ∘ S` not a rational germ  (`not_ratGerm_log_of_pole`),
  * the coefficient's split into `A + B·log (S x)`  (`substituted_coeff_splits`),
  * `A` and `B` rational  (the closure lemmas), and
  * the coefficient vanishing on a ray  — which is what the descent's minimality supplies,

the `log`-part `B = −s·(gyd cs)[j]` is eventually zero.

**Where the vanishing comes from is not this theorem's business**, and that is deliberate: it is a
hypothesis, because in route A it arrives from the proportionality the minimal-relation argument
forces, not from the relation itself. Folding it in would have made this look like more than it is. -/

/-- **The assembly.** A substituted coefficient that vanishes on a ray has `EvZeroF` `log`-part. -/
theorem substituted_coeff_log_part_evZero
    {S s : Real → Real} {es cs : List (Real → Real)}
    {j : Nat} {p q r w : Real → Real} {X : Real}
    (hnr : ¬ RatGerm (fun x => log (S x))) (hX : 1 ≤ X)
    (hp : es[j]? = some p)
    (hq : (gscale s ((fun _ => (0 : Real)) :: gyd cs))[j]? = some q)
    (hr : (gyd cs)[j]? = some r)
    (hRp : RatGerm p) (hRq : RatGerm q) (hRr : RatGerm r)
    (hRs : RatGerm s) (hRinv : RatGerm (fun x => 1 / S x))
    (hw : (gadd es (gadd (gscale s ((fun _ => (0 : Real)) :: gyd cs))
                         (gscale (fbasisSubMul S s) (gyd cs))))[j]? = some w)
    (hzero : ∀ x : Real, X ≤ x → w x = 0) :
    EvZeroF (fun x => (0 - s x) * r x) := by
  obtain ⟨w', hw', hsplit⟩ := substituted_coeff_splits hp hq hr
  have hww : w = w' := by rw [hw] at hw'; exact Option.some_inj.mp hw'
  refine log_separation (A := fun x => p x + q x + s x * (1 / S x) * r x)
    (B := fun x => (0 - s x) * r x) hnr
    (ratGerm_add (ratGerm_add hRp hRq) (ratGerm_mul (ratGerm_mul hRs hRinv) hRr))
    (ratGerm_mul (ratGerm_neg hRs) hRr) hX (fun x hx => ?_)
  show (p x + q x + s x * (1 / S x) * r x) + ((0 - s x) * r x) * log (S x) = 0
  rw [← hsplit x, ← hww]
  exact hzero x hx

/-- **`RatGerm` is closed under difference.** Same construction as `ratGerm_add` with `psub`. -/
theorem ratGerm_sub {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x - g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨psub (pmul Pa Qb) (pmul Pb Qa), pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x - g x = _
    rw [pev_psub, pev_pmul, pev_pmul, pev_pmul,
        hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    refine (div_of_eq_mul (mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))) ?_).symm
    rw [show (pev Qa x * pev Qb x)
           * (pev Pa x / pev Qa x - pev Pb x / pev Qb x)
         = pev Qb x * (pev Qa x * (pev Pa x / pev Qa x))
           - pev Qa x * (pev Qb x * (pev Pb x / pev Qb x)) from by mach_ring,
        mul_div_cancel_left (hQa x (le_trans hYa hx)),
        mul_div_cancel_left (hQb x (le_trans hYb hx))]
    mach_ring

/-! ### The shape minimality actually supplies: the CROSS-DIFFERENCE

`substituted_coeff_log_part_evZero` takes "the coefficient vanishes" as its hypothesis. Checking
what the descent delivers shows that is **not** the shape available: `GermDerivEntry`'s descent
builds `gscaleSub cd dtop cs₀ ds₀`, whose entries are `cd·d − dtop·c`, and *"minimality kills every
remaining coefficient"* of THAT. So the vanishing on offer is of a cross-difference, not of a
substituted coefficient on its own.

The separation survives it, because the cross-difference is still linear in `log`:

    cd·(A + B·log S) − dtop·c  =  (cd·A − dtop·c)  +  (cd·B)·log S

so the `log`-part is `cd·B` and the rest stays free of `log`. This is the version a caller can
actually reach for; the earlier one is kept because it is the simpler statement and the algebra is
shared, but **prefer this one when wiring the descent**. -/
theorem crossDiff_log_part_evZero
    {S s cd dtop c : Real → Real} {es cs : List (Real → Real)}
    {j : Nat} {p q r w : Real → Real} {X : Real}
    (hnr : ¬ RatGerm (fun x => log (S x))) (hX : 1 ≤ X)
    (hp : es[j]? = some p)
    (hq : (gscale s ((fun _ => (0 : Real)) :: gyd cs))[j]? = some q)
    (hr : (gyd cs)[j]? = some r)
    (hRp : RatGerm p) (hRq : RatGerm q) (hRr : RatGerm r)
    (hRs : RatGerm s) (hRinv : RatGerm (fun x => 1 / S x))
    (hRcd : RatGerm cd) (hRdtop : RatGerm dtop) (hRc : RatGerm c)
    (hw : (gadd es (gadd (gscale s ((fun _ => (0 : Real)) :: gyd cs))
                         (gscale (fbasisSubMul S s) (gyd cs))))[j]? = some w)
    (hzero : ∀ x : Real, X ≤ x → cd x * w x - dtop x * c x = 0) :
    EvZeroF (fun x => cd x * ((0 - s x) * r x)) := by
  obtain ⟨w', hw', hsplit⟩ := substituted_coeff_splits hp hq hr
  have hww : w = w' := by rw [hw] at hw'; exact Option.some_inj.mp hw'
  refine log_separation
    (A := fun x => cd x * (p x + q x + s x * (1 / S x) * r x) - dtop x * c x)
    (B := fun x => cd x * ((0 - s x) * r x)) hnr
    (ratGerm_sub (ratGerm_mul hRcd
        (ratGerm_add (ratGerm_add hRp hRq) (ratGerm_mul (ratGerm_mul hRs hRinv) hRr)))
      (ratGerm_mul hRdtop hRc))
    (ratGerm_mul hRcd (ratGerm_mul (ratGerm_neg hRs) hRr)) hX (fun x hx => ?_)
  have hz := hzero x hx
  rw [hww, hsplit x] at hz
  show (cd x * (p x + q x + s x * (1 / S x) * r x) - dtop x * c x)
      + (cd x * ((0 - s x) * r x)) * log (S x) = 0
  -- NOT `rw [← hz]`: the goal contains `0 - s x`, and a backward rewrite of `_ = 0` fires on THAT
  -- zero. Third instance of this in one session; the corpus writes negation as `0 - ·` throughout,
  -- so backward rewrites against `= 0` are systematically hazardous here. Go forward instead.
  rw [show (cd x * (p x + q x + s x * (1 / S x) * r x) - dtop x * c x)
         + (cd x * ((0 - s x) * r x)) * log (S x)
       = cd x * ((p x + q x + s x * (1 / S x) * r x)
                 + ((0 - s x) * r x) * log (S x)) - dtop x * c x from by mach_ring]
  exact hz

/-! ### Minimality kills every cross-difference coefficient — extracted

The vanishing that `crossDiff_log_part_evZero` consumes is available, but only INSIDE
`minimal_grel_identity`'s proof: `gcancel_top` then `all_gcoeffs_evZero_of_shorter'`, three lines
that are not exposed as a theorem. Extracted here, because it is what lets the descent be run on a
relation OTHER than `gdrel`.

**And it must be run on another one.** `gdrel v cs es = gadd es (gscale v (gyd cs))` — its
coefficients carry `v = (exp (S x) + 1/S x)·s x`, so they carry `exp`, and `top_two_multiplier_splits`
already showed that shape is not separable. The SUBSTITUTED list
(`fbasis_relation_substituted`) is a different list with the same `gbipev` at `Fbasis ∘ S`, and its
coefficients carry `log` instead — which is the whole point of the substitution.

Both machinery pieces are generic in the relation, so nothing stops the descent running on the
substituted list, and that is how the two threads meet. -/

/-- **Minimality kills every cross-difference coefficient.** For a minimal relation `cs₀ ++ [cd]`
and any relation `ds₀ ++ [dtop]` of the same length, every entry of `gscaleSub cd dtop cs₀ ds₀` is
eventually zero — the top cancels, and what is left is shorter than minimal. -/
theorem minimal_crossDiff_evZero {u : Real → Real} {cs₀ ds₀ : List (Real → Real)}
    {cd dtop : Real → Real}
    (hlen : cs₀.length = ds₀.length)
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → (cs₀ ++ [cd]).length ≤ ns.length)
    (hc : GEvRel u (cs₀ ++ [cd])) (hd : GEvRel u (ds₀ ++ [dtop])) :
    ∀ c : Real → Real, c ∈ gscaleSub cd dtop cs₀ ds₀ → EvZeroF c := by
  refine all_gcoeffs_evZero_of_shorter' hmin (gcancel_top hlen hc hd) ?_
  have h1 : (gscaleSub cd dtop cs₀ ds₀).length = cs₀.length :=
    gscaleSub_length cd dtop cs₀ ds₀ hlen
  have h2 : (cs₀ ++ [cd]).length = cs₀.length + 1 := by simp
  rw [h1, h2]
  omega

/-! ### Germ congruence, and the abstract-`S` form the route needs

`not_ratGerm_log_of_pole` concludes about `fun x => log (pev P x / pev Q x)` LITERALLY, while route
A carries an abstract `S` that merely agrees with `P/Q` on a ray. `RatGerm` is a germ property, so
the transfer is sound — but it was being done INLINE (`EMLLogNotRational`'s
`fun x hx => by rw [← h x]; exact hg x hx`), and this would have been the second copy. The corpus's
own rule is to generalise at the second instance, so here it is as a lemma. -/

/-- **`RatGerm` only sees the germ.** Two functions agreeing on a ray are rational together. -/
theorem ratGerm_congr {f g : Real → Real} {X : Real} (hX : 1 ≤ X)
    (h : ∀ x : Real, X ≤ x → f x = g x) (hg : RatGerm g) : RatGerm f := by
  obtain ⟨P, Q, Xg, hXg, hQ, hge⟩ := hg
  obtain ⟨Y, hY, hYX, hYg⟩ := two_bounds' hX hXg
  exact ⟨P, Q, Y, hY, fun x hx => hQ x (le_trans hYg hx),
    fun x hx => by rw [h x (le_trans hYX hx)]; exact hge x (le_trans hYg hx)⟩

/-- **`¬ RatGerm (log ∘ S)` for an abstract `S`** that agrees with `P/Q` on a ray. This is the form
route A can actually cite: it carries `S` as a germ, not as a pair of polynomials. -/
theorem not_ratGerm_log_comp_of_pole {q P Q Qt : List Real} {S : Real → Real}
    {X : Real} {r : Nat}
    (hq : PIrred q) (hchar : ∀ rr : Nat, DerivCoprime q (rr + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hX : 1 ≤ X)
    (hPpos : ∀ x : Real, X ≤ x → 0 < pev P x)
    (hQpos : ∀ x : Real, X ≤ x → 0 < pev Q x)
    (hSdef : ∀ x : Real, X ≤ x → S x = pev P x / pev Q x) :
    ¬ RatGerm (fun x => log (S x)) := by
  intro hrat
  exact not_ratGerm_log_of_pole hq hchar hPd hPn hQ hQtd hX hPpos hQpos
    (ratGerm_congr hX (fun x hx => by rw [hSdef x hx]) hrat)

end MachLib
