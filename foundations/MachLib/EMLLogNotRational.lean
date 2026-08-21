import MachLib.EMLBipevTrim

/-!
# `log ∉ C₀` — the growth question, moved into the algebraic frame

`FQueryLowerBound` fell to an envelope: `exp` outgrows every polynomial, a zero-query term is an
eventual rational germ, and rational germs are polynomially bounded. That instrument is
**structurally blind to `log`**. `log x ≤ x` sits inside a polynomial envelope, so no refinement of
the envelope argument can exclude it.

Two routes that look available are not.

**Direct germ comparison.** From `log x = P(x)/Q(x)`, `pev_dichotomy` gives `|P| ≥ c·xᵐ` and
`pev_envelope` gives `|Q| ≤ C·xᴹ`, hence `log x ≥ (c/C)·x^{m−M}`. That contradicts nothing unless
`m > M`, and closing that case needs `log x / x → 0`, which this corpus does not have.

**Inverting through `exp`.** From `log x = S(x)` one gets `exp (S x) = x`, and if a rational germ
tending to `+∞` were at least linear, `not_polyEnvelope_of_ge_exp_scaled` would finish. But
"unbounded rational germ ⟹ at least linear" is *exactly* the missing fact. Circular.

## The route that works

Substitute `x = exp t`. Because `log (exp t) = t` **unconditionally** — `log_exp`, no positivity
side condition — the germ identity becomes

```
t · Q(exp t) = P(exp t)        for all large t
```

that is, `Σⱼ (aⱼ − t·bⱼ) · (exp t)ʲ = 0`: a polynomial in `exp t` whose coefficients are polynomials
in `t`, of degree ≤ 1. **That is precisely the shape `exp_not_algebraic` forbids.** The growth
question has become an algebraic one, and the algebraic one is already a theorem.

Nothing analytic is added here. What the file contains is the substitution, the coefficient
bookkeeping (`logRel`), and the nontriviality argument. The germ's nonvanishing denominator is spent
**twice**, and only one of the two uses is obvious: once to clear `log x = P/Q` into
`t·Q(exp t) = P(exp t)`, and once to know the relation that produces is not the trivial one.
`logRel_zero_all_evZero` is the specimen showing the second use cannot be dropped.

## Why the coefficients are linear in `t`, and why that is the whole trick

The relation `Σⱼ (aⱼ − t·bⱼ)·yʲ` is linear in `t` at every index. So its `t`-difference at fixed `y`
is `−Q(y)`: **two values of `t` recover the denominator**. That is how `logRel_not_all_evZero` turns
"every coefficient dies" into "`Q ≡ 0`", contradicting the germ's nonvanishing denominator without
ever inspecting an individual coefficient of `P` or `Q`.

## The finding

`exp_not_algebraic` was proved to settle a *transcendence* question about `F`. It also settles a
*growth* question about `log`, once a substitution moves that question into the algebraic frame — so
it is a more general instrument than it looked. The next move for the `L_F` lower-bound programme is
probably not another envelope, but asking of each open growth question whether some substitution
puts it in reach of the algebraic theorem.
-/

namespace MachLib

open Real

/-! ## The relation family of a candidate `log` germ -/

/-- `P`, as coefficients constant in `t`. -/
noncomputable def constPairs : List Real → List (List Real)
  | []      => []
  | a :: as => [a] :: constPairs as

/-- `Q`, as coefficients linear in `t`: index `j` carries `−t·bⱼ`. -/
noncomputable def linPairs : List Real → List (List Real)
  | []      => []
  | b :: bs => [0, 0 - b] :: linPairs bs

private theorem constPairs_head_shuffle (a t y z : Real) : a + t * 0 + y * z = a + y * z := by
  mach_mpoly [a, t, y, z]

private theorem linPairs_nil_shuffle (t : Real) : (0 : Real) = 0 - t * 0 := by
  mach_mpoly [t]

private theorem linPairs_head_shuffle (b t y z : Real) :
    0 + t * (0 - b + t * 0) + y * (0 - t * z) = 0 - t * (b + y * z) := by
  mach_mpoly [b, t, y, z]

private theorem logRel_join_shuffle (a c : Real) : a + (0 - c) = a - c := by
  mach_mpoly [a, c]

theorem bipev_constPairs : ∀ (P : List Real) (t y : Real),
    bipev (constPairs P) t y = pev P y := by
  intro P
  induction P with
  | nil => intro _ _; rfl
  | cons a as ih =>
      intro t y
      show a + t * 0 + y * bipev (constPairs as) t y = a + y * pev as y
      rw [ih t y]
      exact constPairs_head_shuffle a t y (pev as y)

theorem bipev_linPairs : ∀ (Q : List Real) (t y : Real),
    bipev (linPairs Q) t y = 0 - t * pev Q y := by
  intro Q
  induction Q with
  | nil => intro t _; exact linPairs_nil_shuffle t
  | cons b bs ih =>
      intro t y
      show 0 + t * (0 - b + t * 0) + y * bipev (linPairs bs) t y = 0 - t * (b + y * pev bs y)
      rw [ih t y]
      exact linPairs_head_shuffle b t y (pev bs y)

/-- **The substituted relation, as a coefficient family.** Index `j` is `[aⱼ, −bⱼ]` — the
coefficient `aⱼ − t·bⱼ`, linear in `t`. -/
noncomputable def logRel (P Q : List Real) : List (List Real) :=
  bpadd (constPairs P) (linPairs Q)

theorem bipev_logRel (P Q : List Real) (t y : Real) :
    bipev (logRel P Q) t y = pev P y - t * pev Q y := by
  rw [logRel, bipev_bpadd, bipev_constPairs, bipev_linPairs]
  exact logRel_join_shuffle (pev P y) (t * pev Q y)

/-! ## Nontriviality: where the nonvanishing denominator is spent -/

private theorem denom_from_two_t (p q Z : Real) :
    q = p - Z * q - (p - (Z + 1) * q) := by
  mach_mpoly [p, q, Z]

private theorem sub_zero_zero : (0 : Real) - 0 = 0 := by mach_ring

/-- **The relation is nontrivial.** If every coefficient of `logRel P Q` were eventually zero, the
whole family would vanish — for every `y`, since coefficients are what vanish — and then `Q` itself
would be identically zero, which the germ's nonvanishing denominator forbids.

The `t`-difference is the entire argument: the coefficients are linear in `t`, so evaluating the
vanishing family at `t = Z` and `t = Z + 1` with the same `y` subtracts to `Q(y) = 0`. No individual
coefficient of `P` or `Q` is ever inspected. -/
theorem logRel_not_all_evZero {P Q : List Real} {X : Real} (hX : 1 ≤ X)
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0) :
    ¬ ∀ L : List Real, L ∈ logRel P Q → EvZeroF (pev L) := by
  intro hall
  obtain ⟨Z, hZ, hz⟩ := bipev_evZero_of_all_evZero (logRel P Q) hall
  have hzero : ∀ y : Real, pev Q y = 0 := by
    intro y
    have h1 : pev P y - Z * pev Q y = 0 := by
      rw [← bipev_logRel P Q Z y]; exact hz Z y (le_refl Z)
    have h2 : pev P y - (Z + 1) * pev Q y = 0 := by
      rw [← bipev_logRel P Q (Z + 1) y]
      exact hz (Z + 1) y (le_add_nonneg' (le_of_lt zero_lt_one_ax))
    rw [denom_from_two_t (pev P y) (pev Q y) Z, h1, h2]
    exact sub_zero_zero
  exact hQ X (le_refl X) (hzero X)

/-- **The nontriviality hypothesis is real, not defensive.** For `P = Q = [0]` the family
`logRel P Q` is `[[0 + 0, 0 − 0]]` — one coefficient, and it dies. So "the relation is nontrivial"
is not a property of the *shape* `logRel` produces; it has to come from somewhere, and the only
place it can come from is the germ's nonvanishing denominator.

Drop `hQ` from `logRel_not_all_evZero` and this is the counterexample. -/
theorem logRel_zero_all_evZero :
    ∀ L : List Real, L ∈ logRel [0] [0] → EvZeroF (pev L) := by
  intro L hL
  have hmem : L ∈ [[(0 : Real) + 0, 0 - 0]] := hL
  cases hmem with
  | head =>
      refine ⟨1, le_refl 1, fun x _ => ?_⟩
      show (0 : Real) + 0 + x * (0 - 0 + x * 0) = 0
      mach_ring
  | tail _ h => cases h

/-! ## The substitution, and the theorem -/

/-- `exp` carries every tail `t ≥ |log X| + 1` into the tail `x ≥ X`. The absolute value is there so
the threshold is `≥ 1` without needing `log X ≥ 0`. -/
theorem le_exp_of_le_abs_log {X t : Real} (hX : 1 ≤ X) (ht : abs (log X) + 1 ≤ t) : X ≤ exp t := by
  have hXpos : (0 : Real) < X := lt_of_lt_of_le zero_lt_one_ax hX
  have hlogX : log X ≤ t :=
    le_trans (le_trans (le_abs_self (log X)) (le_add_nonneg' (le_of_lt zero_lt_one_ax))) ht
  rcases lt_total (log X) t with h | h | h
  · have hlt := exp_lt h
    rw [exp_log hXpos] at hlt
    exact le_of_lt hlt
  · rw [← h, exp_log hXpos]; exact le_refl X
  · exact absurd (lt_of_lt_of_le h hlogX) (lt_irrefl_ax _)

/-- **`log` is not an eventual rational germ.**

The substitution `x = exp t` turns the germ identity into a polynomial relation in `exp t` with
coefficients polynomial in `t`, and `exp_not_algebraic_of_not_all_evZero` refuses it. Since
`C₀ = eventual rational germs` (`zero_query_iff_ratGerm`), this is `log ∉ C₀`. -/
theorem log_not_ratGerm : ¬ RatGerm log := by
  rintro ⟨P, Q, X, hX, hQ, he⟩
  refine exp_not_algebraic_of_not_all_evZero (logRel P Q)
    (logRel_not_all_evZero hX hQ) ⟨abs (log X) + 1, ?_, fun t ht => ?_⟩
  · have v := add_le_add_wit (abs_nonneg (log X)) (le_refl (1 : Real))
    rw [zero_add] at v; exact v
  · have hXe : X ≤ exp t := le_exp_of_le_abs_log hX ht
    have hQe : pev Q (exp t) ≠ 0 := hQ (exp t) hXe
    have hteq : t = pev P (exp t) / pev Q (exp t) := by
      have h := he (exp t) hXe
      rw [log_exp t] at h
      exact h
    have hmul : t * pev Q (exp t) = pev P (exp t) := by
      -- rewriting `t` forward would rewrite the `t` inside `exp t` too; go the other way
      have h0 := div_mul_self' (a := pev P (exp t)) hQe
      rw [← hteq] at h0
      exact h0
    rw [bipev_logRel, hmul]
    exact sub_self (pev P (exp t))

/-- **`log` is not zero-query — not even eventually.** The stronger form: no `F`-free term agrees
with `log` on any tail, let alone everywhere. -/
theorem log_not_zero_query : ¬ ∃ T : FTerm, fOcc T = 0 ∧
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → FTerm.eval T x = log x := by
  intro h
  exact log_not_ratGerm ((zero_query_iff_ratGerm log).mp h)

/-- **`LogQueryLowerBound`, discharged.** Computing `log` costs at least one `F`-query.

Companion to `fQueryLowerBound_holds`, and by a different instrument: that one is an envelope
argument, this one is the algebraic theorem reached through a substitution. Their axiom footprints
are nevertheless **identical** — 42 axioms each, set-equal, `#print axioms` on both — because the
two instruments are built from the same substrate and the substitution adds nothing but `log_exp`
and monotonicity of `exp`, which were already spent elsewhere.

`div_zero` is in that footprint and is load-bearing here for the same reason as there: without it
`x ↦ a x / 0` is an unconstrained function, a model could set `divR y 0 = log y`, and
`div var (sub var var)` would be a zero-query term computing `log`. The statement would then be
independent, not merely unproved. -/
theorem logQueryLowerBound_holds : LogQueryLowerBound := by
  intro T h
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exfalso
    obtain ⟨P, Q, X, hX, hQ, hg⟩ := ratGerm_of_zero_query T h0
    exact log_not_ratGerm ⟨P, Q, X, hX, hQ, fun x hx => by rw [← h x]; exact hg x hx⟩
  · exact hp

end MachLib
