import MachLib.MPolyRing
import MachLib.Forge
import MachLib.Sign
import MachLib.Linarith
import MachLib.EML

/-! # The key algebraic tool for `growthCompetitionWitness`'s non-monotonicity

`WitnessResidualGrowthCompetitionWitness.lean` left non-monotonicity explicitly open, flagging
two possible routes: a derivative-based sign-crossing argument, or careful numerical interval
bounds. This file completes the FIRST piece of the derivative route, worked out on paper (and
numerically cross-checked against a finite-difference ground truth, catching a genuine
hand-derivation error along the way — see the module-level notes below) before touching Lean.

**The derivation, in outline.** Write `T(x) := exp(A(x)) - B(x)` with `A := boundedNonConstantWitness
c1`, `B := boundedNonConstantWitness c2`. Using `A`'s own known derivative and eval formulas,
`T'(x) = exp(x) · S(E)` where `E := exp(exp x)` and

  `S(E) = log(c2)/(E - log c2) - E·log(c1)/(E - log c1)²`.

(`exp(x) > 0` always, so `T'`'s sign matches `S(E)`'s.) Clearing the positive denominator
`(E-log c2)·(E-log c1)²` (valid for `E > max(log c1, log c2)`, guaranteed by both trees' own
well-definedness), `S(E) < 0` iff a QUADRATIC in `E` is negative:

  `(q-p)·E² - pq·E + p²q < 0`, where `p := log c1`, `q := log c2`.

**Why this matters**: this quadratic is the SAME algebraic object regardless of which specific
`c1, c2` are chosen — it turns a transcendental sign-comparison problem (which would otherwise
need numerical bounds on `log(2.2)`, `log(2.7)`, etc.) into a PURE ALGEBRA problem, avoidable
without building any new numeric-bound infrastructure at all.

**The tool built here**: `quadratic_neg_between` — an upward-opening quadratic (`k > 0`)
negative at two points `a < b` is negative throughout `[a,b]`. Proof: the exact identity
`(b-a)·quad(E) = (b-E)·quad(a) + (E-a)·quad(b) - k·(b-a)·(E-a)·(b-E)` (verified via `mach_mpoly`,
with one `mach_mpoly`-specific gotcha — see below) makes every term on the right `≤ 0` (and at
least one strictly, since `(b-E)` and `(E-a)` can't both vanish), giving the whole product `< 0`,
hence (dividing by the positive `b-a`) `quad(E) < 0`.

**Two build gotchas, both new.** (1) `mach_mpoly` — usually the "complete normaliser" for this
kind of multi-atom polynomial identity — left a residual `-0 = 0` sub-goal on THIS specific
4-variable, degree-3-product identity, closed by tactic `mach_mpoly [...]; rw [neg_zero]`
immediately after; every SMALLER piece of the same identity (tested separately) closed via
`mach_mpoly` alone, so this is a genuine (if narrow) limitation, not a modeling error — confirmed
by an independent numeric check (5 random substitutions) BEFORE debugging the Lean side, which is
what revealed the gap was in the tactic, not the identity. (2) `by_contra` is not a recognized
tactic in this codebase (no Mathlib) — the established `refine Classical.byContradiction (fun hcon
=> ?_)` pattern is required instead; this cost one debugging cycle. -/

namespace MachLib
namespace Real

theorem mul_nonpos_of_nonneg_of_nonpos {a b : Real} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  rcases lt_total (a * b) 0 with h | h | h
  · exact le_of_lt h
  · exact le_of_eq h
  · exfalso
    have hnb : 0 ≤ -b := neg_nonneg_of_nonpos hb
    have hprod : 0 ≤ a * (-b) := mul_nonneg ha hnb
    have heq : a * (-b) = -(a * b) := mul_neg a b
    rw [heq] at hprod
    have hcontra := add_le_add_left hprod (a * b)
    have e1 : a * b + 0 = a * b := add_zero _
    have e2 : a * b + -(a * b) = 0 := add_neg _
    rw [e1, e2] at hcontra
    exact lt_irrefl_ax _ (lt_of_le_of_lt hcontra h)

theorem mul_neg_of_pos_of_neg_local {a b : Real} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  rcases lt_total (a * b) 0 with h | h | h
  · exact h
  · exfalso
    have hnb : 0 < -b := neg_pos_of_neg hb
    have hprod : 0 < a * (-b) := mul_pos ha hnb
    have heq : a * (-b) = -(a * b) := mul_neg a b
    rw [heq, h] at hprod
    rw [neg_zero] at hprod
    exact lt_irrefl_ax _ hprod
  · exfalso
    have hnb : 0 < -b := neg_pos_of_neg hb
    have hprod : 0 < a * (-b) := mul_pos ha hnb
    have heq : a * (-b) = -(a * b) := mul_neg a b
    rw [heq] at hprod
    have hcontra := add_lt_add_left hprod (a * b)
    have e1 : a * b + 0 = a * b := add_zero _
    have e2 : a * b + -(a * b) = 0 := add_neg _
    rw [e1, e2] at hcontra
    exact lt_irrefl_ax _ (lt_trans_ax h hcontra)

theorem sub_le_self_of_nonneg {X T : Real} (hT : 0 ≤ T) : X - T ≤ X := by
  have hnT : -T ≤ -(0 : Real) := neg_le_neg hT
  rw [neg_zero] at hnT
  have h := add_le_add_left hnT X
  have e1 : X + -T = X - T := by mach_mpoly [X, T]
  have e2 : X + 0 = X := add_zero _
  rwa [e1, e2] at h

/-- **Convexity fact for a quadratic**: an upward-opening quadratic negative at two points
`a<b` is negative throughout `[a,b]`. Via the exact identity `(b-a)*quad(E) = (b-E)*quad(a) +
(E-a)*quad(b) - k*(b-a)*(E-a)*(b-E)`, all three RHS terms `≤0` and at least one strictly (since
`(b-E)` and `(E-a)` can't both vanish, as their sum is the fixed positive `b-a`). No calculus,
no roots, no discriminant — pure algebra. -/
theorem quadratic_neg_between {k m n a b E : Real} (hk : 0 < k) (hab : a < b)
    (hEa : a ≤ E) (hEb : E ≤ b)
    (hqa : k * a * a + m * a + n < 0) (hqb : k * b * b + m * b + n < 0) :
    k * E * E + m * E + n < 0 := by
  have hba : 0 < b - a := sub_pos_of_lt hab
  have hbE : 0 ≤ b - E := sub_nonneg_of_le hEb
  have hEa' : 0 ≤ E - a := sub_nonneg_of_le hEa
  have hident : (b - a) * (k * E * E + m * E + n)
      = (b - E) * (k * a * a + m * a + n) + (E - a) * (k * b * b + m * b + n)
        - k * (b - a) * (E - a) * (b - E) := by
    mach_mpoly [k, m, n, a, b, E]
    rw [neg_zero]
  have hterm3 : 0 ≤ k * (b - a) * (E - a) * (b - E) := by
    apply mul_nonneg
    apply mul_nonneg
    exact mul_nonneg (le_of_lt hk) (le_of_lt hba)
    exact hEa'
    exact hbE
  have hsum_neg : (b - E) * (k * a * a + m * a + n) + (E - a) * (k * b * b + m * b + n) < 0 := by
    rcases (le_iff_lt_or_eq 0 (b - E)).mp hbE with hstrict | heq0
    · have hterm1 : (b - E) * (k * a * a + m * a + n) < 0 :=
        mul_neg_of_pos_of_neg_local hstrict hqa
      have hterm2 : (E - a) * (k * b * b + m * b + n) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hEa' (le_of_lt hqb)
      have h := add_le_add_left hterm2 ((b - E) * (k * a * a + m * a + n))
      have e2 : (b - E) * (k * a * a + m * a + n) + 0 = (b - E) * (k * a * a + m * a + n) :=
        add_zero _
      rw [e2] at h
      exact lt_of_le_of_lt h hterm1
    · have hEeqb : E = b := by
        have h1 : b - E = 0 := heq0.symm
        have h3 : b - E + E = 0 + E := by rw [h1]
        have e3 : b - E + E = b := by mach_mpoly [b, E]
        have e4 : (0 : Real) + E = E := zero_add _
        rw [e3, e4] at h3
        exact h3.symm
      have hEab' : 0 < E - a := by rw [hEeqb]; exact hba
      have hterm2 : (E - a) * (k * b * b + m * b + n) < 0 :=
        mul_neg_of_pos_of_neg_local hEab' hqb
      have hterm1 : (b - E) * (k * a * a + m * a + n) ≤ 0 := by
        rw [← heq0]
        exact le_of_eq (zero_mul _)
      have h := add_le_add_left hterm1 ((E - a) * (k * b * b + m * b + n))
      have e5 : (E - a) * (k * b * b + m * b + n) + 0 = (E - a) * (k * b * b + m * b + n) :=
        add_zero _
      rw [e5] at h
      have h2 := lt_of_le_of_lt h hterm2
      have e6 : (E - a) * (k * b * b + m * b + n) + (b - E) * (k * a * a + m * a + n)
          = (b - E) * (k * a * a + m * a + n) + (E - a) * (k * b * b + m * b + n) := add_comm _ _
      rwa [e6] at h2
  have hfinal_num : (b - a) * (k * E * E + m * E + n) < 0 := by
    rw [hident]
    exact lt_of_le_of_lt (sub_le_self_of_nonneg hterm3) hsum_neg
  refine Classical.byContradiction (fun hcon => ?_)
  have hqE_nonneg : 0 ≤ k * E * E + m * E + n := by
    rcases lt_total (k * E * E + m * E + n) 0 with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hprod_nonneg : 0 ≤ (b - a) * (k * E * E + m * E + n) :=
    mul_nonneg (le_of_lt hba) hqE_nonneg
  exact lt_irrefl_ax _ (lt_of_le_of_lt hprod_nonneg hfinal_num)

end Real
end MachLib
