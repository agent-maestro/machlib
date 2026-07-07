import MachLib.Decimal
import MachLib.Linarith
import MachLib.SelfMapConjugacy
import MachLib.Trig

/-!
# `mach_sign` — automated sign/positivity for Forge `> 0` obligations

The largest blocked-`@verify` subclass is `f(vars) > 0` (≈178 of the `Discovered/` sorries): a
product / sum / `exp` of manifestly-positive subterms (positive inputs by hypothesis, `exp` always
positive, positive constants). `mach_positivity` already closes squares / decimals / fog bands but has
no `mul_pos` / `add_pos` / `exp_pos` recursion, and the goals carry the decimal zero `0.0`
(`realOfScientific 0 true 1`) rather than `0`, so a `mul_pos`-produced `0 < _` doesn't match `_ > 0.0`.

`mach_sign` bridges both: normalise the decimal zero to `0` (only the zeros, so `mach_positivity`'s
`OfScientific` arms still fire on nonzero literals), then recurse through `mul_pos` / `add_pos` /
`div_pos` / `exp_pos` / `exp10_pos` (and their `≤` mirrors), delegating leaves to `mach_positivity`.
Every leaf is a real positivity fact — it cannot manufacture a false sign (`x > 0`, `x·x > 0`,
`a − b > 0` are all correctly *refused*).

**Measured (2026-06-30), per-obligation** (the rigorous metric: swap each `sorry` for
`(first | mach_sign | sorry)` so the file always compiles, then `#print axioms` per theorem — a
theorem with no `sorryAx` is a *real* close): of the `Discovered/` positivity/ordering obligations,
the tactics close **126 / 165 (76%)**. (A per-FILE check reads ≈60%, but that under-counts — a
multi-obligation file stays red if any one obligation fails.) Coverage spans: positivity
(`mul_pos`/`add_pos`/`div_pos`/`exp_pos`/`sqrt_pos`), the sigmoid-GELU/zero-floor/`1−p`/`realPow` arms,
the **transcendental-bound** arms (`log_nonneg`, `one_lt_exp`, `tanh_mul_add_self_nonneg` — all derived
from existing axioms, no new ones), the **ordering layer** (`mach_le` + `min_nonneg` + recursive
additive + `sub_nonneg_of_le` for structural `a − b ≥ 0`), and — using the emitted refinement
hypotheses — **bound transitivity** (`0 ≤ x`/`0 < x` from `c ≤ x` + `0 ≤ c`) and **square
monotonicity** (`|a| ≤ |b| ⇒ a² ≤ b²`).

Honest ceiling — the structural close-rate saturates near **~76%**. The Phase-1 arm batch lifted it
+10 (70→76), *below* the optimistic "~90%" shape-count estimate: real obligations stack blockers
beyond their headline shape (a positive constant behind a `def`, a `√`/product inside an `exp` arg, a
multi-step hypothesis chain), so a shape that "should" close often has one more gate. The remaining
~24% split into (a) **domain** inequalities — `a − b ≥ 0` where `b ≤ a` is Black-Scholes-price /
energy-balance specific, not structural — and (b) compounding-blocker cases needing a per-kernel push.
Neither is closed by "one more arm"; see `docs/verify_closerate_scope.md`.
-/

namespace MachLib.Real

/-- `exp10 x > 0` (base-10 exponential is always positive) — `exp10 x = exp(x·log 10) > 0`. -/
theorem exp10_pos (x : Real) : 0 < exp10 x := by rw [exp10_def]; exact exp_pos _

/-- `|x|·|x| = x·x` — bridges a square to its absolute value (`x·x ≥ 0`). -/
theorem abs_mul_self (x : Real) : abs x * abs x = x * x := by
  rw [← abs_mul, abs_of_nonneg (mul_self_nonneg x)]

/-- **Square monotonicity: `|a| ≤ |b| ⇒ a·a ≤ b·b`.** The `v1² ≤ v0²`-from-`|v1| ≤ |v0|` step in
energy/quadratic kernels (defibrillator). Built from the monotone-multiply lemmas, no new axiom. -/
theorem mul_self_le_mul_self_of_abs_le {a b : Real} (h : abs a ≤ abs b) : a * a ≤ b * b := by
  rw [← abs_mul_self a, ← abs_mul_self b]
  exact le_trans (mul_le_mul_of_nonneg_right h (abs_nonneg a))
                 (mul_le_mul_of_nonneg_left h (abs_nonneg b))

/-- `0 < 1 + tanh x` — the sigmoid/GELU positivity (`HALF·(1 + tanh …)` shape). From `−1 < tanh x`. -/
theorem one_add_tanh_pos (x : Real) : 0 < 1 + tanh x := by
  have h := sub_pos_of_lt (neg_one_lt_tanh x)
  have e : tanh x - (-1) = 1 + tanh x := by mach_ring
  rwa [e] at h

/-- `0 ≤ tanh y · c + c` for `0 ≤ c` (= `c·(1+tanh y)`) — the un-factored sigmoid (`sigmoid_alt`). -/
theorem tanh_mul_add_self_nonneg (y c : Real) (hc : 0 ≤ c) : 0 ≤ tanh y * c + c := by
  have e : tanh y * c + c = c * (1 + tanh y) := by mach_ring
  rw [e]; exact mul_nonneg hc (le_of_lt (one_add_tanh_pos y))

/-- `1 < exp x` for `0 < x` (from `exp_lt` + `exp_zero`). The `exp(positive) > 1` shape (`up_factor`). -/
theorem one_lt_exp {x : Real} (h : 0 < x) : 1 < exp x := by
  have := exp_lt h; rwa [exp_zero] at this

/-- `1 ≤ exp x` for `0 ≤ x`. -/
theorem one_le_exp {x : Real} (h : 0 ≤ x) : 1 ≤ exp x := by
  have := exp_monotone h; rwa [exp_zero] at this

/-- `log` is monotone (`≤`) on the positives — from the strict `log_lt_log` axiom. -/
theorem log_le_log {x y : Real} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y := by
  rcases (le_iff_lt_or_eq x y).mp hxy with h | h
  · exact le_of_lt (log_lt_log hx h)
  · subst h; exact le_refl _

/-- `0 ≤ log x` for `1 ≤ x` (from `log_le_log` + `log_one`). The `log(1+snr) ≥ 0` shape (`shannon`). -/
theorem log_nonneg {x : Real} (h : 1 ≤ x) : 0 ≤ log x := by
  have := log_le_log zero_lt_one_ax h; rwa [log_one] at this

/-- The decimal zero `0.0…0` *is* `0` — cleared via `realOfScientific_clears` (`0·10ᵉ = 0`). -/
theorem rOS_zero (e : Nat) : realOfScientific 0 true e = 0 := by
  have hc : natCast (10 ^ e) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos e (by decide)))
  refine mul_right_cancel' hc ?_
  rw [realOfScientific_clears 0 e, natCast_zero, zero_mul]

/-- Simp form: rewrite only zero-mantissa literals (`0.0`) to `0`, leaving nonzero decimals as
`OfScientific` so `mach_positivity`'s decimal arms keep matching. -/
@[simp] theorem ofSci_zero (e : Nat) : (OfScientific.ofScientific 0 true e : Real) = 0 := rOS_zero e

/-- The ordering companion: prove `b ≤ a` goals by monotonicity (`exp_monotone`, `neg_le_neg`,
`add_le_add_left`, `mul_le_mul_of_nonneg_left`) and the `min`/`max` bounds, delegating `0 ≤ _`
side-conditions to `mach_sign_core`. Mutually recursive with it. This is what lets `sub_nonneg_of_le`
turn an `a − b ≥ 0` goal into a tractable `b ≤ a` — e.g. an exp-difference `exp(−h₀) − exp(−h₁) ≥ 0`
from `h₀ ≤ h₁`. -/
syntax "mach_le" : tactic

/-- Recursive positivity core: `exp_pos`, `mul_pos`, `add_pos`, `min_nonneg`, the tanh/max/pow arms,
and `sub_nonneg_of_le` (→ `mach_le`), delegating leaves to the existing `mach_positivity`. -/
syntax "mach_sign_core" : tactic
macro_rules
  | `(tactic| mach_sign_core) => `(tactic|
      first
      | assumption
      | exact exp_pos _
      | exact exp_nonneg _
      | exact exp10_pos _
      | exact one_add_tanh_pos _
      | exact le_of_lt (one_add_tanh_pos _)
      | exact le_max_right _ _
      | exact le_max_left _ _
      | exact sqrt_nonneg _
      | (apply sqrt_pos <;> mach_sign_core)
      | (apply one_lt_exp <;> mach_sign_core)
      | (apply one_le_exp <;> mach_sign_core)
      | (apply log_nonneg <;> mach_le)
      | (apply tanh_mul_add_self_nonneg <;> mach_sign_core)
      | mach_positivity
      | (apply mul_pos <;> mach_sign_core)
      | (apply add_pos <;> mach_sign_core)
      | (apply div_pos_of_pos_pos <;> mach_sign_core)
      | (apply sub_pos_of_lt <;> mach_sign_core)
      | (apply mul_nonneg <;> mach_sign_core)
      | (apply add_nonneg <;> mach_sign_core)
      | (apply div_nonneg <;> mach_sign_core)
      | (apply realPow_nonneg <;> mach_sign_core)
      | (apply min_nonneg <;> mach_sign_core)
      -- bound transitivity: `0 ≤ x` from a refinement hyp `c ≤ x` (e.g. `capacitance ≥ C_MIN`)
      -- + `0 ≤ c`. The `by assumption` resolves the hyp (instantiating the midpoint) first.
      | (refine le_trans ?_ (by assumption) <;> mach_sign_core)
      | (refine lt_of_lt_of_le ?_ (by assumption) <;> mach_sign_core)
      -- strict-hyp bound transitivity: `0 ≤ x` / `0 < x` from a STRICT hyp `c < x`
      -- + `0 ≤ c` (e.g. a deadzone / threshold guard `x > 1` after an `if`-split).
      | (refine le_of_lt (lt_of_le_of_lt ?_ (by assumption)) <;> mach_sign_core)
      | (refine lt_of_le_of_lt ?_ (by assumption) <;> mach_sign_core)
      | (apply sub_nonneg_of_le <;> mach_le))

macro_rules
  | `(tactic| mach_le) => `(tactic|
      first
      | assumption
      | exact le_refl _
      | exact le_max_right _ _
      | exact le_max_left _ _
      | exact min_le_right _ _
      | exact min_le_left _ _
      | (apply exp_monotone <;> mach_le)
      | (apply neg_le_neg <;> mach_le)
      | (apply add_le_add_left <;> mach_le)
      | (apply mul_self_le_mul_self_of_abs_le <;> mach_le)
      -- additive ordering, recursive: `x ≤ y + z` via `x ≤ y` (recurse) + `0 ≤ z`
      -- (closes nested `a ≤ (a+b)+c`, e.g. carbon `total ≥ scope1`).
      | (refine le_trans ?_ (le_add_of_nonneg_right ?_) <;> (first | mach_le | mach_sign_core))
      | (apply mul_le_mul_of_nonneg_left <;> (first | mach_le | mach_sign_core)))

/-- **`mach_sign`** — close a Forge `f(vars) > 0` / `0 < f(vars)` obligation. Normalise the decimal
zero, then run the positivity recursion. -/
macro "mach_sign" : tactic => `(tactic|
  ((try simp only [ofSci_zero] at *) <;> mach_sign_core))

/-- `¬ a ≤ b → b ≤ a` on `Real` (totality of the order, from `lt_total`).
The negated-guard branch of an `if a ≤ b … else …` @verify obligation
lands here: e.g. `max(a,b) ≥ a` in the else arm needs `a ≤ b` from
`¬ (b ≤ a)`. Placed in the emit-imported SignTactic (0 dependents) so the
Lean backend's branch closers can cite it without a heavier import. -/
theorem le_of_not_le {a b : Real} (h : ¬ a ≤ b) : b ≤ a := by
  rcases lt_total a b with hlt | heq | hgt
  · exact absurd (le_of_lt hlt) h
  · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inr heq)) h
  · exact le_of_lt hgt

/-- **Convex-combination interval preservation (upper).** A blend
`α·a + (1-α)·b` of two values each `≤ M`, with `α ∈ [0,1]`, is itself `≤ M`.
The generalisation of `interval_add_scale` (Forge.lean) off the unit interval:
the inputs live in an ARBITRARY range `[·, M]`, not `[0,1]`. This is the
anti-drift guarantee a complementary filter / EMA / weighted average earns —
the fused estimate never escapes the interval its inputs occupy — and it is
exactly the goal a positivity closer (`mach_sign`) cannot reach, since it is a
convexity bound, not a sign fact. Placed in the emit-imported SignTactic (0
dependents) so the Lean backend's closers can cite it, like `le_of_not_le`. -/
theorem convex_comb_le {α a b M : Real} (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (ha : a ≤ M) (hb : b ≤ M) : α * a + (1 - α) * b ≤ M := by
  have hα1 : 0 ≤ 1 - α := one_sub_nonneg_of_le_one h1
  have collapse : α * M + (1 - α) * M = M := by mach_ring
  exact le_trans (add_le_add_both (mul_le_mul_of_nonneg_left ha h0)
                                  (mul_le_mul_of_nonneg_left hb hα1))
                 (le_of_eq collapse)

/-- **Convex-combination interval preservation (lower).** Dual of
`convex_comb_le`: a blend of two values each `≥ lo`, with `α ∈ [0,1]`, is
`≥ lo`. Together they discharge `lo ≤ result ≤ hi` for a weighted blend. -/
theorem convex_comb_ge {α a b lo : Real} (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (ha : lo ≤ a) (hb : lo ≤ b) : lo ≤ α * a + (1 - α) * b := by
  have hα1 : 0 ≤ 1 - α := one_sub_nonneg_of_le_one h1
  have collapse : lo = α * lo + (1 - α) * lo := by mach_ring
  exact le_trans (le_of_eq collapse)
                 (add_le_add_both (mul_le_mul_of_nonneg_left ha h0)
                                  (mul_le_mul_of_nonneg_left hb hα1))

/-! ### Regression suite -/
namespace SignTests
example (p : Real) (h : p > (0.0 : Real)) : p * (exp p) > (0.0 : Real) := by mach_sign
example (a b : Real) (ha : a > (0.0 : Real)) (hb : b > (0.0 : Real)) : a * b > (0.0 : Real) := by mach_sign
example (x : Real) : (exp x) > (0.0 : Real) := by mach_sign
example (a b : Real) (ha : a > (0.0 : Real)) (hb : b > (0.0 : Real)) :
    a + (b * (exp a)) > (0.0 : Real) := by mach_sign
-- new arms: sigmoid/GELU, zero-floor max, 1−p denominators, real powers
example (x : Real) : (0.5 : Real) * (1 + tanh x) > (0 : Real) := by mach_sign
example (e : Real) : max e (0 : Real) ≥ (0 : Real) := by mach_sign
example (c e : Real) (hc : c > (0:Real)) : c * (max e (0:Real)) ≥ (0 : Real) := by mach_sign
example (p : Real) (h : p < (1:Real)) : (1 : Real) - p > (0 : Real) := by mach_sign
example (b y : Real) (hb : b ≥ (0:Real)) : b ^ y ≥ (0 : Real) := by mach_sign
-- ordering layer: saturating min/max ≥ 0, exp-difference monotonicity, ≤-recursion
example (e hi : Real) (h : (0:Real) ≤ hi) : (0:Real) ≤ min (max e 0) hi := by mach_sign
example (a b : Real) (h : a ≤ b) : (0:Real) ≤ exp (-a) - exp (-b) := by mach_sign
example (x y : Real) (h : x ≤ y) : exp x ≤ exp y := by mach_le
example (c x y : Real) (hc : (0:Real) ≤ c) (h : x ≤ y) : c * x ≤ c * y := by mach_le
-- using refinement hyps: bound transitivity + square monotonicity (the defibrillator chain)
example (x : Real) (h : (0.5:Real) ≤ x) : (0:Real) ≤ x := by mach_sign
example (a b : Real) (h : abs a ≤ abs b) : a * a ≤ b * b := by mach_le
example (c v0 v1 : Real) (hc : (0.5:Real) ≤ c) (hv : abs v1 ≤ abs v0) :
    c * (v0 * v0 - v1 * v1) ≥ (0:Real) := by mach_sign
-- Phase 1: transcendental bounds + additive/strict-bound ordering
example (B snr : Real) (hB : (0:Real) ≤ B) (hs : (0:Real) ≤ snr) :
    B * log ((1:Real) + snr) ≥ (0:Real) := by mach_sign      -- log positivity (shannon)
example (x : Real) (h : (0:Real) < x) : exp x > (1:Real) := by mach_sign  -- exp-vs-one (binomial)
example (y c : Real) (hc : (0:Real) ≤ c) : tanh y * c + c ≥ (0:Real) := by mach_sign  -- tanh-affine (sigmoid)
example (a b c : Real) (hb : (0:Real) ≤ b) (hc : (0:Real) ≤ c) : (a + b) + c ≥ a := by mach_le  -- additive (carbon)
example (t : Real) (h : t ≥ (0.5:Real)) : (0:Real) < t := by mach_sign     -- strict bound-transitivity
-- convex-combination interval preservation (complementary filter / EMA anti-drift):
-- a blend of two in-range values stays in range, for ANY α ∈ [0,1].
example (g a alpha lo M : Real) (h0 : (0:Real) ≤ alpha) (h1 : alpha ≤ (1:Real))
    (hg : g ≤ M) (ha : a ≤ M) : alpha * g + (1 - alpha) * a ≤ M := convex_comb_le h0 h1 hg ha
example (g a alpha lo M : Real) (h0 : (0:Real) ≤ alpha) (h1 : alpha ≤ (1:Real))
    (hg : lo ≤ g) (ha : lo ≤ a) : lo ≤ alpha * g + (1 - alpha) * a := convex_comb_ge h0 h1 hg ha
end SignTests

end MachLib.Real
