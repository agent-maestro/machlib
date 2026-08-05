import MachLib.SinNotInEML
import MachLib.FieldLemmas
import MachLib.SignTactic
import MachLib.EMLAsymptoticClass

/-!
# `K/x` at depth 2: every reaching tree has `K > 1`

**The prior arm proved the floor for ONE family** — `no_exp_eq_log_of_le_one`, the impossibility
`exp a ≠ log K` for `K ≤ 1`. **This closes the depth-2 case for the family that an exhaustive
numerical search found to be the ONLY depth-2 shape reaching `K/x`**
(`monogate-research/exploration/inv_x_reachable_K_2026_08_04/RESULT.md`: 93 distinct `K` at depth 2,
every one from `((c ⊕ x) ⊕ c)`, none `≤ 1`).

**The route is "constrain the destination", not shape enumeration.** Two evaluations at distinct
positive points force the outer constant, and the outer constant forces `K` behind an `exp`.

**What the search contributed:** it did not prove anything. It told us *which shape to constrain* and
*what invariant to look for* — `K = exp(strictly positive)`. That is the search earning its keep as
a direction-finder rather than as evidence.
-/

namespace MachLib
namespace Real

/-- `x · exp(u − log x) = exp u` for `x > 0`. The division-free form of `exp(u − log x) = exp u / x`,
which is what lets the whole argument stay inside the corpus's algebraic idiom. -/
theorem mul_exp_sub_log {u x : Real} (hx : 0 < x) :
    x * exp (u - log x) = exp u := by
  -- DIVISION-FREE on purpose: `exp_sub` would introduce `/`, which `mach_mpoly` does not
  -- normalise and for which this corpus has no cancellation lemma. `exp_add` keeps the whole
  -- argument inside the algebraic idiom the tactics actually support.
  have h1 : exp (log x) * exp (u - log x) = exp u := by
    rw [← exp_add]
    have e : log x + (u - log x) = u := by mach_ring
    rw [e]
  rw [exp_log hx] at h1
  exact h1

/-- **The depth-2 reciprocal family, evaluated.** `eml (eml (const a) var) (const c)` sends `x` to
`exp(exp a)/x − log c`, here in the division-free form `x · eval = exp(exp a) − x · log c`. -/
theorem depth2_eval_scaled (a c x : Real) (hx : 0 < x) :
    x * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x
      = exp (exp a) - x * log c := by
  show x * (exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - log c) = _
  show x * (exp (exp a - log x) - log c) = _
  have h : x * (exp (exp a - log x) - log c)
      = x * exp (exp a - log x) - x * log c := by mach_mpoly [x, exp (exp a - log x), log c]
  rw [h, mul_exp_sub_log hx]

/-- **The outer constant is FORCED.** If the tree agrees with `K/x` at two distinct positive points,
`log c = 0` — there is no freedom in the second argument. -/
theorem depth2_forces_log_c_zero {a c K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₂ = K) :
    log c = 0 := by
  rw [depth2_eval_scaled a c x₁ h₁] at e₁
  rw [depth2_eval_scaled a c x₂ h₂] at e₂
  -- (exp(exp a) − x₁·L) = (exp(exp a) − x₂·L)  ⟹  (x₂ − x₁)·L = 0
  have h := e₁.trans e₂.symm
  have hsub : (x₂ - x₁) * log c = 0 := by
    have e : (x₂ - x₁) * log c
        = (exp (exp a) - x₁ * log c) - (exp (exp a) - x₂ * log c) := by
      mach_mpoly [x₁, x₂, log c, exp (exp a)]
    rw [e, h]; mach_mpoly [exp (exp a), x₂, log c]
  have hx : x₂ - x₁ ≠ 0 := by
    intro hz
    apply hne
    have e : x₁ = x₂ - (x₂ - x₁) := by mach_ring
    rw [e, hz]; mach_ring
  -- This corpus has `mul_ne_zero` but no `mul_eq_zero`, and no `by_contra` tactic. The
  -- contrapositive plus `Classical.byContradiction` does the same work with what exists.
  exact Classical.byContradiction (fun hL => (mul_ne_zero hx hL) hsub)

/-- **`K > 1`, for every depth-2 tree of this family reaching `K/x`.**

`K = exp(exp a)`, and `exp a > 0`, so `K > 1`. **The floor is not a bound that happens to hold — it
is `exp` being unable to reach `0`.** -/
theorem depth2_K_over_x_gt_one {a c K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₂ = K) :
    1 < K := by
  have hL : log c = 0 := depth2_forces_log_c_zero h₁ h₂ hne e₁ e₂
  rw [depth2_eval_scaled a c x₁ h₁, hL] at e₁
  have hK : K = exp (exp a) := by
    rw [← e₁]; mach_mpoly [x₁, exp (exp a)]
  rw [hK]
  exact one_lt_exp (exp_pos a)

/-! ## Unbounded depth: the left subtree need not be `const a`

The depth-2 proof used `eml (const a) var` on the left. **Nothing in it needed the `const`.**
What it needed was that the left subtree's inner value be the SAME at the two test points --
which `const a` supplies trivially and which any tree agreeing at two points supplies too.

**So the same argument closes an unbounded-depth family**, and the search that suggested the
depth-2 shape had nothing to do with reaching it: this came from reading the algebra after the
search was found blind above `K ≈ 1.4e11`.
-/

/-- `x · eval (eml (eml t var) (const c)) x = exp (exp (t.eval x)) − x · log c`, for **any** `t`. -/
theorem left_var_eval_scaled (t : EMLTree) (c x : Real) (hx : 0 < x) :
    x * (EMLTree.eml (EMLTree.eml t EMLTree.var) (EMLTree.const c)).eval x
      = exp (exp (t.eval x)) - x * log c := by
  show x * (exp ((EMLTree.eml t EMLTree.var).eval x) - log c) = _
  show x * (exp (exp (t.eval x) - log x) - log c) = _
  have h : x * (exp (exp (t.eval x) - log x) - log c)
      = x * exp (exp (t.eval x) - log x) - x * log c := by
    mach_mpoly [x, exp (exp (t.eval x) - log x), log c]
  rw [h, mul_exp_sub_log hx]

/-- **`K > 1` at UNBOUNDED DEPTH.**

For **any** EML tree `t` whatsoever — no depth bound, no shape restriction — if
`eml (eml t var) (const c)` agrees with `K/x` at two distinct positive points **at which `t` takes
the same value**, then `K = exp (exp (t.eval x₁)) > 1`.

`const a` is the special case where the agreement hypothesis is free. **The floor is `exp` being
unable to reach `0`, and that has nothing to do with how deep the tree is.** -/
theorem left_var_K_gt_one {t : EMLTree} {c K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t EMLTree.var) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t EMLTree.var) (EMLTree.const c)).eval x₂ = K) :
    1 < K := by
  rw [left_var_eval_scaled t c x₁ h₁] at e₁
  rw [left_var_eval_scaled t c x₂ h₂, ← hagree] at e₂
  have h := e₁.trans e₂.symm
  have hsub : (x₂ - x₁) * log c = 0 := by
    have e : (x₂ - x₁) * log c
        = (exp (exp (t.eval x₁)) - x₁ * log c) - (exp (exp (t.eval x₁)) - x₂ * log c) := by
      mach_mpoly [x₁, x₂, log c, exp (exp (t.eval x₁))]
    rw [e, h]; mach_mpoly [exp (exp (t.eval x₁)), x₂, log c]
  have hx : x₂ - x₁ ≠ 0 := by
    intro hz; apply hne
    have e : x₁ = x₂ - (x₂ - x₁) := by mach_ring
    rw [e, hz]; mach_ring
  have hL : log c = 0 := Classical.byContradiction (fun hL => (mul_ne_zero hx hL) hsub)
  rw [hL] at e₁
  have hK : K = exp (exp (t.eval x₁)) := by
    rw [← e₁]; mach_mpoly [x₁, exp (exp (t.eval x₁))]
  rw [hK]
  exact one_lt_exp (exp_pos _)

/-! ## The target, stated directly: `1/x` is not in this family

The bounds above say `K > 1`. **`1/x` is `K = 1`**, so it is excluded — but a reader should not have
to derive that, and stating it directly exposes exactly where the contradiction lands.
-/

/-- **`1/x` is NOT `eml (eml t var) (const c)`, for ANY `t` agreeing at two points.**

The contradiction is sharp: agreement forces `exp (exp (t.eval x₁)) = 1`, and `exp` of anything is
`> 1` when its argument is `> 0` — which `exp (t.eval x₁)` always is.

**The obstruction is not that `1` is a hard value to hit. It is that `exp` cannot reach `0`.** -/
theorem one_over_x_not_left_var {t : EMLTree} {c x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t EMLTree.var) (EMLTree.const c)).eval x₁ = 1)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t EMLTree.var) (EMLTree.const c)).eval x₂ = 1) :
    False := by
  have h := left_var_K_gt_one h₁ h₂ hne hagree e₁ e₂
  exact lt_irrefl_ax _ h

/-! ## Two sharpenings the statements above needed, found while writing this corollary

**1. `K = 0` is a trivial escape and must be excluded by hypothesis, not by hope.**
`eml (const a) (const c)` with `exp a = log c` evaluates to the CONSTANT `0`, so `x · eval x = 0` for
every `x`. That is `K = 0 ≤ 1` — but it is the zero function, not `0/x` in any useful sense. **The
theorems above are safe because their shape is `eml (eml t var) (const c)`, which this is not**; a
general "every `K/x` tree has `K > 1`" claim would be FALSE without excluding `K = 0`.

**2. Two-point agreement is strictly weaker than `= K/x` everywhere, and that is fine HERE.**
Trees exist whose `x · eval x` coincides at two points with `K ≤ 1` — e.g. `eml var (const c)` with
`c` chosen from `x₁, x₂`. **The theorems above are not weakened by this**, because their conclusion is
about the shape they name. And for the target it is exactly enough: **`1/x` agrees everywhere, so it
agrees at two points, so the exclusion bites.**

**Recorded because a future session reading only the statements would not see either.**
-/

/-! ## Root-case census: the leaf/leaf case, closed completely

`eml (const a) (const c)` evaluates to a value **independent of `x`**. So `x · eval x` can be
constant only if that value is `0` — and then `K = 0`.

**This formalises the `K = 0` escape noted above**: it is not merely *a* degenerate case, it is the
*only* thing this root shape can produce. -/
theorem const_const_forces_K_zero {a c K x₁ x₂ : Real} (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.const a) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.const a) (EMLTree.const c)).eval x₂ = K) :
    K = 0 ∧ exp a = log c := by
  have ev : ∀ y : Real,
      (EMLTree.eml (EMLTree.const a) (EMLTree.const c)).eval y = exp a - log c := fun _ => rfl
  rw [ev x₁] at e₁
  rw [ev x₂] at e₂
  have h := e₁.trans e₂.symm
  have hsub : (x₁ - x₂) * (exp a - log c) = 0 := by
    have e : (x₁ - x₂) * (exp a - log c)
        = x₁ * (exp a - log c) - x₂ * (exp a - log c) := by
      mach_mpoly [x₁, x₂, exp a, log c]
    rw [e, h]; mach_mpoly [x₂, exp a, log c]
  have hx : x₁ - x₂ ≠ 0 := by
    intro hz; apply hne
    have e : x₁ = x₂ + (x₁ - x₂) := by mach_ring
    rw [e, hz]; mach_ring
  have hv : exp a - log c = 0 :=
    Classical.byContradiction (fun hv => (mul_ne_zero hx hv) hsub)
  refine ⟨?_, ?_⟩
  · rw [← e₁, hv]; mach_ring
  · have e : exp a = (exp a - log c) + log c := by mach_ring
    rw [e, hv]; mach_ring

/-! ## Root cases 2, 4, 5 — closed for the TARGET, and the census's word "mechanical" corrected

The census called these *"reduces, mechanical"*. **Writing them showed that was too optimistic.**
None closes by the generic two-point move — that move only *determines* the free constant instead of
contradicting it. **Each closes for `1/x` specifically, by evaluating at points chosen so the
arithmetic collapses.** That is a different and weaker claim than the census made, and the difference
was found by doing the work rather than by estimating it.
-/

/-- **Case 5** — `eml var var`. Immediate: at `x = 1` the tree is `exp 1`, and `1/1 = 1 < exp 1`. -/
theorem one_over_x_not_var_var
    (e₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = 1) : False := by
  have ev : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = exp 1 - log 1 := rfl
  rw [ev, log_one] at e₁
  have h1 : exp 1 = 1 := by
    have e : exp 1 = exp 1 - 0 := by mach_ring
    rw [e, e₁]
  have h := one_lt_exp_one
  rw [h1] at h
  exact lt_irrefl_ax 1 h

/-- **Case 4** — `eml var (const c)`. Two points force `exp 1 − exp (1+1) = 1/(1+1)`, but the left
side is **negative**: `exp(1+1) = exp 1 · exp 1 > exp 1` because `exp 1 > 1`. -/
theorem one_over_x_not_var_const {c : Real}
    (e₁ : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval 1 = 1)
    (e₂ : (1 + 1) * (EMLTree.eml EMLTree.var (EMLTree.const c)).eval (1 + 1) = 1) : False := by
  have v₁ : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval 1 = exp 1 - log c := rfl
  have v₂ : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval (1 + 1)
      = exp (1 + 1) - log c := rfl
  rw [v₁] at e₁; rw [v₂] at e₂
  -- exp(1+1) = exp 1 * exp 1, and exp 1 > 1, so exp(1+1) > exp 1
  have hgrow : exp 1 < exp (1 + 1) := by
    rw [exp_add]
    have key : 1 * exp 1 < exp 1 * exp 1 :=
      mul_lt_mul_of_pos_right one_lt_exp_one (exp_pos 1)
    have e : 1 * exp 1 = exp 1 := by mach_ring
    rw [e] at key
    exact key
  -- No usable linear-arithmetic tactic over these atoms in this corpus, so the
  -- cancellation is done by hand: substitute log c, then read off a positive quantity
  -- forced to equal a negative one.
  have hc : log c = exp 1 - 1 := by
    have e : log c = exp 1 - (exp 1 - log c) := by mach_ring
    rw [e, e₁]; mach_ring
  rw [hc] at e₂
  have hpos : 0 < exp (1 + 1) - exp 1 := sub_pos_of_lt hgrow
  have htwo : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hmul : 0 < (1 + 1) * (exp (1 + 1) - exp 1) := mul_pos htwo hpos
  -- but e₂ forces that same quantity to be 1 - (1+1) = -1
  have hneg : (1 + 1) * (exp (1 + 1) - exp 1) = 1 - (1 + 1) := by
    have e : (1 + 1) * (exp (1 + 1) - exp 1)
        = (1 + 1) * (exp (1 + 1) - (exp 1 - 1)) - (1 + 1) := by
      mach_mpoly [exp (1 + 1), exp 1]
    rw [e, e₂]; mach_ring
  rw [hneg] at hmul
  -- hmul : 0 < 1 - (1+1).  Add 1 on the left: 1 + 0 < 1 + (1 - (1+1)) = 0, so 1 < 0.
  have hadd := add_lt_add_left hmul 1
  have eL : (1 : Real) + 0 = 1 := by mach_ring
  have eR : (1 : Real) + (1 - (1 + 1)) = 0 := by mach_ring
  rw [eL, eR] at hadd
  exact lt_irrefl_ax 0 (lt_trans_ax one_pos hadd)

/-- **Case 2** — `eml (const a) var`. Evaluating at `1` and at `exp 1` (where `log` is `1`) forces
`0 = 1 / exp 1`, and `exp 1 > 0`. -/
theorem one_over_x_not_const_var {a : Real}
    (e₁ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval 1 = 1)
    (e₂ : exp 1 * (EMLTree.eml (EMLTree.const a) EMLTree.var).eval (exp 1) = 1) : False := by
  have v₁ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval 1 = exp a - log 1 := rfl
  have v₂ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval (exp 1)
      = exp a - log (exp 1) := rfl
  rw [v₁, log_one] at e₁
  rw [v₂, log_exp] at e₂
  -- e₁ : exp a - 0 = 1  ⟹  exp a = 1;  e₂ : exp 1 * (exp a - 1) = 1  ⟹  0 = 1
  have ha : exp a = 1 := by
    have e : exp a = exp a - 0 := by mach_ring
    rw [e, e₁]
  rw [ha] at e₂
  have hz : exp 1 * (1 - 1) = 0 := by mach_ring
  rw [hz] at e₂
  -- e₂ : (0 : Real) = 1
  have h := one_pos
  rw [← e₂] at h
  exact lt_irrefl_ax 0 h

/-! ## The syntactic hypothesis was never needed either — `t₂` only has to be constant-VALUED

Every theorem above requires the root's right child to *be* `const c`. **The argument never used
that.** What it used is that `log (t₂.eval x)` takes the same value at the two test points — which
`const c` supplies syntactically and which **any tree agreeing at those points supplies
semantically**.

**This is not a cosmetic weakening.** The numerical search found real hits whose right child is a
genuine subtree that happens to evaluate to a constant — e.g. `(c ⊕ c)` with `c = (0, 1)` evaluates
to `exp 0 − log 1 = 1`. Those were outside every statement above and are inside this one.

**Census cases 3, 6 and 9 are therefore closed whenever `t₂` agrees at the two points.** What remains
is only `t₂` genuinely varying with `x`.
-/

/-- `x · eval (eml (eml t var) t₂) x = exp (exp (t.eval x)) − x · log (t₂.eval x)`, for **any** `t`
and **any** `t₂`. -/
theorem left_var_gen_eval_scaled (t t₂ : EMLTree) (x : Real) (hx : 0 < x) :
    x * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x
      = exp (exp (t.eval x)) - x * log (t₂.eval x) := by
  show x * (exp ((EMLTree.eml t EMLTree.var).eval x) - log (t₂.eval x)) = _
  show x * (exp (exp (t.eval x) - log x) - log (t₂.eval x)) = _
  have h : x * (exp (exp (t.eval x) - log x) - log (t₂.eval x))
      = x * exp (exp (t.eval x) - log x) - x * log (t₂.eval x) := by
    mach_mpoly [x, exp (exp (t.eval x) - log x), log (t₂.eval x)]
  rw [h, mul_exp_sub_log hx]

/-- **`K > 1` with BOTH children arbitrary trees.**

`t` and `t₂` are unrestricted — any shape, any depth. The only hypotheses are that each takes the
same value at the two test points. `const c` on the right is the special case where that is free.

**This closes census cases 3, 6 and 9 for every constant-valued `t₂`, however it is built.** -/
theorem left_var_gen_K_gt_one {t t₂ : EMLTree} {K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    -- WEAKENED 2026-08-05: the proof reads only `log (t₂.eval ·)`, never `t₂.eval ·`.
    -- That is not a cosmetic weakening HERE, because this corpus TOTALISES `log`: two
    -- genuinely different non-positive values share a `log`, and such trees satisfy this
    -- hypothesis while failing the equality one. They were excluded for no reason the
    -- proof needed.
    (h2agree : log (t₂.eval x₁) = log (t₂.eval x₂))
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₂ = K) :
    1 < K := by
  rw [left_var_gen_eval_scaled t t₂ x₁ h₁] at e₁
  rw [left_var_gen_eval_scaled t t₂ x₂ h₂, ← hagree, ← h2agree] at e₂
  have h := e₁.trans e₂.symm
  have hsub : (x₂ - x₁) * log (t₂.eval x₁) = 0 := by
    have e : (x₂ - x₁) * log (t₂.eval x₁)
        = (exp (exp (t.eval x₁)) - x₁ * log (t₂.eval x₁))
          - (exp (exp (t.eval x₁)) - x₂ * log (t₂.eval x₁)) := by
      mach_mpoly [x₁, x₂, log (t₂.eval x₁), exp (exp (t.eval x₁))]
    rw [e, h]; mach_mpoly [exp (exp (t.eval x₁)), x₂, log (t₂.eval x₁)]
  have hx : x₂ - x₁ ≠ 0 := by
    intro hz; apply hne
    have e : x₁ = x₂ - (x₂ - x₁) := by mach_ring
    rw [e, hz]; mach_ring
  have hL : log (t₂.eval x₁) = 0 :=
    Classical.byContradiction (fun hL => (mul_ne_zero hx hL) hsub)
  rw [hL] at e₁
  have hK : K = exp (exp (t.eval x₁)) := by
    rw [← e₁]; mach_mpoly [x₁, exp (exp (t.eval x₁))]
  rw [hK]
  exact one_lt_exp (exp_pos _)

/-- **`1/x` excluded with both children arbitrary.** -/
theorem one_over_x_not_left_var_gen {t t₂ : EMLTree} {x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    (h2agree : log (t₂.eval x₁) = log (t₂.eval x₂))
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₁ = 1)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₂ = 1) :
    False :=
  lt_irrefl_ax _ (left_var_gen_K_gt_one h₁ h₂ hne hagree h2agree e₁ e₂)

/-! ## The last constructor: the left child's right slot need not be `var` either

`left_var_gen_K_gt_one` still writes `var` in one place. **Re-reading the proof, what it uses is that
`x · exp(A − log (v.eval x))` is independent of `x`** — which needs `v.eval x = m · x` for a constant
`m`. **`var` is `m = 1`.**

**And this one is NOT free.** With a general `m` the conclusion weakens from `1 < K` to `1 < m · K`:
a large `m` would let `K` drop to `1`. **So the floor's last line of defence is that `m · x` is not
reachable** — and an adversarial search over depth ≤ 3, ≤ 3 constant slots, 17-value grid found
**ZERO** `eml`-rooted trees evaluating to `m · x` for any `m` whatsoever. `var` itself is the only
witness, at `m = 1`. Evidence, not proof.
-/

/-- `m · (x · exp (u − log (m·x))) = exp u`, for `0 < m`, `0 < x`. Division-free. -/
theorem mul_mul_exp_sub_log_mul {u m x : Real} (hm : 0 < m) (hx : 0 < x) :
    m * (x * exp (u - log (m * x))) = exp u := by
  have hmx : 0 < m * x := mul_pos hm hx
  have h1 : exp (log (m * x)) * exp (u - log (m * x)) = exp u := by
    rw [← exp_add]
    have e : log (m * x) + (u - log (m * x)) = u := by mach_ring
    rw [e]
  rw [exp_log hmx] at h1
  have e : m * (x * exp (u - log (m * x))) = m * x * exp (u - log (m * x)) := by
    mach_mpoly [m, x, exp (u - log (m * x))]
  rw [e, h1]

/-- **The scale-`m` generalisation.** `t`, `t₂`, `v` all arbitrary; `v` evaluates to `m·x` at the two
test points. The conclusion is `1 < m · K` — **weaker than `1 < K`, and correctly so.** -/
theorem left_scaled_K {t t₂ v : EMLTree} {K m x₁ x₂ : Real}
    (hm : 0 < m) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    (h2agree : log (t₂.eval x₁) = log (t₂.eval x₂))
    (hv₁ : v.eval x₁ = m * x₁) (hv₂ : v.eval x₂ = m * x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t v) t₂).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t v) t₂).eval x₂ = K) :
    1 < m * K := by
  have step : ∀ y : Real, 0 < y → v.eval y = m * y →
      m * (y * (EMLTree.eml (EMLTree.eml t v) t₂).eval y)
        = exp (exp (t.eval y)) - m * (y * log (t₂.eval y)) := by
    intro y hy hvy
    show m * (y * (exp ((EMLTree.eml t v).eval y) - log (t₂.eval y))) = _
    show m * (y * (exp (exp (t.eval y) - log (v.eval y)) - log (t₂.eval y))) = _
    rw [hvy]
    have e : m * (y * (exp (exp (t.eval y) - log (m * y)) - log (t₂.eval y)))
        = m * (y * exp (exp (t.eval y) - log (m * y))) - m * (y * log (t₂.eval y)) := by
      mach_mpoly [m, y, exp (exp (t.eval y) - log (m * y)), log (t₂.eval y)]
    rw [e, mul_mul_exp_sub_log_mul hm hy]
  have E₁ := step x₁ h₁ hv₁
  have E₂ := step x₂ h₂ hv₂
  rw [e₁] at E₁; rw [e₂, ← hagree, ← h2agree] at E₂
  have h := E₁.symm.trans E₂
  have hsub : (m * x₂ - m * x₁) * log (t₂.eval x₁) = 0 := by
    have e : (m * x₂ - m * x₁) * log (t₂.eval x₁)
        = (exp (exp (t.eval x₁)) - m * (x₁ * log (t₂.eval x₁)))
          - (exp (exp (t.eval x₁)) - m * (x₂ * log (t₂.eval x₁))) := by
      mach_mpoly [m, x₁, x₂, log (t₂.eval x₁), exp (exp (t.eval x₁))]
    rw [e, h]; mach_mpoly [exp (exp (t.eval x₁)), m, x₂, log (t₂.eval x₁)]
  have hx : m * x₂ - m * x₁ ≠ 0 := by
    intro hz; apply hne
    have hmne : m ≠ 0 := ne_of_gt hm
    have e : m * (x₂ - x₁) = m * x₂ - m * x₁ := by mach_mpoly [m, x₁, x₂]
    rw [← e] at hz
    have hd : x₂ - x₁ = 0 := Classical.byContradiction (fun hd => (mul_ne_zero hmne hd) hz)
    have e2 : x₁ = x₂ - (x₂ - x₁) := by mach_ring
    rw [e2, hd]; mach_ring
  have hL : log (t₂.eval x₁) = 0 :=
    Classical.byContradiction (fun hL => (mul_ne_zero hx hL) hsub)
  rw [hL] at E₁
  have hK : m * K = exp (exp (t.eval x₁)) := by
    have e : exp (exp (t.eval x₁)) - m * (x₁ * 0) = exp (exp (t.eval x₁)) := by
      mach_mpoly [m, x₁, exp (exp (t.eval x₁))]
    rw [e] at E₁; exact E₁
  rw [hK]
  exact one_lt_exp (exp_pos _)

/-- **`1/x` from this shape forces `m > 1`.** Since no `eml`-rooted tree evaluating to `m·x` was
found at all, this is the floor's remaining load-bearing gap, stated exactly. -/
theorem one_over_x_forces_m_gt_one {t t₂ v : EMLTree} {m x₁ x₂ : Real}
    (hm : 0 < m) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hagree : t.eval x₁ = t.eval x₂)
    (h2agree : log (t₂.eval x₁) = log (t₂.eval x₂))
    (hv₁ : v.eval x₁ = m * x₁) (hv₂ : v.eval x₂ = m * x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t v) t₂).eval x₁ = 1)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t v) t₂).eval x₂ = 1) :
    1 < m := by
  have h := left_scaled_K hm h₁ h₂ hne hagree h2agree hv₁ hv₂ e₁ e₂
  have e : m * 1 = m := by mach_ring
  rw [e] at h; exact h

/-- **`eml (const a) var` is never `m·x` for `m > 0`.**

Evaluating at `1` and at `exp 1` (where `log` is `1`) gives `m = 1 + m · exp 1`. But `exp 1 > 1` and
`m > 0` force `m · exp 1 > m`, so the right side exceeds `m` — **`m > m`.**

**`m > 0` is not a convenience hypothesis:** `v.eval x = m·x` sits under a `log` in the parent, so a
non-positive `m·x` is outside the intended domain anyway. -/
theorem const_var_not_mx {a m : Real} (hm : 0 < m)
    (e₁ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval 1 = m * 1)
    (e₂ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval (exp 1) = m * exp 1) :
    False := by
  have v₁ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval 1 = exp a - log 1 := rfl
  have v₂ : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval (exp 1)
      = exp a - log (exp 1) := rfl
  rw [v₁, log_one] at e₁
  rw [v₂, log_exp] at e₂
  -- e₁ : exp a - 0 = m * 1  ⟹  exp a = m
  have ha : exp a = m := by
    have e : exp a = exp a - 0 := by mach_ring
    rw [e, e₁]; mach_ring
  rw [ha] at e₂
  -- e₂ : m - 1 = m * exp 1
  have hmm : m < m * exp 1 := by
    -- only `mul_lt_mul_of_pos_right` is reachable from this import root, so commute
    have key : 1 * m < exp 1 * m := mul_lt_mul_of_pos_right one_lt_exp_one hm
    have e1 : 1 * m = m := by mach_ring
    have e2 : exp 1 * m = m * exp 1 := by mach_ring
    rw [e1, e2] at key; exact key
  -- but e₂ says m * exp 1 = m - 1, which is less than m
  have hlt : m * exp 1 < m := by
    have e : m * exp 1 = m - 1 := e₂.symm
    rw [e]
    have key := add_lt_add_left one_pos (m - 1)
    have eL : (m - 1) + 0 = m - 1 := by mach_ring
    have eR : (m - 1) + 1 = m := by mach_ring
    rw [eL, eR] at key; exact key
  exact lt_irrefl_ax _ (lt_trans_ax hmm hlt)

/-! ## The recursion, made explicit

Every remaining case has been described as *"recurses"*. **That is a remark, not a result.** The
lemma below turns it into one: it names, exactly, the next family a prover would have to handle.

**The halt is not "we do not know what happens next". It is "the next target is
`exp (exp a − m·x)`, and nothing in the corpus says whether that is reachable."** Stating it this way
means the next session attacks a named function rather than an open-ended reduction.
-/

/-- **One step of the recursion, as a theorem — for ANY target.**

`m · x` was over-strong: the proof never uses what the target IS. **Fourth instance of the pattern
in this file** — a hypothesis written as a specific expression when the argument needs only a value.

If `eml u w` hits **any** value `f` at a point where `u` is `a` and `w` is positive, the right child
is pinned: `w.eval x = exp (exp a − f)`.

**This is the regress ENGINE.** Applied to `1/x` it names `m·x`; applied to `m·x` it names
`C·exp(−m·x)`; applied to that it names `exp(A − C·exp(−m·x))`. **Each step wraps the previous
target in another `exp`/`log` layer — the targets grow while the tree shrinks.**

> **That opposition is the shape of a termination argument, and it is the first route this arm has
> had to a general result rather than another case.** -/
theorem const_left_pins_child {u w : EMLTree} {a f x : Real}
    (hu : u.eval x = a) (hw : 0 < w.eval x)
    (e : (EMLTree.eml u w).eval x = f) :
    w.eval x = exp (exp a - f) := by
  have v : (EMLTree.eml u w).eval x = exp (u.eval x) - log (w.eval x) := rfl
  rw [v, hu] at e
  -- e : exp a - log (w.eval x) = m * x
  have hlog : log (w.eval x) = exp a - f := by
    have e2 : log (w.eval x) = exp a - (exp a - log (w.eval x)) := by mach_ring
    rw [e2, e]
  have := exp_log hw          -- exp (log (w.eval x)) = w.eval x
  rw [hlog] at this
  exact this.symm

/-! ## `var`/`var`, closed — with both costs paid explicitly

**Cost 1: an axiom.** `exp_tangent_line_strict` (`EMLAsymptoticClass.lean:528`) is a
classical-citation axiom, not a theorem. **It is used here and nowhere else in this file**, so
`#print axioms` separates the theorems that depend on it from the ones that do not.

**Cost 2: one numeric fact, isolated rather than smuggled.** The chain needs `e²(e−2) > 1`, which
`2 < e` does not give (it yields only `> 0`). It is carried as the hypothesis `he`, **stated
division-free**, so the analytic argument is complete and clean and exactly one thing is owed.

**Discharge path for `he`:** the tangent bound at `t = 1/2` gives `exp(1/2) > 3/2`, hence
`e > 9/4`, hence `e²(e−2) > 81/64 > 1`. **That step needs division arithmetic, which `mach_mpoly`
cannot normalise** — the fifth instance of that friction here. Isolating `he` means the next session
buys exactly one lemma, not a proof.
-/

/-- **`exp(e) > e² + 1`** — the analytic core, given the numeric fact `he`. -/
theorem exp_exp_one_gt (he : 1 < exp 1 * exp 1 * (exp 1 - (1 + 1))) :
    exp 1 * exp 1 + 1 < exp (exp 1) := by
  have h2e : (1 : Real) + 1 < exp 1 := exp_tangent_line_strict 1 one_pos
  have hpos : 0 < exp 1 - (1 + 1) := sub_pos_of_lt h2e
  have htan := exp_tangent_line_strict (exp 1 - (1 + 1)) hpos
  -- htan : (exp 1 - (1+1)) + 1 < exp (exp 1 - (1+1))
  have hsq : (0 : Real) < exp 1 * exp 1 := mul_pos (exp_pos 1) (exp_pos 1)
  -- exp (exp 1) = exp 1 * exp 1 * exp (exp 1 - (1+1))
  have hsplit : exp (exp 1) = exp 1 * exp 1 * exp (exp 1 - (1 + 1)) := by
    have e : (1 : Real) + 1 + (exp 1 - (1 + 1)) = exp 1 := by mach_ring
    have h := exp_add (1 + 1) (exp 1 - (1 + 1))
    rw [e] at h
    rw [h, exp_add 1 1]
  -- multiply htan by the positive exp 1 * exp 1
  have hlift : ((exp 1 - (1 + 1)) + 1) * (exp 1 * exp 1)
      < exp (exp 1 - (1 + 1)) * (exp 1 * exp 1) :=
    mul_lt_mul_of_pos_right htan hsq
  -- (e−1)·e² = e²(e−2) + e².  My first attempt wrote (e²−e²·1) for the second term,
  -- which is 0 -- off by exactly e².
  have eL : ((exp 1 - (1 + 1)) + 1) * (exp 1 * exp 1)
      = exp 1 * exp 1 * (exp 1 - (1 + 1)) + exp 1 * exp 1 := by
    mach_mpoly [exp 1]
  have eR : exp (exp 1 - (1 + 1)) * (exp 1 * exp 1)
      = exp 1 * exp 1 * exp (exp 1 - (1 + 1)) := by
    mach_mpoly [exp 1, exp (exp 1 - (1 + 1))]
  rw [eL, eR, ← hsplit] at hlift
  -- hlift : e²(e−2) + e² < exp(exp 1)
  -- he    : 1 < e²(e−2),  so  e² + 1 < e² + e²(e−2) = e²(e−2) + e² < exp(exp 1)
  have hadd := add_lt_add_left he (exp 1 * exp 1)
  have ecomm : exp 1 * exp 1 + exp 1 * exp 1 * (exp 1 - (1 + 1))
      = exp 1 * exp 1 * (exp 1 - (1 + 1)) + exp 1 * exp 1 := by mach_mpoly [exp 1]
  rw [ecomm] at hadd
  exact lt_trans_ax hadd hlift

/-- **`eml var var` is never `m·x`.** At `x = 1` it forces `m = e`; at `x = exp 1` it forces
`exp(e) = e² + 1`, contradicting `exp_exp_one_gt`. -/
theorem var_var_not_mx {m : Real} (he : 1 < exp 1 * exp 1 * (exp 1 - (1 + 1)))
    (e₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = m * 1)
    (e₂ : (EMLTree.eml EMLTree.var EMLTree.var).eval (exp 1) = m * exp 1) :
    False := by
  have v₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = exp 1 - log 1 := rfl
  have v₂ : (EMLTree.eml EMLTree.var EMLTree.var).eval (exp 1)
      = exp (exp 1) - log (exp 1) := rfl
  rw [v₁, log_one] at e₁
  rw [v₂, log_exp] at e₂
  have hm : m = exp 1 := by
    have e : m = m * 1 := by mach_ring
    rw [e, ← e₁]; mach_ring
  rw [hm] at e₂
  -- e₂ : exp (exp 1) - 1 = exp 1 * exp 1
  have heq : exp 1 * exp 1 + 1 = exp (exp 1) := by
    have e : exp 1 * exp 1 + 1 = (exp (exp 1) - 1) + 1 := by rw [e₂]
    rw [e]; mach_ring
  have hgt := exp_exp_one_gt he
  rw [heq] at hgt
  exact lt_irrefl_ax _ hgt

/-! ## The CLAMPED branch — territory the searches never covered

`MachLib.Real.log` is **clamped**: `log_nonpos : x ≤ 0 → log x = 0`. So a node whose right child
goes non-positive is **not undefined — it collapses to `exp (u.eval x)`**, a pure exponential with
no subtraction.

**Every numerical search in this arm discarded that case** (79.5 % of pairs), because the guard
`if b ≤ 0 then reject` was written for floating-point safety and, against a totalised `log`, deletes
a defined case instead of skipping an undefined one.

**`1/x` from the clamped branch needs `exp (u.eval x) = 1/x`, i.e. `u` evaluating to `−log x`.**
The lemmas below are the entrance to that question: **three of its four sub-cases die on `exp_pos`
alone.**
-/

/-- If `eml p var` hits `A − log x`, then `exp (p.eval x) = A`. **The `log x` cancels; whatever is
left must be the value of an exponential.** -/
theorem eml_var_forces_exp_eq {p : EMLTree} {A x : Real}
    (e : (EMLTree.eml p EMLTree.var).eval x = A - log x) :
    exp (p.eval x) = A := by
  have v : (EMLTree.eml p EMLTree.var).eval x = exp (p.eval x) - log x := rfl
  rw [v] at e
  have h : exp (p.eval x) = (exp (p.eval x) - log x) + log x := by mach_ring
  rw [h, e]; mach_ring

/-- **`−log x` is not `eml p var`, for ANY `p`.**

`A = 0` there, so the node would force `exp (p.eval x) = 0` — and `exp` is never zero.

**This kills one of the four sub-cases of the clamped branch outright**, at every depth, with no
axiom and no numeric fact. -/
theorem neg_log_not_via_var {p : EMLTree} {x : Real}
    (e : (EMLTree.eml p EMLTree.var).eval x = 0 - log x) :
    False := by
  have h := eml_var_forces_exp_eq e
  exact absurd h (ne_of_gt (exp_pos _))

/-! ## The clamped branch reproduces the SAME floor

A clamped node is `exp (u.eval x)` — no subtraction. For it to be `K/x` its left child must hit
`log K − log x`. **And `eml_var_forces_exp_eq` already says what that costs:** the `log x` cancels and
`log K` must be the value of an exponential, hence **positive**, hence `K > 1`.

**The clamped path does not offer a cheaper route to `1/x`. It offers the same one.** That is why the
clamped search produced 3,929 new functions and not one of them is `K/x`. -/

/-- **`K > 1` on the CLAMPED branch too.**

A clamped node evaluates to `exp (u.eval x)`; with `u = eml p var` and the node equal to `K/x`
(division-free: `x · node = K`), the same identity that drove the positive branch applies —
`K = exp (exp (p.eval x))`, and `exp` of a positive number exceeds `1`.

**No axiom, no numeric fact, any depth of `p`.** -/
theorem clamped_K_over_x_gt_one {p : EMLTree} {K x : Real} (hx : 0 < x)
    (e : x * exp ((EMLTree.eml p EMLTree.var).eval x) = K) :
    1 < K := by
  have v : (EMLTree.eml p EMLTree.var).eval x = exp (p.eval x) - log x := rfl
  rw [v, mul_exp_sub_log hx] at e
  rw [← e]
  exact one_lt_exp (exp_pos _)

/-- **`1/x` is not a clamped node over `eml p var`, at any depth.** -/
theorem one_over_x_not_clamped_var {p : EMLTree} {x : Real} (hx : 0 < x)
    (e : x * exp ((EMLTree.eml p EMLTree.var).eval x) = 1) :
    False :=
  lt_irrefl_ax _ (clamped_K_over_x_gt_one hx e)

/-! ## FUNCTIONAL reasoning — the arm's first statements quantified over all `x`

Every theorem above is **pointwise**: hypotheses at specific `x` values. That technique produced
25 results and is **provably exhausted** (`METHOD_BARRIER.md`): three evaluation points give three
equations in seven unknowns, and each further point adds one equation and two unknowns.

**The residue needs statements about all `x` at once.** These are the first.

**The easy direction closes; the hard one is named at the end.**
-/

/-- **Functional: a constant-valued node with a constant-valued LEFT child has a constant-valued
RIGHT child.**

`exp a − log (w x) = c` for every `x` pins `log (w x) = exp a − c`, the same value at every point;
`w` is positive, so `exp` of both sides recovers `w` itself. -/
theorem const_node_const_left_forces_const_right {u w : EMLTree} {a c : Real}
    (hu : ∀ x : Real, 0 < x → u.eval x = a)
    (hpos : ∀ x : Real, 0 < x → 0 < w.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml u w).eval x = c) :
    ∀ x y : Real, 0 < x → 0 < y → w.eval x = w.eval y := by
  have pin : ∀ z : Real, 0 < z → log (w.eval z) = exp a - c := by
    intro z hz
    have v : (EMLTree.eml u w).eval z = exp (u.eval z) - log (w.eval z) := rfl
    have hz' := h z hz
    rw [v, hu z hz] at hz'
    have e : log (w.eval z) = exp a - (exp a - log (w.eval z)) := by mach_ring
    rw [e, hz']
  intro x y hx hy
  have hxl := pin x hx
  have hyl := pin y hy
  have hlog : log (w.eval x) = log (w.eval y) := by rw [hxl, hyl]
  have ex := exp_log (hpos x hx)
  have ey := exp_log (hpos y hy)
  rw [← ex, ← ey, hlog]

/-- **Functional: the same, for a `K/x` node.** If the left child is constant-valued and the node is
`K/x`, the right child's `log` is pinned to `exp a − K/x` — which VARIES. **So the right child of a
`K/x` node with constant-valued left child is NEVER constant-valued for `K ≠ 0`.**

**This is the exact opposite of the unblocking lemma's easy case, and it is worth stating because it
shows the lemma cannot be proved by finding constancy on the right.** -/
theorem kx_node_const_left_forces_varying_right {u w : EMLTree} {a K x y : Real}
    (hne : x ≠ y) (hK : K ≠ 0)
    (hux : u.eval x = a) (huy : u.eval y = a)
    (ex : x * (EMLTree.eml u w).eval x = K)
    (ey : y * (EMLTree.eml u w).eval y = K) :
    w.eval x ≠ w.eval y := by
  intro heq
  -- equal right values ⟹ the node takes the same value at x and y ⟹ K/x = K/y ⟹ x = y
  have vx : (EMLTree.eml u w).eval x = exp (u.eval x) - log (w.eval x) := rfl
  have vy : (EMLTree.eml u w).eval y = exp (u.eval y) - log (w.eval y) := rfl
  rw [vx, hux, heq] at ex
  rw [vy, huy] at ey
  -- ex : x * (exp a - log (w.eval y)) = K,  ey : y * (exp a - log (w.eval y)) = K
  have h := ex.trans ey.symm
  have hsub : (x - y) * (exp a - log (w.eval y)) = 0 := by
    have e : (x - y) * (exp a - log (w.eval y))
        = x * (exp a - log (w.eval y)) - y * (exp a - log (w.eval y)) := by
      mach_mpoly [x, y, exp a, log (w.eval y)]
    rw [e, h]; mach_mpoly [y, exp a, log (w.eval y)]
  have hxy : x - y ≠ 0 := by
    intro hz; apply hne
    have e : x = y + (x - y) := by mach_ring
    rw [e, hz]; mach_ring
  have hv : exp a - log (w.eval y) = 0 :=
    Classical.byContradiction (fun hv => (mul_ne_zero hxy hv) hsub)
  rw [hv] at ex
  apply hK
  rw [← ex]; mach_ring

end Real
end MachLib
