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
    (h2agree : t₂.eval x₁ = t₂.eval x₂)
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
    (hagree : t.eval x₁ = t.eval x₂) (h2agree : t₂.eval x₁ = t₂.eval x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₁ = 1)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml t EMLTree.var) t₂).eval x₂ = 1) :
    False :=
  lt_irrefl_ax _ (left_var_gen_K_gt_one h₁ h₂ hne hagree h2agree e₁ e₂)

end Real
end MachLib
