import MachLib.Exp
import MachLib.Log
import MachLib.Forge
import MachLib.Trig
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.IteratedExpBounds
import MachLib.AnalyticFiniteZeros

/-!
# Differentiation Infrastructure — header port for analytic derivative usage

Ports the statement of `HasDerivAt` and the basic derivative-rule
toolbox (the analytic-derivative usage seen in monogate-lean's
InfiniteZerosBarrier and its upstream sources)
into MachLib as axioms. This is the second of the two routes
identified for closing the 2 remaining depth-2 sin barrier cases (the
first being Khovanskii uniform bounds).

The port provides:

1. **`HasDerivAt f f' x`** predicate (opaque axiom).
2. **Base-function derivatives** as axioms:
   - `Real.exp`'s derivative is `Real.exp` itself.
   - `Real.log`'s derivative is `1 / x` on `(0, ∞)`.
   - `Real.sin`'s derivative is `Real.cos`.
   - `Real.cos`'s derivative is `-Real.sin`.
3. **Composition / arithmetic rules** as axioms:
   - constant rule, identity rule
   - add, sub, mul rules
   - chain rule
   - reciprocal rule

4. **Uniqueness of derivative**: if `HasDerivAt f a x` and
   `HasDerivAt f b x`, then `a = b`.

5. **From global equality, derivative equality**: if `f = g` globally,
   then their derivatives agree where defined.

**Honest scope:** This is a header port. The semantic content of
`HasDerivAt` is axiomatized; a future formalization could replace
the axioms with a power-series or limit-based definition.

**Closing the 2 remaining cases with this infrastructure:**

For each of Case 4 (Row 3 vc-vc) and Case 2 (Row 3 cv-vc), differentiate
`t.eval x = sin x` to get `t.eval'(x) = cos(x)`. Compute `t.eval'(x)`
symbolically from the EML structure:

For Case 4: `t.eval x = exp(exp x - log d1) - log(exp x - log d)`.
`t.eval'(x) = exp(exp x - log d1) · exp x - (1/(exp x - log d)) · exp x`
           ` = exp x · [exp(exp x - log d1) - 1/(exp x - log d)]`.

Evaluate at a specific x where this can be shown > 1 in absolute value
(contradicting `|cos x| ≤ 1`), OR show asymptotic unboundedness.

The closure proofs for the 2 cases are NOT in this file. They require
combining the 3-point constraints (E0, E1, Eπ) with the derivative
constraint at one or more specific points. This is a focused 1-2 session
follow-up artifact.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## The `HasDerivAt` predicate -/

/-- `HasDerivAt f f' x` means the function `f` has derivative `f'` at the
point `x`. Axiomatized; a future formalization could replace this with a
power-series-based or limit-based definition. -/
axiom HasDerivAt (f : Real → Real) (f' : Real) (x : Real) : Prop

/-- Uniqueness of the derivative. -/
axiom HasDerivAt_unique (f : Real → Real) (a b : Real) (x : Real) :
    HasDerivAt f a x → HasDerivAt f b x → a = b

/-! ## Base-function derivatives -/

/-- Constant function has derivative 0. -/
axiom HasDerivAt_const (c : Real) (x : Real) :
    HasDerivAt (fun _ => c) 0 x

/-- Identity function has derivative 1. -/
axiom HasDerivAt_id (x : Real) : HasDerivAt (fun x => x) 1 x

/-- `(exp x)' = exp x`. -/
axiom HasDerivAt_exp (x : Real) : HasDerivAt Real.exp (Real.exp x) x

/-- `(log x)' = 1 / x` for `x > 0`. (On `x ≤ 0`, MachLib's `log` is
constant 0, so the derivative would be 0 there; we restrict to the
analytic domain.) -/
axiom HasDerivAt_log_pos (x : Real) :
    0 < x → HasDerivAt Real.log (1 / x) x

/-- `(sin x)' = cos x`. -/
axiom HasDerivAt_sin (x : Real) : HasDerivAt Real.sin (Real.cos x) x

/-- `(cos x)' = -sin x`. -/
axiom HasDerivAt_cos (x : Real) : HasDerivAt Real.cos (-Real.sin x) x

/-! ## Closure rules -/

/-- Sum rule: `(f + g)' = f' + g'`. -/
axiom HasDerivAt_add (f g : Real → Real) (a b : Real) (x : Real) :
    HasDerivAt f a x → HasDerivAt g b x →
    HasDerivAt (fun y => f y + g y) (a + b) x

/-- Difference rule: `(f - g)' = f' - g'`. -/
axiom HasDerivAt_sub (f g : Real → Real) (a b : Real) (x : Real) :
    HasDerivAt f a x → HasDerivAt g b x →
    HasDerivAt (fun y => f y - g y) (a - b) x

/-- Product rule: `(f · g)' = f' · g + f · g'`. -/
axiom HasDerivAt_mul (f g : Real → Real) (a b : Real) (x : Real) :
    HasDerivAt f a x → HasDerivAt g b x →
    HasDerivAt (fun y => f y * g y) (a * g x + f x * b) x

/-- Chain rule: `(f ∘ g)' = f'(g(x)) · g'(x)`. -/
axiom HasDerivAt_comp (f g : Real → Real) (a b : Real) (x : Real) :
    HasDerivAt g a x →
    HasDerivAt f b (g x) →
    HasDerivAt (fun y => f (g y)) (b * a) x

/-- Reciprocal rule: `(1/f)' = -f' / f^2` when `f x ≠ 0`. -/
axiom HasDerivAt_inv (f : Real → Real) (a : Real) (x : Real) :
    f x ≠ 0 → HasDerivAt f a x →
    HasDerivAt (fun y => 1 / f y) (-a / (f x * f x)) x

/-- Negation rule: `(-f)' = -f'`. -/
axiom HasDerivAt_neg (f : Real → Real) (a : Real) (x : Real) :
    HasDerivAt f a x → HasDerivAt (fun y => -f y) (-a) x

/-! ## From global function equality to derivative equality -/

/-- If two functions agree globally, their derivatives agree pointwise
wherever both exist. -/
axiom HasDerivAt_of_eq (f g : Real → Real) (a : Real) (x : Real) :
    (∀ y, f y = g y) → HasDerivAt f a x → HasDerivAt g a x

/-- **Local congruence.** `HasDerivAt` depends only on `f`'s behavior in an arbitrarily small
neighborhood of `x`: if `f` and `g` agree throughout some neighborhood of `x`, a derivative of one
transfers to the other. This is the standard local/neighborhood-invariance property any genuine
notion of pointwise differentiability satisfies (unlike `HasDerivAt_of_eq` above, which needs
agreement EVERYWHERE) — MachLib's opaque axiomatization had not yet stated it. -/
axiom HasDerivAt_congr (f g : Real → Real) (a x : Real)
    (h : ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y = g y) :
    HasDerivAt f a x → HasDerivAt g a x

/-! ## `log`'s derivative on the clamped (non-positive) side

MachLib's `Real.log` is piecewise: the analytic `ln` for `x > 0`, clamped to the constant `0` for
`x ≤ 0` (`log_nonpos`, `Log.lean`). `HasDerivAt_log_pos` above covers the analytic side. On the
clamped side, `log` is LITERALLY the constant-`0` function throughout any neighborhood that stays
`≤ 0` — so `HasDerivAt_congr` against `HasDerivAt_const` gives its derivative there for free, no new
axiom needed. -/

/-- **`(log x)' = 0` for `x < 0`.** Derived, not axiomatized: `log` agrees with the constant-`0`
function throughout the neighborhood `(2x, 0)` of `x` (every point there is `< 0`, hence clamped),
so its derivative transfers from `HasDerivAt_const` via `HasDerivAt_congr`. -/
theorem HasDerivAt_log_neg {x : Real} (hx : x < 0) : HasDerivAt Real.log 0 x := by
  have hxpos : (0 : Real) < -x := by
    have h2 := add_lt_add_left hx (-x)
    rwa [neg_add_self, add_zero] at h2
  refine HasDerivAt_congr (fun _ => (0 : Real)) Real.log 0 x ⟨-x, hxpos, fun y hy => ?_⟩
    (HasDerivAt_const 0 x)
  have hle : y - x ≤ abs (y - x) := by
    rcases lt_total (y - x) 0 with h | h | h
    · exact le_of_lt (lt_of_lt_of_le h (abs_nonneg _))
    · rw [h]; exact abs_nonneg 0
    · rw [abs_of_nonneg (le_of_lt h)]; exact le_refl _
  have hlt : y - x < -x := lt_of_le_of_lt hle hy
  have hylt : y < 0 := by
    have h2 := add_lt_add_left hlt x
    rwa [show x + (y - x) = y from by mach_mpoly [x, y], add_neg] at h2
  exact (Real.log_nonpos (le_of_lt hylt)).symm

end Real
end MachLib

/-!
## Strategy for closing the 2 remaining cases

The 2 deferred cases (Row 3 cv-vc and Row 3 vc-vc) both have the
hypothesis `t.eval x = sin x` for all x.

Differentiating both sides: `t.eval'(x) = cos(x)`.

For Case 4 (Row 3 vc-vc): `t = .eml(.eml(.var, .const d1), .eml(.var, .const d))`.
`t.eval x = exp(exp x - log d1) - log(exp x - log d)`.

Symbolic derivative (using chain + sub):
`t.eval'(x) = exp(exp x - log d1) · exp x - (1/(exp x - log d)) · exp x`
           ` = exp x · [exp(exp x - log d1) - 1/(exp x - log d)]`.

Pick a specific x to contradict `|cos x| ≤ 1`:

At `x = 0` (assuming `log d, log d1 ≤ 0` for log convention to give 0,
which corresponds to d, d1 ≤ 0; this sub-case probably needs splitting):
`t.eval'(0) = 1 · [exp(1) - 1/(1 - 0)] = exp 1 - 1`. And `cos 0 = 1`.
So `exp 1 - 1 = 1`, i.e., `exp 1 = 2`. But `exp_one_gt_two : 2 < exp 1`,
contradiction.

For `d, d1 > 0` (log d, log d1 real), the analysis is more involved but
follows the same structure: use the constraints from (E0), (E1), (Eπ)
combined with the derivative constraint at one or two specific points.

For Case 2 (Row 3 cv-vc), similar.

**The closure proofs are deferred to a focused follow-up artifact**
that combines this differentiation infrastructure with the per-case
algebra. The infrastructure itself is the reusable contribution here.
-/

-- Demonstration / sub-case proofs deferred to a focused follow-up
-- artifact that case-splits on d ≤ 0 vs d > 0 and combines the
-- algebraic and derivative arguments.
