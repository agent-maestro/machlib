import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.Iteration

/-!
# Forward-error as a compositional algebra — the product rule

Frontier-1b (the operator-basis research) showed the forward-error bound of a
kernel is a *structural attribute* of its expression tree: in the standard model
each rounding op contributes a `(1+w)` factor, and the factors **compound through
a product** (the exponents ADD) but not through a nonneg sum (which takes the
max). FPModel already proves the **sum** side abstractly (`cond_combine`,
`RSum_bound`). This file supplies the missing **product** side, so the algebra is
rigorous on both:

* `npow_add` — the exponent bookkeeping `(1+w)^(a+b) = (1+w)^a · (1+w)^b`.
* `mul_grow` — **the product-composition rule.** If `x` is magnitude-bounded by
  `(1+w)^a · |xe|` and `y` by `(1+w)^b · |ye|`, then a rounded product
  `p ≈ x·y` is bounded by `(1+w)^(a+b+1) · |xe|·|ye|`: the operand exponents add,
  plus one for the multiply's own rounding. This is exactly why
  Frontier-1b's corrected depth counts SUM children through a `×` (the v1 that
  took the max under-counted product chains).

Composing `mul_grow` (products) with `cond_combine` (sums) up an expression tree
derives the `(1+w)^d - 1` bound for any kernel from its operators — the
"prove ~12 operator rules once, get 92% of the library" dividend, made rigorous.

`sorryAx`-free, Mathlib-free. Builds on `FPModel` (`RoundsW`, `roundsW_abs`,
`abs_le_one_add`) and `Iteration` (`npow_nonneg`).
-/

namespace MachLib.Real

/-! Fresh-var ring identities (mach_mpoly's atom parser dislikes
recursion/param terms like `npow a x`, so the algebra is factored out). -/
theorem ea_mulswap3 (x p q : Real) : x * (p * q) = p * (x * q) := by mach_mpoly [x, p, q]
theorem ea_regroup (p s q t : Real) : (p * s) * (q * t) = (p * q) * (s * t) := by
  mach_mpoly [p, s, q, t]
theorem ea_assoc3 (a b c : Real) : a * (b * c) = (a * b) * c := by mach_mpoly [a, b, c]

/-- Exponent law for `npow`: `x^(a+b) = x^a · x^b`. -/
theorem npow_add (x : Real) (a : Nat) : ∀ b, npow (a + b) x = npow a x * npow b x
  | 0     => by rw [Nat.add_zero, show npow 0 x = 1 from rfl]; mach_ring
  | b + 1 => by
      rw [Nat.add_succ, npow_succ, npow_succ, npow_add x a b,
          ea_mulswap3 x (npow a x) (npow b x)]

/-- **Product-composition rule.** Magnitude bounds with growth exponents `a`, `b`
compose through a rounded product into exponent `a+b+1` (operands add, +1 for the
multiply's rounding). The `×`-analogue of `cond_combine`; together they propagate
forward-error over any expression tree. -/
theorem mul_grow {w x y p xe ye : Real} {a b : Nat}
    (hw : 0 ≤ w)
    (hx : abs x ≤ npow a (1 + w) * abs xe)
    (hy : abs y ≤ npow b (1 + w) * abs ye)
    (hp : RoundsW w p (x * y)) :
    abs p ≤ npow (a + b + 1) (1 + w) * (abs xe * abs ye) := by
  have h1w : (0 : Real) ≤ 1 + w :=
    le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw)
  -- |p| ≤ (1+w)·|x·y| = (1+w)·(|x|·|y|)
  have h1 : abs p ≤ (1 + w) * abs (x * y) := abs_le_one_add (roundsW_abs hp)
  rw [abs_mul] at h1
  -- |x|·|y| ≤ (npow a (1+w)·|xe|)·(npow b (1+w)·|ye|)
  have hax : 0 ≤ npow a (1 + w) * abs xe := mul_nonneg (npow_nonneg h1w a) (abs_nonneg xe)
  have hxy : abs x * abs y ≤ (npow a (1 + w) * abs xe) * (npow b (1 + w) * abs ye) :=
    le_trans (mul_le_mul_of_nonneg_right hx (abs_nonneg y))
             (mul_le_mul_of_nonneg_left hy hax)
  -- regroup and fold the exponents: = npow (a+b) (1+w) · (|xe|·|ye|)
  rw [ea_regroup (npow a (1 + w)) (abs xe) (npow b (1 + w)) (abs ye),
      ← npow_add (1 + w) a b] at hxy
  -- |p| ≤ (1+w)·(npow (a+b) (1+w) · (|xe|·|ye|)) = npow (a+b+1) (1+w) · (|xe|·|ye|)
  have h2 : (1 + w) * (abs x * abs y)
      ≤ (1 + w) * (npow (a + b) (1 + w) * (abs xe * abs ye)) :=
    mul_le_mul_of_nonneg_left hxy h1w
  have hfold : (1 + w) * (npow (a + b) (1 + w) * (abs xe * abs ye))
      = npow (a + b + 1) (1 + w) * (abs xe * abs ye) := by
    rw [npow_succ]; exact ea_assoc3 (1 + w) (npow (a + b) (1 + w)) (abs xe * abs ye)
  exact le_trans h1 (le_trans h2 (le_of_eq hfold))

end MachLib.Real
