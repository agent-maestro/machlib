import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.Iteration

/-!
# Magnitude-growth as a compositional algebra — the product rule

NOTE ON SCOPE (corrected): the `*_grow` lemmas here bound the **magnitude** of a
computed value — `|v| ≤ (1+w)^d · F` — i.e. the *upper* half of the standard
model. That is a real, compositional Higham running-error magnitude bound, but it
is NOT the forward error `|v − ve|` (which also needs the lower side). The TRUE
two-sided forward-error algebra is `MachLib.ForwardError` (`renc_mul`/`renc_add`/
`renc_fwd`, giving `|v − ve| ≤ ((1+w)^d − 1)·ve`); the transcendental rules in
`ErrorAlgebraTrans` are likewise genuine forward error. Read `*_grow` below as
*magnitude growth*, not forward error.

Frontier-1b showed this magnitude bound is a *structural attribute* of the tree:
each rounding op contributes a `(1+w)` factor, and the factors **compound through
a product** (exponents ADD) but not through a nonneg sum (which takes the max).
This file supplies the **product** magnitude rule (FPModel/`cond_combine` give the
sum side):

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
theorem ea_distrib (a b c : Real) : a * b + a * c = a * (b + c) := by mach_mpoly [a, b, c]

/-- Sum of nonnegs is nonneg — used by generated leaf-factor nonneg proofs. -/
theorem add_nonneg_ea {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have h := add_le_add_both ha hb
  have e : (0 : Real) + 0 = 0 := by mach_ring
  rw [e] at h; exact h

/-- Exponent law for `npow`: `x^(a+b) = x^a · x^b`. -/
theorem npow_add (x : Real) (a : Nat) : ∀ b, npow (a + b) x = npow a x * npow b x
  | 0     => by rw [Nat.add_zero, show npow 0 x = 1 from rfl]; mach_ring
  | b + 1 => by
      rw [Nat.add_succ, npow_succ, npow_succ, npow_add x a b,
          ea_mulswap3 x (npow a x) (npow b x)]

/-- **Product-composition rule (magnitude).** Magnitude bounds with growth
exponents `a`, `b` compose through a rounded product into exponent `a+b+1`
(operands add, +1 for the multiply's rounding). The `×`-analogue of `cond_combine`;
together they propagate the *magnitude* bound over any expression tree. (The
forward-error analogue is `ForwardError.renc_mul`.) -/
theorem mul_grow {w x y p X Y : Real} {a b : Nat}
    (hw : 0 ≤ w) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : abs x ≤ npow a (1 + w) * X)
    (hy : abs y ≤ npow b (1 + w) * Y)
    (hp : RoundsW w p (x * y)) :
    abs p ≤ npow (a + b + 1) (1 + w) * (X * Y) := by
  have h1w : (0 : Real) ≤ 1 + w :=
    le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw)
  have h1 : abs p ≤ (1 + w) * abs (x * y) := abs_le_one_add (roundsW_abs hp)
  rw [abs_mul] at h1
  have hax : 0 ≤ npow a (1 + w) * X := mul_nonneg (npow_nonneg h1w a) hX
  have hxy : abs x * abs y ≤ (npow a (1 + w) * X) * (npow b (1 + w) * Y) :=
    le_trans (mul_le_mul_of_nonneg_right hx (abs_nonneg y))
             (mul_le_mul_of_nonneg_left hy hax)
  rw [ea_regroup (npow a (1 + w)) X (npow b (1 + w)) Y, ← npow_add (1 + w) a b] at hxy
  have h2 : (1 + w) * (abs x * abs y) ≤ (1 + w) * (npow (a + b) (1 + w) * (X * Y)) :=
    mul_le_mul_of_nonneg_left hxy h1w
  have hfold : (1 + w) * (npow (a + b) (1 + w) * (X * Y))
      = npow (a + b + 1) (1 + w) * (X * Y) := by
    rw [npow_succ]; exact ea_assoc3 (1 + w) (npow (a + b) (1 + w)) (X * Y)
  exact le_trans h1 (le_trans h2 (le_of_eq hfold))

/-! ## exponent lifting + the sum rule (completes the arithmetic interface) -/

/-- `npow` is monotone in the exponent for base `≥ 1` (additive-gap form). -/
theorem npow_mono {z : Real} (hz1 : 1 ≤ z) (a : Nat) :
    ∀ k, npow a z ≤ npow (a + k) z
  | 0     => le_refl _
  | k + 1 => by
      rw [Nat.add_succ, npow_succ]
      have hz0 : 0 ≤ z := le_trans (le_of_lt one_pos) hz1
      have hnn : 0 ≤ npow (a + k) z := npow_nonneg hz0 (a + k)
      have hstep : npow (a + k) z ≤ z * npow (a + k) z := by
        have h := mul_le_mul_of_nonneg_right hz1 hnn
        rwa [one_mul_thm] at h
      exact le_trans (npow_mono hz1 a k) hstep

theorem npow_mono_le {z : Real} (hz1 : 1 ≤ z) {a b : Nat} (hab : a ≤ b) :
    npow a z ≤ npow b z := by
  obtain ⟨k, hk⟩ := Nat.le.dest hab
  rw [← hk]; exact npow_mono hz1 a k

/-- Lift a magnitude bound to any larger exponent (so two operands can be
brought to a common exponent before the sum rule). -/
theorem npow_le_lift {w X v : Real} {a m : Nat}
    (hw : 0 ≤ w) (hX : 0 ≤ X)
    (hv : abs v ≤ npow a (1 + w) * X) (ham : a ≤ m) :
    abs v ≤ npow m (1 + w) * X := by
  have h1w : (1 : Real) ≤ 1 + w := le_add_of_nonneg_right hw
  exact le_trans hv (mul_le_mul_of_nonneg_right (npow_mono_le h1w ham) hX)

/-- **Sum-composition rule (nonneg).** Two operands at a *common* exponent `m`
combine through a rounded sum into exponent `m+1` — the exponent does NOT
compound (unlike a product). The `+`-analogue of `mul_grow`; lift first with
`npow_le_lift` to share `m = max a b`. -/
theorem add_grow {w x y p X Y : Real} {m : Nat}
    (hw : 0 ≤ w)
    (hx : abs x ≤ npow m (1 + w) * X)
    (hy : abs y ≤ npow m (1 + w) * Y)
    (hp : RoundsW w p (x + y)) :
    abs p ≤ npow (m + 1) (1 + w) * (X + Y) := by
  have h1w : (0 : Real) ≤ 1 + w :=
    le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw)
  have h1 : abs p ≤ (1 + w) * abs (x + y) := abs_le_one_add (roundsW_abs hp)
  have hchain : abs (x + y) ≤ npow m (1 + w) * (X + Y) := by
    rw [← ea_distrib (npow m (1 + w)) X Y]
    exact le_trans (abs_add x y) (add_le_add_both hx hy)
  have h4 : (1 + w) * abs (x + y) ≤ (1 + w) * (npow m (1 + w) * (X + Y)) :=
    mul_le_mul_of_nonneg_left hchain h1w
  have hfold : (1 + w) * (npow m (1 + w) * (X + Y)) = npow (m + 1) (1 + w) * (X + Y) := by
    rw [npow_succ]; exact ea_assoc3 (1 + w) (npow m (1 + w)) (X + Y)
  exact le_trans h1 (le_trans h4 (le_of_eq hfold))

/-! ## the certifier interface: leaf base case + a worked composition

Templates the certifier emits for the **magnitude** bound: every leaf gets
`leaf_bound` (exponent 0), every `×` node `mul_grow`, every `+` node `add_grow`.
`length_sq2_compose` shows the fold closes end-to-end. (For the TRUE forward
error `|s − exact|`, the analogous fold over the two-sided rules is
`ForwardError.length_sq2_fwd_compose`.) -/

/-- Base case: a leaf (variable/constant) equals its own exact value — exponent 0. -/
theorem leaf_bound (w x : Real) : abs x ≤ npow 0 (1 + w) * abs x := by
  have e : npow 0 (1 + w) * abs x = abs x := by
    rw [show npow 0 (1 + w) = 1 from rfl]; exact one_mul_thm (abs x)
  exact le_of_eq e.symm

/-- **Worked composition (magnitude)** — `length_sq2 = x*x + y*y`, folding
`leaf_bound` → `mul_grow` → `add_grow` to bound `|s| ≤ (1+w)²·exact`. This is the
*magnitude* fold; the forward-error counterpart is
`ForwardError.length_sq2_fwd_compose`. -/
theorem length_sq2_compose {w x y px py s : Real}
    (hw : 0 ≤ w)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py)) :
    abs s ≤ npow 2 (1 + w) * (abs x * abs x + abs y * abs y) :=
  add_grow hw
    (mul_grow hw (abs_nonneg x) (abs_nonneg x) (leaf_bound w x) (leaf_bound w x) hpx)
    (mul_grow hw (abs_nonneg y) (abs_nonneg y) (leaf_bound w y) (leaf_bound w y) hpy)
    hs

end MachLib.Real
