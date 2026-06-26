import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.Linarith
import MachLib.MPolyRing

/-!
# `MachLib.FPModel` — verified forward-error for the EML scalar fragment

Forge emits one EML kernel to many targets. MachLib already proves a
property of a kernel's **exact real** semantics (`vec3_length_sq ≥ 0`,
…). The cross-target story has been *regression-tested* — the
conformance harness samples WGSL≈Rust at `1e-6` — but not **proven**.

This module is the first rung of proving it: a forward-error bound
relating a kernel's IEEE-754 `f64` evaluation to its exact `Real`
value. EML's restriction to straight-line scalar math (no loops, no
memory) is what makes this tractable where general compiler
verification is CompCert-scale — the equivalence is a closed-form
expression bound, not a semantics-preservation theorem.

**The model.** We use the *standard model of floating-point arithmetic*
(Higham, *Accuracy and Stability of Numerical Algorithms* §2.2): a
correctly-rounded operation returns the exact result perturbed by a
relative error of at most one unit roundoff `u`. We axiomatize exactly
that one fact — in the same Mathlib-free, single-axiom spirit as
MachLib's `abs_add` / `abs_mul`. For IEEE binary64, `u = 2⁻⁵³`.

`Rounds fl e` says machine value `fl` is a valid rounding of exact `e`:
`fl = e·(1+δ)` with `|δ| ≤ u`. A kernel's `f64` evaluation is any value
obtained by rounding at each node; the theorems hold for *every* such
rounding (a universal forward-error bound).

**Headline:** for `length_sq` (all summands `≥ 0`, so no catastrophic
cancellation) the `f64` result is within the tight relative bound
`(1+u)ⁿ − 1` of the exact value — `≈ n·u`, the expected order.
-/

namespace MachLib.Real

/-- Unit roundoff. For IEEE-754 binary64 (`f64`), `u = 2⁻⁵³ ≈ 1.1·10⁻¹⁶`.
Kept abstract; every bound below holds for any `0 ≤ u ≤ 1`. -/
axiom u : Real
axiom u_nonneg : (0 : Real) ≤ u
axiom u_le_one : u ≤ 1

/-- The standard model of floating-point arithmetic: `fl` is a valid
rounding of the exact real `e` when `fl = e·(1+δ)` for some relative
perturbation `|δ| ≤ u` (written `-u ≤ δ ≤ u`). -/
def Rounds (fl e : Real) : Prop :=
  ∃ δ : Real, -u ≤ δ ∧ δ ≤ u ∧ fl = e * (1 + δ)

/-- `abs t ≤ B` from the two one-sided bounds, by splitting the `if` in
`abs`'s definition — no `not_le` needed. -/
theorem abs_le_of {t B : Real} (h1 : t ≤ B) (h2 : -t ≤ B) : abs t ≤ B := by
  unfold abs
  by_cases h : 0 ≤ t
  · rw [if_pos h]; exact h1
  · rw [if_neg h]; exact h2

/-! ### Order/sign preliminaries (Mathlib-free, derived from MachLib primitives) -/

theorem neg_nonneg_of_nonpos {x : Real} (h : x ≤ 0) : 0 ≤ -x := by
  have hc : x + (-x) ≤ 0 + (-x) := add_le_add_both h (le_refl (-x))
  have e1 : x + (-x) = 0 := by mach_ring
  have e2 : (0 : Real) + (-x) = -x := by mach_ring
  rw [e1, e2] at hc; exact hc

theorem neg_le_neg {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  have hc : a + (-a + -b) ≤ b + (-a + -b) := add_le_add_both h (le_refl (-a + -b))
  have e1 : a + (-a + -b) = -b := by mach_mpoly [a, b]
  have e2 : b + (-a + -b) = -a := by mach_mpoly [a, b]
  rw [e1, e2] at hc; exact hc

theorem mul_self_nonneg (x : Real) : 0 ≤ x * x := by
  rcases lt_total 0 x with h | h | h
  · exact mul_nonneg (le_of_lt h) (le_of_lt h)
  · have hx : x = 0 := h.symm
    rw [hx, mul_zero]; exact le_refl 0
  · have hnx : 0 ≤ -x := neg_nonneg_of_nonpos (le_of_lt h)
    have hp : 0 ≤ (-x) * (-x) := mul_nonneg hnx hnx
    have e : (-x) * (-x) = x * x := by mach_ring
    rw [e] at hp; exact hp

theorem sub_le_sub_right {a b : Real} (h : a ≤ b) (c : Real) : a - c ≤ b - c := by
  rw [sub_def, sub_def]; exact add_le_add_both h (le_refl (-c))

theorem sub_le_sub_left {a b : Real} (h : a ≤ b) (c : Real) : c - b ≤ c - a := by
  rw [sub_def, sub_def]; exact add_le_add_both (le_refl c) (neg_le_neg h)

theorem one_add_u_nonneg : (0 : Real) ≤ 1 + u := by
  have : (0 : Real) ≤ 1 := le_of_lt one_pos
  exact le_trans this (le_add_of_nonneg_right u_nonneg)

theorem one_sub_u_nonneg : (0 : Real) ≤ 1 - u := sub_nonneg_of_le u_le_one

theorem one_sub_u_le_one : (1 : Real) - u ≤ 1 := sub_le_self u_nonneg

/-- Upper bound from one rounding of a nonnegative quantity. -/
theorem Rounds.upper {fl e : Real} (h : Rounds fl e) (he : 0 ≤ e) :
    fl ≤ e * (1 + u) := by
  obtain ⟨δ, _, hδu, hfl⟩ := h
  rw [hfl]
  exact mul_le_mul_of_nonneg_left (add_le_add_left hδu 1) he

/-- Lower bound from one rounding of a nonnegative quantity. -/
theorem Rounds.lower {fl e : Real} (h : Rounds fl e) (he : 0 ≤ e) :
    e * (1 - u) ≤ fl := by
  obtain ⟨δ, hδl, _, hfl⟩ := h
  rw [hfl]
  have : (1 : Real) - u ≤ 1 + δ := by
    have := add_le_add_left hδl 1
    -- 1 + (-u) ≤ 1 + δ  ⟹  1 - u ≤ 1 + δ
    have e1 : (1 : Real) + (-u) = 1 - u := by mach_ring
    rw [e1] at this; exact this
  exact mul_le_mul_of_nonneg_left this he

/-- A rounded nonnegative quantity is nonnegative (uses `u ≤ 1`). -/
theorem Rounds.nonneg {fl e : Real} (h : Rounds fl e) (he : 0 ≤ e) :
    0 ≤ fl := by
  have h1 : e * (1 - u) ≤ fl := Rounds.lower h he
  have h2 : (0 : Real) ≤ e * (1 - u) := mul_nonneg he one_sub_u_nonneg
  exact le_trans h2 h1

/-- **2D forward-error.** The `f64` evaluation of `x² + y²` (round each
product, then round the sum) is within the relative bound `(1+u)² − 1`
of the exact value. -/
theorem length_sq2_fwd_error
    (x y : Real) (p1 p2 r : Real)
    (hp1 : Rounds p1 (x * x)) (hp2 : Rounds p2 (y * y))
    (hr : Rounds r (p1 + p2)) :
    abs (r - (x * x + y * y)) ≤ ((1 + u) * (1 + u) - 1) * (x * x + y * y) := by
  have hxx : (0 : Real) ≤ x * x := mul_self_nonneg x
  have hyy : (0 : Real) ≤ y * y := mul_self_nonneg y
  have hsum : (0 : Real) ≤ x * x + y * y := add_nonneg hxx hyy
  have hp1n : (0 : Real) ≤ p1 := Rounds.nonneg hp1 hxx
  have hp2n : (0 : Real) ≤ p2 := Rounds.nonneg hp2 hyy
  have hp12 : (0 : Real) ≤ p1 + p2 := add_nonneg hp1n hp2n
  -- upper: r ≤ (x²+y²)(1+u)²
  have u1 : p1 ≤ x * x * (1 + u) := Rounds.upper hp1 hxx
  have u2 : p2 ≤ y * y * (1 + u) := Rounds.upper hp2 hyy
  have usum : p1 + p2 ≤ (x * x + y * y) * (1 + u) := by
    have := add_le_add_both u1 u2
    have e : x * x * (1 + u) + y * y * (1 + u) = (x * x + y * y) * (1 + u) := by mach_ring
    rw [e] at this; exact this
  have ur : r ≤ (p1 + p2) * (1 + u) := Rounds.upper hr hp12
  have urb : r ≤ (x * x + y * y) * (1 + u) * (1 + u) :=
    le_trans ur (mul_le_mul_of_nonneg_right usum one_add_u_nonneg)
  -- lower: (x²+y²)(1-u)² ≤ r
  have l1 : x * x * (1 - u) ≤ p1 := Rounds.lower hp1 hxx
  have l2 : y * y * (1 - u) ≤ p2 := Rounds.lower hp2 hyy
  have lsum : (x * x + y * y) * (1 - u) ≤ p1 + p2 := by
    have := add_le_add_both l1 l2
    have e : x * x * (1 - u) + y * y * (1 - u) = (x * x + y * y) * (1 - u) := by mach_ring
    rw [e] at this; exact this
  have lr : (p1 + p2) * (1 - u) ≤ r := Rounds.lower hr hp12
  have lrb : (x * x + y * y) * (1 - u) * (1 - u) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right lsum one_sub_u_nonneg) lr
  -- assemble the abs bound
  apply abs_le_of
  · -- r - (x²+y²) ≤ ((1+u)²-1)(x²+y²)
    have : r - (x * x + y * y) ≤ (x * x + y * y) * (1 + u) * (1 + u) - (x * x + y * y) :=
      sub_le_sub_right urb (x * x + y * y)
    have e : (x * x + y * y) * (1 + u) * (1 + u) - (x * x + y * y)
        = ((1 + u) * (1 + u) - 1) * (x * x + y * y) := by mach_mpoly [x, y, u]
    rw [e] at this; exact this
  · -- (x²+y²) - r ≤ ((1+u)²-1)(x²+y²)
    have hneg : -(r - (x * x + y * y)) = (x * x + y * y) - r := by mach_ring
    rw [hneg]
    have : (x * x + y * y) - r ≤ (x * x + y * y) - (x * x + y * y) * (1 - u) * (1 - u) :=
      sub_le_sub_left lrb (x * x + y * y)
    -- (x²+y²)(1-(1-u)²) ≤ (x²+y²)((1+u)²-1)   since (1+u)²+(1-u)² ≥ 2
    have step : (x * x + y * y) - (x * x + y * y) * (1 - u) * (1 - u)
        ≤ ((1 + u) * (1 + u) - 1) * (x * x + y * y) := by
      have key : (1 : Real) - (1 - u) * (1 - u) ≤ (1 + u) * (1 + u) - 1 := by
        -- (1+u)² + (1-u)² - 2 = 2u² ≥ 0
        have hdiff : (1 + u) * (1 + u) - 1 - (1 - (1 - u) * (1 - u)) = u * u + u * u := by
          mach_mpoly [u]
        have hnn : (0 : Real) ≤ u * u + u * u := add_nonneg (mul_self_nonneg u) (mul_self_nonneg u)
        have hd : (0 : Real) ≤ (1 + u) * (1 + u) - 1 - (1 - (1 - u) * (1 - u)) := by
          rw [hdiff]; exact hnn
        exact le_of_sub_nonneg hd
      have e1 : (x * x + y * y) - (x * x + y * y) * (1 - u) * (1 - u)
          = (1 - (1 - u) * (1 - u)) * (x * x + y * y) := by mach_mpoly [x, y, u]
      rw [e1]
      exact mul_le_mul_of_nonneg_right key hsum
    exact le_trans this step

/-- `1 ≤ 1 + u`. -/
theorem one_le_one_add_u : (1 : Real) ≤ 1 + u := le_add_of_nonneg_right u_nonneg

/-- `A ≤ A·(1+u)` for `0 ≤ A` (one more rounding can only grow a nonneg bound). -/
theorem le_mul_one_add_u {A : Real} (hA : 0 ≤ A) : A ≤ A * (1 + u) := by
  have hstep : A * 1 ≤ A * (1 + u) := mul_le_mul_of_nonneg_left one_le_one_add_u hA
  have e : A * 1 = A := by mach_ring
  rw [e] at hstep; exact hstep

/-- **3D forward-error — the `vec3_length_sq` kernel.** The `f64`
evaluation of `x² + y² + z²` (round each product, then the two sums) is
within the tight relative bound `(1+u)³ − 1 ≈ 3u` of the exact value.
This is the same kernel whose exact-`Real` nonnegativity MachLib already
proves (`vec3_length_sq_nonneg`): the two together say the shipped `f64`
output is nonneg-up-to-`3u` of a value proven `≥ 0`. -/
theorem length_sq3_fwd_error
    (x y z : Real) (p1 p2 p3 s r : Real)
    (hp1 : Rounds p1 (x * x)) (hp2 : Rounds p2 (y * y)) (hp3 : Rounds p3 (z * z))
    (hs : Rounds s (p2 + p3)) (hr : Rounds r (p1 + s)) :
    abs (r - (x * x + y * y + z * z))
      ≤ ((1 + u) * (1 + u) * (1 + u) - 1) * (x * x + y * y + z * z) := by
  have hxx : (0 : Real) ≤ x * x := mul_self_nonneg x
  have hyy : (0 : Real) ≤ y * y := mul_self_nonneg y
  have hzz : (0 : Real) ≤ z * z := mul_self_nonneg z
  have hxy : (0 : Real) ≤ x * x + y * y := add_nonneg hxx hyy
  have hsum : (0 : Real) ≤ x * x + y * y + z * z := add_nonneg hxy hzz
  have hp2n : (0 : Real) ≤ p2 := Rounds.nonneg hp2 hyy
  have hp3n : (0 : Real) ≤ p3 := Rounds.nonneg hp3 hzz
  have hp23 : (0 : Real) ≤ p2 + p3 := add_nonneg hp2n hp3n
  have hp1n : (0 : Real) ≤ p1 := Rounds.nonneg hp1 hxx
  have hsn : (0 : Real) ≤ s := Rounds.nonneg hs hp23
  have hp1s : (0 : Real) ≤ p1 + s := add_nonneg hp1n hsn
  -- upper chain: r ≤ (x²+y²+z²)(1+u)³
  have u1 : p1 ≤ x * x * (1 + u) := Rounds.upper hp1 hxx
  have u2 : p2 ≤ y * y * (1 + u) := Rounds.upper hp2 hyy
  have u3 : p3 ≤ z * z * (1 + u) := Rounds.upper hp3 hzz
  have u23 : p2 + p3 ≤ (y * y + z * z) * (1 + u) := by
    have := add_le_add_both u2 u3
    have e : y * y * (1 + u) + z * z * (1 + u) = (y * y + z * z) * (1 + u) := by
      mach_mpoly [y, z, u]
    rw [e] at this; exact this
  have us : s ≤ (y * y + z * z) * (1 + u) * (1 + u) :=
    le_trans (Rounds.upper hs hp23) (mul_le_mul_of_nonneg_right u23 one_add_u_nonneg)
  have u1s : p1 + s ≤ (x * x + y * y + z * z) * (1 + u) * (1 + u) := by
    have hadd := add_le_add_both u1 us
    have hx1 : x * x * (1 + u) ≤ x * x * (1 + u) * (1 + u) :=
      le_mul_one_add_u (mul_nonneg hxx one_add_u_nonneg)
    have hsum2 : x * x * (1 + u) + (y * y + z * z) * (1 + u) * (1 + u)
        ≤ (x * x + y * y + z * z) * (1 + u) * (1 + u) := by
      have h := add_le_add_both hx1 (le_refl ((y * y + z * z) * (1 + u) * (1 + u)))
      have e : x * x * (1 + u) * (1 + u) + (y * y + z * z) * (1 + u) * (1 + u)
          = (x * x + y * y + z * z) * (1 + u) * (1 + u) := by mach_mpoly [x, y, z, u]
      rw [e] at h; exact h
    exact le_trans hadd hsum2
  have urb : r ≤ (x * x + y * y + z * z) * (1 + u) * (1 + u) * (1 + u) :=
    le_trans (Rounds.upper hr hp1s) (mul_le_mul_of_nonneg_right u1s one_add_u_nonneg)
  -- lower chain: (x²+y²+z²)(1-u)³ ≤ r
  have l1 : x * x * (1 - u) ≤ p1 := Rounds.lower hp1 hxx
  have l2 : y * y * (1 - u) ≤ p2 := Rounds.lower hp2 hyy
  have l3 : z * z * (1 - u) ≤ p3 := Rounds.lower hp3 hzz
  have l23 : (y * y + z * z) * (1 - u) ≤ p2 + p3 := by
    have := add_le_add_both l2 l3
    have e : y * y * (1 - u) + z * z * (1 - u) = (y * y + z * z) * (1 - u) := by
      mach_mpoly [y, z, u]
    rw [e] at this; exact this
  have ls : (y * y + z * z) * (1 - u) * (1 - u) ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right l23 one_sub_u_nonneg) (Rounds.lower hs hp23)
  have l1s : (x * x + y * y + z * z) * (1 - u) * (1 - u) ≤ p1 + s := by
    have hadd := add_le_add_both l1 ls
    have hx1 : x * x * (1 - u) * (1 - u) ≤ x * x * (1 - u) := by
      have hA : (0 : Real) ≤ x * x * (1 - u) := mul_nonneg hxx one_sub_u_nonneg
      have hstep : x * x * (1 - u) * (1 - u) ≤ x * x * (1 - u) * 1 :=
        mul_le_mul_of_nonneg_left one_sub_u_le_one hA
      have e : x * x * (1 - u) * 1 = x * x * (1 - u) := by mach_ring
      rw [e] at hstep; exact hstep
    have hsum2 : (x * x + y * y + z * z) * (1 - u) * (1 - u)
        ≤ x * x * (1 - u) + (y * y + z * z) * (1 - u) * (1 - u) := by
      have h := add_le_add_both hx1 (le_refl ((y * y + z * z) * (1 - u) * (1 - u)))
      have e : x * x * (1 - u) * (1 - u) + (y * y + z * z) * (1 - u) * (1 - u)
          = (x * x + y * y + z * z) * (1 - u) * (1 - u) := by mach_mpoly [x, y, z, u]
      rw [e] at h; exact h
    exact le_trans hsum2 hadd
  have lrb : (x * x + y * y + z * z) * (1 - u) * (1 - u) * (1 - u) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right l1s one_sub_u_nonneg) (Rounds.lower hr hp1s)
  -- assemble
  apply abs_le_of
  · have hsub : r - (x * x + y * y + z * z)
        ≤ (x * x + y * y + z * z) * (1 + u) * (1 + u) * (1 + u) - (x * x + y * y + z * z) :=
      sub_le_sub_right urb (x * x + y * y + z * z)
    have e : (x * x + y * y + z * z) * (1 + u) * (1 + u) * (1 + u) - (x * x + y * y + z * z)
        = ((1 + u) * (1 + u) * (1 + u) - 1) * (x * x + y * y + z * z) := by
      mach_mpoly [x, y, z, u]
    rw [e] at hsub; exact hsub
  · have hneg : -(r - (x * x + y * y + z * z)) = (x * x + y * y + z * z) - r := by mach_ring
    rw [hneg]
    have hsub : (x * x + y * y + z * z) - r
        ≤ (x * x + y * y + z * z) - (x * x + y * y + z * z) * (1 - u) * (1 - u) * (1 - u) :=
      sub_le_sub_left lrb (x * x + y * y + z * z)
    have step : (x * x + y * y + z * z)
          - (x * x + y * y + z * z) * (1 - u) * (1 - u) * (1 - u)
        ≤ ((1 + u) * (1 + u) * (1 + u) - 1) * (x * x + y * y + z * z) := by
      have key : (1 : Real) - (1 - u) * (1 - u) * (1 - u)
          ≤ (1 + u) * (1 + u) * (1 + u) - 1 := by
        have hdiff : (1 + u) * (1 + u) * (1 + u) - 1
              - (1 - (1 - u) * (1 - u) * (1 - u))
            = u * u + u * u + u * u + u * u + u * u + u * u := by mach_mpoly [u]
        have hnn : (0 : Real) ≤ u * u + u * u + u * u + u * u + u * u + u * u :=
          add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
            (mul_self_nonneg u) (mul_self_nonneg u)) (mul_self_nonneg u))
            (mul_self_nonneg u)) (mul_self_nonneg u)) (mul_self_nonneg u)
        have hd : (0 : Real) ≤ (1 + u) * (1 + u) * (1 + u) - 1
            - (1 - (1 - u) * (1 - u) * (1 - u)) := by rw [hdiff]; exact hnn
        exact le_of_sub_nonneg hd
      have e1 : (x * x + y * y + z * z)
            - (x * x + y * y + z * z) * (1 - u) * (1 - u) * (1 - u)
          = (1 - (1 - u) * (1 - u) * (1 - u)) * (x * x + y * y + z * z) := by
        mach_mpoly [x, y, z, u]
      rw [e1]
      exact mul_le_mul_of_nonneg_right key hsum
    exact le_trans hsub step

/-! ## Precision-generic conditioned bounds — the mixed-sign / cancellation case

`length_sq` was the clean case: all summands `≥ 0`, so a *relative* bound holds.
Real kernels like `dot` and `lerp` mix signs (and subtract), so a relative
bound is false near cancellation. The honest statement bounds the **absolute**
error by the **conditioning quantity** `Σ |term|` — and we parameterize the
model over the precision's unit roundoff `w` (f64 `= 2⁻⁵³`, f32 `= 2⁻²⁴`,
bf16 `= 2⁻⁸`), so one theorem covers every target. -/

/-- The standard FP model, parameterized by the precision's unit roundoff `w`.
(`Rounds` above is this at the ambient `w = u`.) -/
def RoundsW (w fl e : Real) : Prop :=
  ∃ δ : Real, -w ≤ δ ∧ δ ≤ w ∧ fl = e * (1 + δ)

/-- `e·(1+d) − e = e·d` (helper; stated with fresh vars so `mach_mpoly`'s
atom parser doesn't trip on an `obtain`-destructured fvar). -/
theorem mul_one_add_sub (e d : Real) : e * (1 + d) - e = e * d := by mach_mpoly [e, d]

/-- Absolute error of one rounding, any precision: `|fl − e| ≤ w·|e|`. -/
theorem roundsW_abs {w fl e : Real} (h : RoundsW w fl e) : abs (fl - e) ≤ w * abs e := by
  obtain ⟨δ, hδl, hδu, hfl⟩ := h
  have hnd : -δ ≤ w := by
    have h1 : -δ ≤ -(-w) := neg_le_neg hδl
    have h2 : -(-w) = w := by mach_ring
    rw [h2] at h1; exact h1
  have hδabs : abs δ ≤ w := abs_le_of hδu hnd
  have hfe : fl - e = e * δ := by rw [hfl]; exact mul_one_add_sub e δ
  rw [hfe, abs_mul, mul_comm (abs e) (abs δ)]
  exact mul_le_mul_of_nonneg_right hδabs (abs_nonneg e)

/-- `|p| ≤ (1+w)·|e|` when `p` is within `w·|e|` of `e`. -/
theorem abs_le_one_add {w p e : Real} (h : abs (p - e) ≤ w * abs e) :
    abs p ≤ (1 + w) * abs e := by
  have ht : abs p ≤ abs e + abs (p - e) := by
    have e1 : p = e + (p - e) := by mach_ring
    have htri := abs_add e (p - e)
    rw [← e1] at htri; exact htri
  have h2 : abs e + abs (p - e) ≤ abs e + w * abs e := add_le_add_left h (abs e)
  have e2 : abs e + w * abs e = (1 + w) * abs e := by mach_ring
  rw [e2] at h2; exact le_trans ht h2

/-- **`dot2` conditioned forward-error.** The `f64`/`f32` evaluation of
`a·b + c·d` — a *mixed-sign* sum, the cancellation-prone case `length_sq`
avoids — is within `(1+w)² − 1 ≈ 2w` of the exact value, measured against the
**conditioning quantity** `|a·b| + |c·d|`. (Not `|result|`: if the result
cancels to ≈ 0 the *relative* error is unbounded — this absolute-vs-Σ|term|
form is the honest one.) Holds for any unit roundoff `w ≥ 0`, so the same
theorem is the f64 *and* the f32/WGSL bound. -/
theorem dot2_fwd_error (w : Real) (hw0 : 0 ≤ w)
    (a b c d : Real) (p1 p2 r : Real)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d))
    (hr : RoundsW w r (p1 + p2)) :
    abs (r - (a * b + c * d))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (a * b) + abs (c * d)) := by
  have hsplit : abs (r - (a * b + c * d))
      ≤ abs (r - (p1 + p2)) + abs ((p1 + p2) - (a * b + c * d)) := by
    have e : r - (a * b + c * d) = (r - (p1 + p2)) + ((p1 + p2) - (a * b + c * d)) := by
      mach_mpoly [r, p1, p2, a, b, c, d]
    rw [e]; exact abs_add _ _
  have hp1b : abs p1 ≤ (1 + w) * abs (a * b) := abs_le_one_add (roundsW_abs hp1)
  have hp2b : abs p2 ≤ (1 + w) * abs (c * d) := abs_le_one_add (roundsW_abs hp2)
  have hsumb : abs (p1 + p2) ≤ (1 + w) * (abs (a * b) + abs (c * d)) := by
    have ht := abs_add p1 p2
    have hadd := add_le_add_both hp1b hp2b
    have e : (1 + w) * abs (a * b) + (1 + w) * abs (c * d)
        = (1 + w) * (abs (a * b) + abs (c * d)) := by mach_mpoly [w, abs (a * b), abs (c * d)]
    rw [e] at hadd
    exact le_trans ht hadd
  have ht1 : abs (r - (p1 + p2)) ≤ w * ((1 + w) * (abs (a * b) + abs (c * d))) :=
    le_trans (roundsW_abs hr) (mul_le_mul_of_nonneg_left hsumb hw0)
  have ht2 : abs ((p1 + p2) - (a * b + c * d)) ≤ w * (abs (a * b) + abs (c * d)) := by
    have hd : (p1 + p2) - (a * b + c * d) = (p1 - a * b) + (p2 - c * d) := by mach_ring
    rw [hd]
    have htri := abs_add (p1 - a * b) (p2 - c * d)
    have hadd := add_le_add_both (roundsW_abs hp1) (roundsW_abs hp2)
    have e : w * abs (a * b) + w * abs (c * d) = w * (abs (a * b) + abs (c * d)) := by
      mach_mpoly [w, abs (a * b), abs (c * d)]
    rw [e] at hadd
    exact le_trans htri hadd
  have hcomb := add_le_add_both ht1 ht2
  have efinal : w * ((1 + w) * (abs (a * b) + abs (c * d))) + w * (abs (a * b) + abs (c * d))
      = ((1 + w) * (1 + w) - 1) * (abs (a * b) + abs (c * d)) := by
    mach_mpoly [w, abs (a * b), abs (c * d)]
  rw [efinal] at hcomb
  exact le_trans hsplit hcomb

end MachLib.Real
