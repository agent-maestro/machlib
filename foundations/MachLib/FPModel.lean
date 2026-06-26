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

theorem le_of_eq {a b : Real} (h : a = b) : a ≤ b := h ▸ le_refl a

theorem le_abs_self (t : Real) : t ≤ abs t := by
  unfold abs
  rcases lt_total 0 t with h | h | h
  · rw [if_pos (le_of_lt h)]; exact le_refl t
  · rw [if_pos (le_of_eq h)]; exact le_refl t
  · have hnt : ¬ (0 ≤ t) := fun hle => lt_irrefl_ax (0 : Real) (lt_of_le_of_lt hle h)
    rw [if_neg hnt]
    exact le_trans (le_of_lt h) (neg_nonneg_of_nonpos (le_of_lt h))

theorem neg_le_abs (t : Real) : -t ≤ abs t := by
  unfold abs
  rcases lt_total 0 t with h | h | h
  · rw [if_pos (le_of_lt h)]
    exact le_trans (neg_nonpos_of_nonneg (le_of_lt h)) (le_of_lt h)
  · have ht : (0 : Real) ≤ t := le_of_eq h
    rw [if_pos ht]; exact le_trans (neg_nonpos_of_nonneg ht) ht
  · have hnt : ¬ (0 ≤ t) := fun hle => lt_irrefl_ax (0 : Real) (lt_of_le_of_lt hle h)
    rw [if_neg hnt]; exact le_refl _

theorem le_of_abs_le {t B : Real} (h : abs t ≤ B) : t ≤ B := le_trans (le_abs_self t) h
theorem neg_le_of_abs_le {t B : Real} (h : abs t ≤ B) : -t ≤ B := le_trans (neg_le_abs t) h

/-- **Cross-target agreement.** Two evaluations of the *same* exact value `e`
agree within the sum of their forward-error bounds. With the f64 bound (`B1`)
and the f32/WGSL bound (`B2`) of a kernel, this proves the two *targets* agree —
the exact statement the conformance harness samples, now a theorem. -/
theorem cross_target {r1 r2 e B1 B2 : Real}
    (h1 : abs (r1 - e) ≤ B1) (h2 : abs (r2 - e) ≤ B2) :
    abs (r1 - r2) ≤ B1 + B2 := by
  apply abs_le_of
  · have ha : r1 - e ≤ B1 := le_of_abs_le h1
    have hb : e - r2 ≤ B2 := by
      have hn := neg_le_of_abs_le h2
      have e1 : -(r2 - e) = e - r2 := by mach_mpoly [r2, e]
      rw [e1] at hn; exact hn
    have hsum := add_le_add_both ha hb
    have e2 : (r1 - e) + (e - r2) = r1 - r2 := by mach_mpoly [r1, r2, e]
    rw [e2] at hsum; exact hsum
  · have ha : r2 - e ≤ B2 := le_of_abs_le h2
    have hb : e - r1 ≤ B1 := by
      have hn := neg_le_of_abs_le h1
      have e1 : -(r1 - e) = e - r1 := by mach_mpoly [r1, e]
      rw [e1] at hn; exact hn
    have hsum := add_le_add_both ha hb
    have e2 : (r2 - e) + (e - r1) = -(r1 - r2) := by mach_mpoly [r1, r2, e]
    have e3 : B2 + B1 = B1 + B2 := by mach_mpoly [B1, B2]
    rw [e2, e3] at hsum; exact hsum

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

/-- `|p| ≤ |e| + E` when `p` is within `E` of `e`. -/
theorem abs_le_add_err {p e E : Real} (h : abs (p - e) ≤ E) : abs p ≤ abs e + E := by
  have e1 : p = e + (p - e) := by mach_mpoly [p, e]
  have ht := abs_add e (p - e)
  rw [← e1] at ht
  exact le_trans ht (add_le_add_left h (abs e))

/-- **The conditioned-sum building block.** One rounding node `r = ⌊acc + x⌉`,
where `acc` approximates exact `e` within budget `Eacc` and `x` approximates
`ex` within `Ex`: the rounded sum approximates `e + ex` within
`w·((|e|+Eacc)+(|ex|+Ex)) + (Eacc+Ex)`. Every `dotN`/`lerp` bound above is a
chain of this lemma — it is what makes the conditioned method compose over an
*arbitrary* summation tree, with no per-kernel reproof. -/
theorem cond_combine (w : Real) (hw0 : 0 ≤ w)
    {acc x r e ex Eacc Ex : Real}
    (hacc : abs (acc - e) ≤ Eacc) (hx : abs (x - ex) ≤ Ex)
    (hr : RoundsW w r (acc + x)) :
    abs (r - (e + ex)) ≤ w * ((abs e + Eacc) + (abs ex + Ex)) + (Eacc + Ex) := by
  have hsplit : abs (r - (e + ex)) ≤ abs (r - (acc + x)) + abs ((acc + x) - (e + ex)) := by
    have eq : r - (e + ex) = (r - (acc + x)) + ((acc + x) - (e + ex)) := by
      mach_mpoly [r, acc, x, e, ex]
    rw [eq]; exact abs_add _ _
  have ht1 : abs (r - (acc + x)) ≤ w * ((abs e + Eacc) + (abs ex + Ex)) := by
    have hsum : abs (acc + x) ≤ (abs e + Eacc) + (abs ex + Ex) :=
      le_trans (abs_add acc x) (add_le_add_both (abs_le_add_err hacc) (abs_le_add_err hx))
    exact le_trans (roundsW_abs hr) (mul_le_mul_of_nonneg_left hsum hw0)
  have ht2 : abs ((acc + x) - (e + ex)) ≤ Eacc + Ex := by
    have hd : (acc + x) - (e + ex) = (acc - e) + (x - ex) := by mach_mpoly [acc, x, e, ex]
    rw [hd]; exact le_trans (abs_add _ _) (add_le_add_both hacc hx)
  exact le_trans hsplit (add_le_add_both ht1 ht2)

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

/-- `0 ≤ 1 + w` for `0 ≤ w`. -/
theorem zero_le_one_add {w : Real} (hw0 : 0 ≤ w) : (0 : Real) ≤ 1 + w :=
  le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw0)

/-- **`dot3` conditioned forward-error — the `vec3` dot kernel.** Reuses
`dot2` for the inner `(ay·by + az·bz)` subtree, then combines with `ax·bx`
at the final rounding. Within `(1+w)³ − 1 ≈ 3w` of the exact value, against
the conditioning quantity `|ax·bx| + |ay·by| + |az·bz|`. -/
theorem dot3_fwd_error (w : Real) (hw0 : 0 ≤ w)
    (ax bx ay by_ az bz : Real) (p1 p2 p3 s r : Real)
    (hp1 : RoundsW w p1 (ax * bx)) (hp2 : RoundsW w p2 (ay * by_))
    (hp3 : RoundsW w p3 (az * bz))
    (hs : RoundsW w s (p2 + p3)) (hr : RoundsW w r (p1 + s)) :
    abs (r - (ax * bx + (ay * by_ + az * bz)))
      ≤ ((1 + w) * (1 + w) * (1 + w) - 1)
          * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz))) := by
  have h1w : (0 : Real) ≤ 1 + w := zero_le_one_add hw0
  -- inner subtree via dot2
  have hsE : abs (s - (ay * by_ + az * bz))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz)) :=
    dot2_fwd_error w hw0 ay by_ az bz p2 p3 s hp2 hp3 hs
  -- |s| ≤ (1+w)²(B+C)
  have hsBound : abs s ≤ (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)) := by
    have htri : abs s ≤ abs (ay * by_ + az * bz) + abs (s - (ay * by_ + az * bz)) := by
      have e1 : s = (ay * by_ + az * bz) + (s - (ay * by_ + az * bz)) := by
        mach_mpoly [s, ay, by_, az, bz]
      have ha := abs_add (ay * by_ + az * bz) (s - (ay * by_ + az * bz))
      rw [← e1] at ha; exact ha
    have hBC : abs (ay * by_ + az * bz) ≤ abs (ay * by_) + abs (az * bz) := abs_add _ _
    have step := add_le_add_both hBC hsE
    have e : (abs (ay * by_) + abs (az * bz))
          + ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz))
        = (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)) := by
      mach_mpoly [w, abs (ay * by_), abs (az * bz)]
    rw [e] at step
    exact le_trans htri step
  have hp1Bound : abs p1 ≤ (1 + w) * abs (ax * bx) := abs_le_one_add (roundsW_abs hp1)
  -- outer split
  have hsplit : abs (r - (ax * bx + (ay * by_ + az * bz)))
      ≤ abs (r - (p1 + s)) + abs ((p1 + s) - (ax * bx + (ay * by_ + az * bz))) := by
    have e : r - (ax * bx + (ay * by_ + az * bz))
        = (r - (p1 + s)) + ((p1 + s) - (ax * bx + (ay * by_ + az * bz))) := by
      mach_mpoly [r, p1, s, ax, bx, ay, by_, az, bz]
    rw [e]; exact abs_add _ _
  have hps : abs (p1 + s)
      ≤ (1 + w) * abs (ax * bx) + (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)) :=
    le_trans (abs_add p1 s) (add_le_add_both hp1Bound hsBound)
  have ht1 : abs (r - (p1 + s))
      ≤ w * ((1 + w) * abs (ax * bx)
          + (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz))) :=
    le_trans (roundsW_abs hr) (mul_le_mul_of_nonneg_left hps hw0)
  have ht2 : abs ((p1 + s) - (ax * bx + (ay * by_ + az * bz)))
      ≤ w * abs (ax * bx) + ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz)) := by
    have hd : (p1 + s) - (ax * bx + (ay * by_ + az * bz))
        = (p1 - ax * bx) + (s - (ay * by_ + az * bz)) := by
      mach_mpoly [p1, s, ax, bx, ay, by_, az, bz]
    rw [hd]
    exact le_trans (abs_add _ _) (add_le_add_both (roundsW_abs hp1) hsE)
  have hcomb := add_le_add_both ht1 ht2
  -- boundexpr ≤ ((1+w)³−1)(A+B+C): the difference is w(1+w)²·|ax·bx| ≥ 0
  have hfinal : w * ((1 + w) * abs (ax * bx)
            + (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)))
          + (w * abs (ax * bx)
            + ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz)))
      ≤ ((1 + w) * (1 + w) * (1 + w) - 1)
          * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz))) := by
    have hnn : (0 : Real) ≤ w * (1 + w) * (1 + w) * abs (ax * bx) :=
      mul_nonneg (mul_nonneg (mul_nonneg hw0 h1w) h1w) (abs_nonneg _)
    have hdiff : ((1 + w) * (1 + w) * (1 + w) - 1)
              * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz)))
            - (w * ((1 + w) * abs (ax * bx)
                + (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)))
              + (w * abs (ax * bx)
                + ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz))))
          = w * (1 + w) * (1 + w) * abs (ax * bx) := by
      mach_mpoly [w, abs (ax * bx), abs (ay * by_), abs (az * bz)]
    have hd : (0 : Real) ≤ ((1 + w) * (1 + w) * (1 + w) - 1)
              * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz)))
            - (w * ((1 + w) * abs (ax * bx)
                + (1 + w) * (1 + w) * (abs (ay * by_) + abs (az * bz)))
              + (w * abs (ax * bx)
                + ((1 + w) * (1 + w) - 1) * (abs (ay * by_) + abs (az * bz)))) := by
      rw [hdiff]; exact hnn
    exact le_of_sub_nonneg hd
  exact le_trans hsplit (le_trans hcomb hfinal)

/-- **`lerp` conditioned forward-error — `a + (b−a)·t`.** The `(b−a)`
subtraction is itself a cancellation source, so the conditioning quantity is
`|a| + |(b−a)·t|`. Within `(1+w)³ − 1` of the exact value. Eval order:
`g = ⌊b−a⌉`, `m = ⌊g·t⌉`, `res = ⌊a+m⌉`. -/
theorem lerp_fwd_error (w : Real) (hw0 : 0 ≤ w)
    (a b t : Real) (g m res : Real)
    (hg : RoundsW w g (b - a)) (hm : RoundsW w m (g * t))
    (hres : RoundsW w res (a + m)) :
    abs (res - (a + (b - a) * t))
      ≤ ((1 + w) * (1 + w) * (1 + w) - 1) * (abs a + abs ((b - a) * t)) := by
  -- inner: |m − (b−a)·t| ≤ ((1+w)²−1)·|(b−a)·t|  (a product with one pre-rounded operand)
  have hmE : abs (m - (b - a) * t) ≤ ((1 + w) * (1 + w) - 1) * abs ((b - a) * t) := by
    have hsplit : abs (m - (b - a) * t) ≤ abs (m - g * t) + abs (g * t - (b - a) * t) := by
      have e : m - (b - a) * t = (m - g * t) + (g * t - (b - a) * t) := by
        mach_mpoly [m, g, b, a, t]
      rw [e]; exact abs_add _ _
    have hgt : abs (g * t) ≤ (1 + w) * abs ((b - a) * t) := by
      have hg1 : abs g ≤ (1 + w) * abs (b - a) := abs_le_one_add (roundsW_abs hg)
      rw [abs_mul g t]
      have step : abs g * abs t ≤ ((1 + w) * abs (b - a)) * abs t :=
        mul_le_mul_of_nonneg_right hg1 (abs_nonneg t)
      have e : ((1 + w) * abs (b - a)) * abs t = (1 + w) * abs ((b - a) * t) := by
        rw [abs_mul (b - a) t]; mach_mpoly [w, abs (b - a), abs t]
      rw [e] at step; exact step
    have hm1 : abs (m - g * t) ≤ w * ((1 + w) * abs ((b - a) * t)) :=
      le_trans (roundsW_abs hm) (mul_le_mul_of_nonneg_left hgt hw0)
    have hm2 : abs (g * t - (b - a) * t) ≤ w * abs ((b - a) * t) := by
      have e1 : g * t - (b - a) * t = (g - (b - a)) * t := by mach_mpoly [g, b, a, t]
      rw [e1, abs_mul (g - (b - a)) t]
      have step : abs (g - (b - a)) * abs t ≤ (w * abs (b - a)) * abs t :=
        mul_le_mul_of_nonneg_right (roundsW_abs hg) (abs_nonneg t)
      have e2 : (w * abs (b - a)) * abs t = w * abs ((b - a) * t) := by
        rw [abs_mul (b - a) t]; mach_mpoly [w, abs (b - a), abs t]
      rw [e2] at step; exact step
    have hcomb := add_le_add_both hm1 hm2
    have efinal : w * ((1 + w) * abs ((b - a) * t)) + w * abs ((b - a) * t)
        = ((1 + w) * (1 + w) - 1) * abs ((b - a) * t) := by mach_mpoly [w, abs ((b - a) * t)]
    rw [efinal] at hcomb
    exact le_trans hsplit hcomb
  -- |m| ≤ (1+w)²·|(b−a)·t|
  have hmBound : abs m ≤ (1 + w) * (1 + w) * abs ((b - a) * t) := by
    have htri : abs m ≤ abs ((b - a) * t) + abs (m - (b - a) * t) := by
      have e1 : m = (b - a) * t + (m - (b - a) * t) := by mach_mpoly [m, b, a, t]
      have ha := abs_add ((b - a) * t) (m - (b - a) * t)
      rw [← e1] at ha; exact ha
    have step := add_le_add_left hmE (abs ((b - a) * t))
    have e : abs ((b - a) * t) + ((1 + w) * (1 + w) - 1) * abs ((b - a) * t)
        = (1 + w) * (1 + w) * abs ((b - a) * t) := by mach_mpoly [w, abs ((b - a) * t)]
    rw [e] at step
    exact le_trans htri step
  -- outer
  have hsplit : abs (res - (a + (b - a) * t))
      ≤ abs (res - (a + m)) + abs (m - (b - a) * t) := by
    have e : res - (a + (b - a) * t) = (res - (a + m)) + (m - (b - a) * t) := by
      mach_mpoly [res, a, m, b, t]
    rw [e]; exact abs_add _ _
  have hres1 : abs (res - (a + m))
      ≤ w * (abs a + (1 + w) * (1 + w) * abs ((b - a) * t)) := by
    have ham : abs (a + m) ≤ abs a + (1 + w) * (1 + w) * abs ((b - a) * t) :=
      le_trans (abs_add a m) (add_le_add_left hmBound (abs a))
    exact le_trans (roundsW_abs hres) (mul_le_mul_of_nonneg_left ham hw0)
  have hcomb := add_le_add_both hres1 hmE
  -- boundexpr ≤ ((1+w)³−1)(|a|+P): difference is ((1+w)³−1−w)·|a| ≥ 0
  have hfinal : w * (abs a + (1 + w) * (1 + w) * abs ((b - a) * t))
          + ((1 + w) * (1 + w) - 1) * abs ((b - a) * t)
      ≤ ((1 + w) * (1 + w) * (1 + w) - 1) * (abs a + abs ((b - a) * t)) := by
    have hcube : (0 : Real) ≤ (1 + w) * (1 + w) * (1 + w) - 1 - w := by
      have e : (1 + w) * (1 + w) * (1 + w) - 1 - w
          = w + w + w * w + w * w + w * w + w * w * w := by mach_mpoly [w]
      have hnn : (0 : Real) ≤ w + w + w * w + w * w + w * w + w * w * w :=
        add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hw0 hw0)
          (mul_self_nonneg w)) (mul_self_nonneg w)) (mul_self_nonneg w))
          (mul_nonneg (mul_self_nonneg w) hw0)
      rw [e]; exact hnn
    have hnn : (0 : Real) ≤ ((1 + w) * (1 + w) * (1 + w) - 1 - w) * abs a :=
      mul_nonneg hcube (abs_nonneg a)
    have hdiff : ((1 + w) * (1 + w) * (1 + w) - 1) * (abs a + abs ((b - a) * t))
            - (w * (abs a + (1 + w) * (1 + w) * abs ((b - a) * t))
              + ((1 + w) * (1 + w) - 1) * abs ((b - a) * t))
          = ((1 + w) * (1 + w) * (1 + w) - 1 - w) * abs a := by
      mach_mpoly [w, abs a, abs ((b - a) * t)]
    have hd : (0 : Real) ≤ ((1 + w) * (1 + w) * (1 + w) - 1) * (abs a + abs ((b - a) * t))
            - (w * (abs a + (1 + w) * (1 + w) * abs ((b - a) * t))
              + ((1 + w) * (1 + w) - 1) * abs ((b - a) * t)) := by rw [hdiff]; exact hnn
    exact le_of_sub_nonneg hd
  exact le_trans hsplit (le_trans hcomb hfinal)

/-- **`dot3` cross-target — Rust f64 vs WGSL f32, proven.** The two precisions'
evaluations of the same `vec3` dot agree within the sum of their forward-error
bounds — the `assert_close(gpu, cpu)` the harness samples, now a theorem (with
the precisions `w1`, `w2` left free: f64 `= 2⁻⁵³`, f32 `= 2⁻²⁴`). -/
theorem dot3_cross_target (w1 w2 : Real) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (ax bx ay by_ az bz : Real)
    (p1 p2 p3 s r : Real) (q1 q2 q3 sQ rQ : Real)
    (hp1 : RoundsW w1 p1 (ax * bx)) (hp2 : RoundsW w1 p2 (ay * by_))
    (hp3 : RoundsW w1 p3 (az * bz))
    (hs : RoundsW w1 s (p2 + p3)) (hr : RoundsW w1 r (p1 + s))
    (hq1 : RoundsW w2 q1 (ax * bx)) (hq2 : RoundsW w2 q2 (ay * by_))
    (hq3 : RoundsW w2 q3 (az * bz))
    (hsQ : RoundsW w2 sQ (q2 + q3)) (hrQ : RoundsW w2 rQ (q1 + sQ)) :
    abs (r - rQ)
      ≤ ((1 + w1) * (1 + w1) * (1 + w1) - 1)
          * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz)))
        + ((1 + w2) * (1 + w2) * (1 + w2) - 1)
          * (abs (ax * bx) + (abs (ay * by_) + abs (az * bz))) :=
  cross_target
    (dot3_fwd_error w1 hw1 ax bx ay by_ az bz p1 p2 p3 s r hp1 hp2 hp3 hs hr)
    (dot3_fwd_error w2 hw2 ax bx ay by_ az bz q1 q2 q3 sQ rQ hq1 hq2 hq3 hsQ hrQ)

/-- **`dot4` conditioned forward-error — the `mat4` cell *and* `quat` component
kernel.** A 4-term sum of products `a₁·b₁ + a₂·b₂ + a₃·b₃ + a₄·b₄`, evaluated as
a *balanced* tree `⌊⌊p₁+p₂⌉ + ⌊p₃+p₄⌉⌉`. This is exactly the shape of both a
`mul_mat4` cell (row · column) and a `mul_quat` Hamilton-product component
(the latter mixed-sign — handled transparently, since the bound is on
magnitudes). Two `dot2`s plus a symmetric combine: because both halves have the
same depth, the bound is `(1+w)³ − 1` with **no slack** (the combine is an
equality, not an inequality). -/
theorem dot4_fwd_error (w : Real) (hw0 : 0 ≤ w)
    (a1 b1 a2 b2 a3 b3 a4 b4 : Real)
    (p1 p2 p3 p4 s1 s2 r : Real)
    (hp1 : RoundsW w p1 (a1 * b1)) (hp2 : RoundsW w p2 (a2 * b2))
    (hp3 : RoundsW w p3 (a3 * b3)) (hp4 : RoundsW w p4 (a4 * b4))
    (hs1 : RoundsW w s1 (p1 + p2)) (hs2 : RoundsW w s2 (p3 + p4))
    (hr : RoundsW w r (s1 + s2)) :
    abs (r - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4)))
      ≤ ((1 + w) * (1 + w) * (1 + w) - 1)
          * ((abs (a1 * b1) + abs (a2 * b2)) + (abs (a3 * b3) + abs (a4 * b4))) := by
  have hs1E : abs (s1 - (a1 * b1 + a2 * b2))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (a1 * b1) + abs (a2 * b2)) :=
    dot2_fwd_error w hw0 a1 b1 a2 b2 p1 p2 s1 hp1 hp2 hs1
  have hs2E : abs (s2 - (a3 * b3 + a4 * b4))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (a3 * b3) + abs (a4 * b4)) :=
    dot2_fwd_error w hw0 a3 b3 a4 b4 p3 p4 s2 hp3 hp4 hs2
  have hs1B : abs s1 ≤ (1 + w) * (1 + w) * (abs (a1 * b1) + abs (a2 * b2)) := by
    have htri : abs s1 ≤ abs (a1 * b1 + a2 * b2) + abs (s1 - (a1 * b1 + a2 * b2)) := by
      have e1 : s1 = (a1 * b1 + a2 * b2) + (s1 - (a1 * b1 + a2 * b2)) := by
        mach_mpoly [s1, a1, b1, a2, b2]
      have ha := abs_add (a1 * b1 + a2 * b2) (s1 - (a1 * b1 + a2 * b2))
      rw [← e1] at ha; exact ha
    have step := add_le_add_both (abs_add (a1 * b1) (a2 * b2)) hs1E
    have e : (abs (a1 * b1) + abs (a2 * b2))
          + ((1 + w) * (1 + w) - 1) * (abs (a1 * b1) + abs (a2 * b2))
        = (1 + w) * (1 + w) * (abs (a1 * b1) + abs (a2 * b2)) := by
      mach_mpoly [w, abs (a1 * b1), abs (a2 * b2)]
    rw [e] at step; exact le_trans htri step
  have hs2B : abs s2 ≤ (1 + w) * (1 + w) * (abs (a3 * b3) + abs (a4 * b4)) := by
    have htri : abs s2 ≤ abs (a3 * b3 + a4 * b4) + abs (s2 - (a3 * b3 + a4 * b4)) := by
      have e1 : s2 = (a3 * b3 + a4 * b4) + (s2 - (a3 * b3 + a4 * b4)) := by
        mach_mpoly [s2, a3, b3, a4, b4]
      have ha := abs_add (a3 * b3 + a4 * b4) (s2 - (a3 * b3 + a4 * b4))
      rw [← e1] at ha; exact ha
    have step := add_le_add_both (abs_add (a3 * b3) (a4 * b4)) hs2E
    have e : (abs (a3 * b3) + abs (a4 * b4))
          + ((1 + w) * (1 + w) - 1) * (abs (a3 * b3) + abs (a4 * b4))
        = (1 + w) * (1 + w) * (abs (a3 * b3) + abs (a4 * b4)) := by
      mach_mpoly [w, abs (a3 * b3), abs (a4 * b4)]
    rw [e] at step; exact le_trans htri step
  have hsplit : abs (r - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4)))
      ≤ abs (r - (s1 + s2))
        + abs ((s1 + s2) - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4))) := by
    have e : r - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4))
        = (r - (s1 + s2)) + ((s1 + s2) - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4))) := by
      mach_mpoly [r, s1, s2, a1, b1, a2, b2, a3, b3, a4, b4]
    rw [e]; exact abs_add _ _
  have hss : abs (s1 + s2)
      ≤ (1 + w) * (1 + w) * (abs (a1 * b1) + abs (a2 * b2))
        + (1 + w) * (1 + w) * (abs (a3 * b3) + abs (a4 * b4)) :=
    le_trans (abs_add s1 s2) (add_le_add_both hs1B hs2B)
  have ht1 : abs (r - (s1 + s2))
      ≤ w * ((1 + w) * (1 + w) * (abs (a1 * b1) + abs (a2 * b2))
          + (1 + w) * (1 + w) * (abs (a3 * b3) + abs (a4 * b4))) :=
    le_trans (roundsW_abs hr) (mul_le_mul_of_nonneg_left hss hw0)
  have ht2 : abs ((s1 + s2) - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4)))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (a1 * b1) + abs (a2 * b2))
        + ((1 + w) * (1 + w) - 1) * (abs (a3 * b3) + abs (a4 * b4)) := by
    have hd : (s1 + s2) - ((a1 * b1 + a2 * b2) + (a3 * b3 + a4 * b4))
        = (s1 - (a1 * b1 + a2 * b2)) + (s2 - (a3 * b3 + a4 * b4)) := by
      mach_mpoly [s1, s2, a1, b1, a2, b2, a3, b3, a4, b4]
    rw [hd]; exact le_trans (abs_add _ _) (add_le_add_both hs1E hs2E)
  have hcomb := add_le_add_both ht1 ht2
  have efinal : w * ((1 + w) * (1 + w) * (abs (a1 * b1) + abs (a2 * b2))
            + (1 + w) * (1 + w) * (abs (a3 * b3) + abs (a4 * b4)))
          + (((1 + w) * (1 + w) - 1) * (abs (a1 * b1) + abs (a2 * b2))
            + ((1 + w) * (1 + w) - 1) * (abs (a3 * b3) + abs (a4 * b4)))
      = ((1 + w) * (1 + w) * (1 + w) - 1)
          * ((abs (a1 * b1) + abs (a2 * b2)) + (abs (a3 * b3) + abs (a4 * b4))) := by
    mach_mpoly [w, abs (a1 * b1), abs (a2 * b2), abs (a3 * b3), abs (a4 * b4)]
  rw [efinal] at hcomb
  exact le_trans hsplit hcomb

/-! ## General N-term summation — Higham's theorem, Mathlib-free

`dot2/3/4` are fixed-arity instances. This is the general sequential rounded
sum of a list, via `cond_combine` + a recursively-defined `Nat`-power (MachLib's
only `^` is the `Real^Real` analytic power). -/

/-- `Nat`-power on `Real` (monoid power). -/
noncomputable def npow : Nat → Real → Real
  | 0,     _ => 1
  | n + 1, x => x * npow n x

theorem npow_succ (n : Nat) (x : Real) : npow (n + 1) x = x * npow n x := rfl

theorem one_le_npow (x : Real) (hx : 1 ≤ x) : ∀ n : Nat, (1 : Real) ≤ npow n x
  | 0 => le_refl 1
  | n + 1 => by
      have ih := one_le_npow x hx n
      have h0x : (0 : Real) ≤ x := le_trans (le_of_lt one_pos) hx
      have hm := mul_le_mul_of_nonneg_left ih h0x
      rw [show x * (1 : Real) = x by mach_ring] at hm
      rw [npow_succ]; exact le_trans hx hm

/-- Exact sum of a list. -/
noncomputable def lsum : List Real → Real
  | [] => 0
  | x :: xs => x + lsum xs

/-- Sum of absolute values — the conditioning quantity. -/
noncomputable def labs : List Real → Real
  | [] => 0
  | x :: xs => abs x + labs xs

theorem labs_nonneg : ∀ xs : List Real, (0 : Real) ≤ labs xs
  | [] => by show (0 : Real) ≤ 0; exact le_refl 0
  | x :: xs => by
      show (0 : Real) ≤ abs x + labs xs
      exact add_nonneg (abs_nonneg x) (labs_nonneg xs)

theorem abs_lsum_le_labs : ∀ xs : List Real, abs (lsum xs) ≤ labs xs
  | [] => by show abs (0 : Real) ≤ 0; rw [abs_zero]; exact le_refl 0
  | x :: xs => by
      show abs (x + lsum xs) ≤ abs x + labs xs
      exact le_trans (abs_add x (lsum xs)) (add_le_add_left (abs_lsum_le_labs xs) (abs x))

/-- Sequential rounded sum: `s = ⌊x₁ + ⌊x₂ + … + ⌊xₙ + 0⌉⌉⌉`. -/
inductive RSum (w : Real) : List Real → Real → Prop
  | nil : RSum w [] 0
  | cons (x : Real) (xs : List Real) (acc r : Real) :
      RSum w xs acc → RoundsW w r (x + acc) → RSum w (x :: xs) r

/-- The per-step algebraic slack (over fresh vars, so `mach_mpoly`'s atom parser
doesn't trip on the `induction`-bound `x`): `target − bound = (1+w)(P−1)·ax`. -/
theorem sum_step_slack (w ax L P : Real) :
    ((1 + w) * P - 1) * (ax + L)
      - (w * ((ax + 0) + (L + (P - 1) * L)) + (0 + (P - 1) * L))
    = (1 + w) * (P - 1) * ax := by mach_mpoly [w, ax, L, P]

/-- **General N-term conditioned summation (Higham).** Any sequential rounded
sum of a list is within `(1+w)ⁿ − 1` of the exact sum, against the conditioning
quantity `Σ|xᵢ|` (`n = length`). `dot2/3/4` are the arity-fixed instances. The
proof is one `cond_combine` per element — the building block, iterated. -/
theorem RSum_bound (w : Real) (hw0 : 0 ≤ w) :
    ∀ {xs : List Real} {s : Real}, RSum w xs s →
      abs (s - lsum xs) ≤ (npow xs.length (1 + w) - 1) * labs xs := by
  intro xs s h
  induction h with
  | nil =>
      show abs ((0 : Real) - 0) ≤ ((1 : Real) - 1) * 0
      rw [show (0 : Real) - 0 = 0 by mach_ring, abs_zero, show ((1 : Real) - 1) * 0 = 0 by mach_ring]
      exact le_refl 0
  | cons x xs acc r h_xs h_r ih =>
      show abs (r - (x + lsum xs))
          ≤ (npow (xs.length + 1) (1 + w) - 1) * (abs x + labs xs)
      have hxx : abs (x - x) ≤ 0 := by
        rw [show x - x = 0 by mach_ring, abs_zero]; exact le_refl 0
      have hcc := cond_combine w hw0 hxx ih h_r
      -- hcc : abs (r - (x + lsum xs))
      --        ≤ w*((|x|+0)+(|lsum xs|+E)) + (0+E),  E = (npow k (1+w) - 1)*labs xs
      refine le_trans hcc ?_
      have hP : (1 : Real) ≤ npow xs.length (1 + w) :=
        one_le_npow (1 + w) (le_add_of_nonneg_right hw0) xs.length
      have hL : (0 : Real) ≤ labs xs := labs_nonneg xs
      have hls : abs (lsum xs) ≤ labs xs := abs_lsum_le_labs xs
      have hax : (0 : Real) ≤ abs x := abs_nonneg x
      -- step 1: replace |lsum xs| by labs xs (monotone, w ≥ 0)
      have hinner : abs (lsum xs) + (npow xs.length (1 + w) - 1) * labs xs
          ≤ labs xs + (npow xs.length (1 + w) - 1) * labs xs :=
        add_le_add_both hls (le_refl _)
      have hmono :
          w * ((abs x + 0) + (abs (lsum xs) + (npow xs.length (1 + w) - 1) * labs xs))
              + (0 + (npow xs.length (1 + w) - 1) * labs xs)
            ≤ w * ((abs x + 0) + (labs xs + (npow xs.length (1 + w) - 1) * labs xs))
              + (0 + (npow xs.length (1 + w) - 1) * labs xs) :=
        add_le_add_both
          (mul_le_mul_of_nonneg_left (add_le_add_left hinner (abs x + 0)) hw0)
          (le_refl _)
      refine le_trans hmono ?_
      -- step 2: equality slack = (1+w)(P-1)|x| ≥ 0
      rw [npow_succ]
      have hslack : (0 : Real)
          ≤ (1 + w) * (npow xs.length (1 + w) - 1) * abs x :=
        mul_nonneg (mul_nonneg (zero_le_one_add hw0) (sub_nonneg_of_le hP)) hax
      have hdiff := sum_step_slack w (abs x) (labs xs) (npow xs.length (1 + w))
      have hd : (0 : Real)
          ≤ ((1 + w) * npow xs.length (1 + w) - 1) * (abs x + labs xs)
            - (w * ((abs x + 0) + (labs xs + (npow xs.length (1 + w) - 1) * labs xs))
              + (0 + (npow xs.length (1 + w) - 1) * labs xs)) := by
        rw [hdiff]; exact hslack
      exact le_of_sub_nonneg hd

/-! ## Concrete precisions — IEEE binary64 and binary32

The theorems above are parameterized over the unit roundoff `w`. Here it
becomes an actual number: `f64_u = 2⁻⁵³`, `f32_u = 2⁻²⁴`, each a real
`1 / 2ⁿ` with a machine-checked `0 ≤ · ≤ 1`, so every `dotN`/`lerp`/
`cross_target`/`RSum_bound` instantiates at a real target precision. -/

theorem one_le_two : (1 : Real) ≤ 1 + 1 := le_add_of_nonneg_right (le_of_lt one_pos)

theorem npow_two_pos (n : Nat) : (0 : Real) < npow n (1 + 1) :=
  lt_of_lt_of_le zero_lt_one_ax (one_le_npow (1 + 1) one_le_two n)

/-- IEEE binary64 unit roundoff, `2⁻⁵³`. -/
noncomputable def f64_u : Real := 1 / npow 53 (1 + 1)
/-- IEEE binary32 unit roundoff, `2⁻²⁴`. -/
noncomputable def f32_u : Real := 1 / npow 24 (1 + 1)

theorem f64_u_nonneg : (0 : Real) ≤ f64_u := one_div_nonneg_of_pos (npow_two_pos 53)
theorem f64_u_le_one : f64_u ≤ 1 :=
  div_le_one_of_le_of_pos (npow_two_pos 53) (one_le_npow (1 + 1) one_le_two 53)
theorem f32_u_nonneg : (0 : Real) ≤ f32_u := one_div_nonneg_of_pos (npow_two_pos 24)
theorem f32_u_le_one : f32_u ≤ 1 :=
  div_le_one_of_le_of_pos (npow_two_pos 24) (one_le_npow (1 + 1) one_le_two 24)

/-- **`dot2` at IEEE binary64** — the abstract bound made concrete: the actual
Rust-`f64` evaluation of `a·b + c·d` is within `(1+2⁻⁵³)² − 1` of the exact
value (≈ 2·2⁻⁵³). One specialization of `dot2_fwd_error`; the same holds for
`f32_u = 2⁻²⁴` and for every other kernel above. -/
theorem dot2_f64 (a b c d : Real) (p1 p2 r : Real)
    (hp1 : RoundsW f64_u p1 (a * b)) (hp2 : RoundsW f64_u p2 (c * d))
    (hr : RoundsW f64_u r (p1 + p2)) :
    abs (r - (a * b + c * d))
      ≤ ((1 + f64_u) * (1 + f64_u) - 1) * (abs (a * b) + abs (c * d)) :=
  dot2_fwd_error f64_u f64_u_nonneg a b c d p1 p2 r hp1 hp2 hr

end MachLib.Real
