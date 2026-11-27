import MachLib.BivariateDeriv

/-!
# The implicit-function axioms need a continuous curve: two refutations (2026-10-27)

Until 2026-10-27 `hasDerivAt_implicit` and `hasDerivAt_implicit_local` asked nothing of the curve `yc` but the
curve identity. So `yc` could jump from one solution branch of `f = 0` to another, and the axiom still gave it a
derivative. This module keeps the old statements as propositions and refutes each from the trusted axioms and
the `HasDerivAt2` rules, which Mathlib's `HasFDerivAt` satisfies (`monogate-lean` checks it). The restated
axioms take `ContinuousAt yc x`. The step function below is not continuous at its jump, so it does not
refute them.

* `implicit_without_continuity_inconsistent`: the old axiom gives `False` (and
  `implicit_local_without_continuity_inconsistent` the old local form, which restricts to it). With `f a b = b (b − 1)` and `yc` the
  step from `0` to `1` at `0`, the identity holds everywhere and `fᵧ = 2 yc − 1 = ±1`, so `yc' = 0` at every
  point. The mean value theorem on `[−1, 0]` then says `yc 0 − yc (−1) = 0`, that is `1 = 0`.
* `old_curve_count_false`: the old `khovanskii_rolle_count_curve` statement is false, not merely unproved. With
  the same `f`, `g a b = a − b` and the step at `1`, the Jacobian `fₓ gᵧ − fᵧ gₓ = −fᵧ` never vanishes, so
  `N = 0`, while `g` along the curve vanishes at `0` and at `1`: two zeros against a bound of one. Every
  theorem that took the old curve count's hypotheses therefore had to gain one, not only the axiom.

Neither file in this pair is a specimen of the NEW statements; the instance modules (`TwoExpCurveValidation`,
`TwoExpNonlinearCurveInstance`, `TwoExpGlobalSumIntersection`, `TwoExpBranchCurveInstance`) discharge their
continuity hypotheses at explicit curves.
-/

namespace MachLib
namespace Real
namespace BivariateImplicitControls

open Classical

/-- The statement of `hasDerivAt_implicit` before 2026-10-27: no continuity hypothesis on `yc`. -/
def OldImplicitStatement : Prop :=
  ∀ (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x : Real),
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → (∀ s : Real, f s (yc s) = 0) → HasDerivAt yc (-fx / fy) x

/-- The statement of `hasDerivAt_implicit_local` before 2026-10-27: the identity on `(p, q) ∋ x`, no continuity. -/
def OldImplicitLocalStatement : Prop :=
  ∀ (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x p q : Real), p < x → x < q →
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → (∀ s : Real, p < s → s < q → f s (yc s) = 0) →
    HasDerivAt yc (-fx / fy) x

/-- The statement of `TwoExp.khovanskii_rolle_count_curve` before 2026-10-27, written out. -/
def OldCurveCountStatement : Prop :=
  ∀ (f g : Real → Real → Real) (fx fy gx gy yc : Real → Real) (a b : Real), a < b →
    (∀ z : Real, a < z → z < b → HasDerivAt2 f (fx z) (fy z) z (yc z)) →
    (∀ z : Real, a < z → z < b → HasDerivAt2 g (gx z) (gy z) z (yc z)) →
    (∀ z : Real, a < z → z < b → fy z ≠ 0) →
    (∀ s : Real, f s (yc s) = 0) →
    ∀ N : Nat, (∀ zeros_J : List Real, zeros_J.Nodup →
        (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) → zeros_J.length ≤ N) →
    ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) → zeros_g.length ≤ N + 1

/-- The step at `t`: `0` below `t`, `1` from `t` on. Both values are roots of `b ↦ b (b − 1)`. -/
noncomputable def step (t s : Real) : Real := if s < t then 0 else 1

private theorem step_root (t s : Real) : step t s * (step t s - 1) = 0 := by
  unfold step
  split
  · rw [zero_mul]
  · rw [sub_self, mul_zero]

/-- The partials of `b (b − 1)` as the `HasDerivAt2` rules build them. -/
private theorem hd2_quad (x y : Real) : HasDerivAt2 (fun _ b : Real => b * (b - 1))
    (0 * (y - 1) + y * (0 - 0)) (1 * (y - 1) + y * (1 - 0)) x y :=
  HasDerivAt2_mul (fun _ b => b) (fun _ b => b - 1) 0 1 (0 - 0) (1 - 0) x y
    (HasDerivAt2_projY x y)
    (HasDerivAt2_sub (fun _ b => b) (fun _ _ => 1) 0 1 0 0 x y
      (HasDerivAt2_projY x y) (HasDerivAt2_const 1 x y))

private theorem neg_one_ne_zero_c : -(1 : Real) ≠ 0 := by
  intro h
  have e : -(-(1 : Real)) = 1 := by mach_ring
  have h1 := congrArg (fun t => -t) h
  rw [e, neg_zero] at h1
  exact zero_ne_one_ax h1.symm

/-- `fᵧ = 2 y − 1` is `−1` or `1` on the step, never `0`. -/
private theorem fy_ne_zero (t s : Real) : 1 * (step t s - 1) + step t s * (1 - 0) ≠ 0 := by
  unfold step
  split
  · have e : 1 * ((0 : Real) - 1) + 0 * (1 - 0) = -1 := by mach_ring
    rw [e]
    exact neg_one_ne_zero_c
  · have e : 1 * ((1 : Real) - 1) + 1 * (1 - 0) = 1 := by mach_ring
    rw [e]
    exact fun h => zero_ne_one_ax h.symm

private theorem neg_one_lt_zero_c : -(1 : Real) < 0 := by
  have h := add_lt_add_left zero_lt_one_ax (-(1 : Real))
  rw [add_zero, neg_add_self] at h
  exact h

/-- **The old implicit-function axiom is inconsistent with the trusted axioms and the `HasDerivAt2` rules.** -/
theorem implicit_without_continuity_inconsistent (h : OldImplicitStatement) : False := by
  have hderiv : ∀ s : Real, HasDerivAt (step 0) 0 s := by
    intro s
    have hd := h (fun _ b : Real => b * (b - 1))
      (0 * (step 0 s - 1) + step 0 s * (0 - 0)) (1 * (step 0 s - 1) + step 0 s * (1 - 0))
      (step 0) s (hd2_quad s (step 0 s)) (fy_ne_zero 0 s) (step_root 0)
    have hfx : 0 * (step 0 s - 1) + step 0 s * (0 - 0) = 0 := by mach_ring
    rw [hfx, neg_zero, div_def 0 _ (fy_ne_zero 0 s), zero_mul] at hd
    exact hd
  obtain ⟨c, f', _, _, hc, hmvt⟩ :=
    mean_value_theorem_ct (step 0) (-1) 0 neg_one_lt_zero_c (fun c _ _ => ⟨0, hderiv c⟩)
  have hf' : f' = 0 := HasDerivAt_unique (step 0) f' 0 c hc (hderiv c)
  have h0 : step 0 0 = 1 := by
    unfold step
    rw [if_neg (lt_irrefl_ax 0)]
  have hm1 : step 0 (-1) = 0 := by
    unfold step
    rw [if_pos neg_one_lt_zero_c]
  rw [h0, hm1, hf', zero_mul] at hmvt
  have e : (1 : Real) - 0 = 1 := by mach_ring
  rw [e] at hmvt
  exact zero_ne_one_ax hmvt.symm

/-- **The old local form is inconsistent too**: on `(x − 1, x + 1)` it gives the old global form. -/
theorem implicit_local_without_continuity_inconsistent (h : OldImplicitLocalStatement) : False := by
  apply implicit_without_continuity_inconsistent
  intro f fx fy yc x h2 hfy hid
  have hlt : x < x + 1 := by
    have v := add_lt_add_left zero_lt_one_ax x
    rw [add_zero] at v
    exact v
  have hgt : x + -1 < x := by
    have v := add_lt_add_left neg_one_lt_zero_c x
    rw [add_zero] at v
    exact v
  exact h f fx fy yc x (x + -1) (x + 1) hgt hlt h2 hfy (fun s _ _ => hid s)

/-- **The old curve count is false.** On `(−1, 2)`, `g a b = a − b` along the step at `1` vanishes at `0` and at
`1`, while the Jacobian against `f a b = b (b − 1)` never vanishes. -/
theorem old_curve_count_false (h : OldCurveCountStatement) : False := by
  have one_lt_two : (1 : Real) < 1 + 1 := by
    have v := add_lt_add_left zero_lt_one_ax (1 : Real)
    rw [add_zero] at v
    exact v
  have zero_lt_two : (0 : Real) < 1 + 1 := lt_trans_ax zero_lt_one_ax one_lt_two
  have hg2 : ∀ z : Real, -1 < z → z < 1 + 1 →
      HasDerivAt2 (fun a b : Real => a - b) (1 - 0) (0 - 1) z (step 1 z) := fun z _ _ =>
    HasDerivAt2_sub (fun a _ => a) (fun _ b => b) 1 0 0 1 z (step 1 z)
      (HasDerivAt2_projX z (step 1 z)) (HasDerivAt2_projY z (step 1 z))
  have hJ : ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, -1 < z ∧ z < 1 + 1 ∧
        (0 * (step 1 z - 1) + step 1 z * (0 - 0)) * (0 - 1)
          - (1 * (step 1 z - 1) + step 1 z * (1 - 0)) * (1 - 0) = 0) →
      zeros_J.length ≤ 0 := by
    intro zs _ hzs
    cases zs with
    | nil => exact Nat.le_refl 0
    | cons z _ =>
      exfalso
      obtain ⟨_, _, hz⟩ := hzs z List.mem_cons_self
      have e : (0 * (step 1 z - 1) + step 1 z * (0 - 0)) * (0 - 1)
          - (1 * (step 1 z - 1) + step 1 z * (1 - 0)) * (1 - 0)
          = -(1 * (step 1 z - 1) + step 1 z * (1 - 0)) := by mach_ring
      rw [e] at hz
      apply fy_ne_zero 1 z
      have hz' := congrArg (fun t => -t) hz
      have e2 : -(-(1 * (step 1 z - 1) + step 1 z * (1 - 0))) = 1 * (step 1 z - 1) + step 1 z * (1 - 0) := by
        mach_ring
      rw [e2, neg_zero] at hz'
      exact hz'
  have hstep0 : step 1 0 = 0 := by
    unfold step
    rw [if_pos zero_lt_one_ax]
  have hstep1 : step 1 1 = 1 := by
    unfold step
    rw [if_neg (lt_irrefl_ax 1)]
  have hzeros : ∀ z ∈ [(0 : Real), 1], -1 < z ∧ z < 1 + 1 ∧ (fun a b : Real => a - b) z (step 1 z) = 0 := by
    intro z hz
    rcases List.mem_cons.mp hz with h0 | h1
    · rw [h0]
      refine ⟨neg_one_lt_zero_c, zero_lt_two, ?_⟩
      show (0 : Real) - step 1 0 = 0
      rw [hstep0, sub_self]
    · rw [List.mem_singleton.mp h1]
      refine ⟨lt_trans_ax neg_one_lt_zero_c zero_lt_one_ax, one_lt_two, ?_⟩
      show (1 : Real) - step 1 1 = 0
      rw [hstep1, sub_self]
  have hnodup : [(0 : Real), 1].Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
    intro hm
    exact zero_ne_one_ax (List.mem_singleton.mp hm)
  have hlen := h (fun _ b : Real => b * (b - 1)) (fun a b : Real => a - b)
    (fun z => 0 * (step 1 z - 1) + step 1 z * (0 - 0)) (fun z => 1 * (step 1 z - 1) + step 1 z * (1 - 0))
    (fun _ => 1 - 0) (fun _ => 0 - 1) (step 1) (-1) (1 + 1)
    (lt_trans_ax neg_one_lt_zero_c zero_lt_two)
    (fun z _ _ => hd2_quad z (step 1 z)) hg2 (fun z _ _ => fy_ne_zero 1 z) (step_root 1)
    0 hJ [(0 : Real), 1] hnodup hzeros
  exact absurd hlen (by decide)

end BivariateImplicitControls
end Real
end MachLib
