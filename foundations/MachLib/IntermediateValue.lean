import MachLib.Rolle
import MachLib.Lemmas
import MachLib.Ring
import MachLib.AnalyticFiniteZerosReal

/-!
# Continuity + sign preservation — toward the in-model IVT (Gate 2d, IFT gate — brick 1.b.1)

Building the Intermediate Value Theorem in-model from the completeness axiom `sup_exists`. `HasDerivAt` is
an opaque axiom, so continuity is bridged by ONE fundamental, witnessable axiom `hasDerivAt_continuousAt`
(differentiable ⟹ continuous). This file provides the ε-δ `ContinuousAt`, that bridge, and the
**sign-preservation** lemmas the IVT sup-construction turns on: a continuous function positive (negative) at
a point stays positive (negative) on a neighborhood. The IVT itself (brick 1.b.2) then takes
`c = sup {x : f x ≤ 0}` and rules out `f c < 0` and `f c > 0` via these.
-/

namespace MachLib
namespace Real

/-- ε-δ continuity at a point. -/
def ContinuousAt (f : Real → Real) (x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → abs (f y - f x) < ε

/-- **Differentiable ⟹ continuous** — the one new analytic axiom (witnessable against Mathlib), bridging
the opaque `HasDerivAt` to continuity. -/
axiom hasDerivAt_continuousAt {f : Real → Real} {f' x : Real} :
    HasDerivAt f f' x → ContinuousAt f x

/-! ## abs helpers -/

private theorem iv_nnp {v : Real} (h : 0 < v) : -v < 0 := by
  have h2 := add_lt_add_left h (-v)
  rw [add_zero, neg_add_self] at h2
  exact h2

private theorem iv_aon {t : Real} (h : t < 0) : abs t = -t := by
  unfold abs
  rw [if_neg (fun hle => lt_irrefl_ax t (lt_of_lt_of_le_r h hle))]

/-- `|u − v| < v ⟹ 0 < u`: closeness within `v` of a value at distance `v` keeps `u` positive. -/
theorem pos_of_abs_sub_lt {u v : Real} (h : abs (u - v) < v) : 0 < u := by
  have hv : 0 < v := lt_of_le_of_lt_r (abs_nonneg (u - v)) h
  rcases lt_total 0 u with hu | hu | hu
  · exact hu
  · exfalso
    have hval : abs (u - v) = v := by
      rw [← hu, show (0 : Real) - v = -v from by mach_ring, iv_aon (iv_nnp hv)]
      mach_ring
    rw [hval] at h; exact lt_irrefl_ax v h
  · exfalso
    have hshift : u - v < 0 := by
      have h1 : u - v < -v := by
        have h2 := add_lt_add_left hu (-v)
        rw [show -v + u = u - v from by mach_mpoly [u, v], add_zero] at h2
        exact h2
      exact lt_trans_ax h1 (iv_nnp hv)
    rw [iv_aon hshift] at h
    have h0u : 0 < u := by
      have hnu : -u < 0 := by
        have h3 := add_lt_add_left h (-v)
        rw [show -v + -(u - v) = -u from by mach_mpoly [u, v], neg_add_self] at h3
        exact h3
      have h4 := add_lt_add_left hnu u
      rw [add_neg, add_zero] at h4
      exact h4
    exact lt_irrefl_ax u (lt_trans_ax hu h0u)

/-- **Sign preservation (positive).** A continuous function positive at `x` is positive on a neighborhood. -/
theorem pos_nbhd_of_continuousAt {f : Real → Real} {x : Real}
    (hc : ContinuousAt f x) (hpos : 0 < f x) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → 0 < f y := by
  obtain ⟨δ, hδ, hy⟩ := hc (f x) hpos
  exact ⟨δ, hδ, fun y hyδ => pos_of_abs_sub_lt (hy y hyδ)⟩

private theorem iv_an (t : Real) : abs (-t) = abs t := by
  rcases lt_total t 0 with h | h | h
  · have hpos : 0 < -t := by
      have h2 := add_lt_add_left h (-t); rw [add_zero, neg_add_self] at h2; exact h2
    rw [abs_of_nonneg (le_of_lt_r hpos), iv_aon h]
  · rw [h, show -(0 : Real) = 0 from by mach_ring]
  · rw [iv_aon (iv_nnp h), abs_of_nonneg (le_of_lt_r h), show -(-t) = t from by mach_ring]

/-- **Sign preservation (negative).** A continuous function negative at `x` is negative on a neighborhood.
Reduces to the positive case for `−f` (which is continuous). -/
theorem neg_nbhd_of_continuousAt {f : Real → Real} {x : Real}
    (hc : ContinuousAt f x) (hneg : f x < 0) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y < 0 := by
  have hpos : 0 < -f x := by
    have h2 := add_lt_add_left hneg (-f x); rw [add_zero, neg_add_self] at h2; exact h2
  have hcn : ContinuousAt (fun z => -f z) x := by
    intro ε hε
    obtain ⟨δ, hδ, hy⟩ := hc ε hε
    refine ⟨δ, hδ, fun y hyδ => ?_⟩
    rw [show -f y - -f x = -(f y - f x) from by mach_ring, iv_an]
    exact hy y hyδ
  obtain ⟨δ, hδ, hy⟩ := pos_nbhd_of_continuousAt hcn hpos
  refine ⟨δ, hδ, fun y hyδ => ?_⟩
  have h3 : 0 < -f y := hy y hyδ
  have h4 := add_lt_add_left h3 (f y)
  rw [add_zero, add_neg] at h4
  exact h4

/-! ## The Intermediate Value Theorem (from `sup_exists`) -/

private theorem iv_ltmin {a b c : Real} (h1 : c < a) (h2 : c < b) : c < min a b := by
  unfold min; split
  · exact h1
  · exact h2

private theorem iv_lerefl (a : Real) : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

private theorem iv_letrans {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp h1 with h1 | h1
  · exact le_of_lt_r (lt_of_lt_of_le_r h1 h2)
  · rw [h1]; exact h2

private theorem iv_ltadd (c : Real) {δ : Real} (h : 0 < δ) : c < c + δ := by
  have h2 := add_lt_add_left h c; rw [add_zero] at h2; exact h2

private theorem iv_subself (c : Real) {δ : Real} (h : 0 < δ) : c - δ < c := by
  have h2 := add_lt_add_left (show -δ < 0 by
    have h3 := add_lt_add_left h (-δ); rw [add_zero, neg_add_self] at h3; exact h3) c
  rw [add_zero, ← sub_def] at h2; exact h2

/-- `x ≤ c ⟹ |x − c| = c − x`. -/
private theorem iv_absub {x c : Real} (h : x ≤ c) : abs (x - c) = c - x := by
  rw [show x - c = -(c - x) from by mach_ring, iv_an]
  apply abs_of_nonneg
  rcases (le_iff_lt_or_eq x c).mp h with hlt | heq
  · exact le_of_lt_r (sub_pos_of_lt hlt)
  · rw [heq, show c - c = 0 from by mach_ring]; exact iv_lerefl 0

/-- **Intermediate Value Theorem (in-model).** A function continuous on `[a,b]` with `f a < 0 < f b` has a
zero in `(a,b)`. Proof: `c = sup {x ∈ [a,b] : f x < 0}` (exists by `sup_exists`); `f c < 0` gives a point of
the set past `c` (sign preservation), and `f c > 0` makes `c − δ` a smaller upper bound — both contradict
`c = sup`. So `f c = 0`. -/
theorem intermediate_value (f : Real → Real) (a b : Real) (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c : Real, a < c ∧ c < b ∧ f c = 0 := by
  have hne : ∃ x, (fun x => a ≤ x ∧ x ≤ b ∧ f x < 0) x :=
    ⟨a, iv_lerefl a, le_of_lt_r hab, hfa⟩
  have hbd : BoundedAbove (fun x => a ≤ x ∧ x ≤ b ∧ f x < 0) := ⟨b, fun x hx => hx.2.1⟩
  obtain ⟨c, hub, hlub⟩ := sup_exists (fun x => a ≤ x ∧ x ≤ b ∧ f x < 0) hne hbd
  have hac : a ≤ c := hub a ⟨iv_lerefl a, le_of_lt_r hab, hfa⟩
  have hcb : c ≤ b := hlub b (fun x hx => hx.2.1)
  have hcont_c : ContinuousAt f c := hcont c hac hcb
  have hfc : f c = 0 := by
    rcases lt_total (f c) 0 with hlt | heq | hgt
    · exfalso
      have hcltb : c < b := by
        rcases (le_iff_lt_or_eq c b).mp hcb with h | h
        · exact h
        · exfalso; rw [h] at hlt; exact lt_irrefl_ax 0 (lt_trans_ax hfb hlt)
      obtain ⟨δ, hδ, hnbhd⟩ := neg_nbhd_of_continuousAt hcont_c hlt
      obtain ⟨x, hcx, hxm⟩ := exists_between c (min (c + δ) b) (iv_ltmin (iv_ltadd c hδ) hcltb)
      have hxb : x ≤ b := le_of_lt_r (lt_of_lt_of_le_r hxm (min_le_right _ _))
      have hxcδ : x < c + δ := lt_of_lt_of_le_r hxm (min_le_left _ _)
      have habs : abs (x - c) < δ := by
        rw [abs_of_nonneg (le_of_lt_r (sub_pos_of_lt hcx))]
        have h2 := add_lt_add_left hxcδ (-c)
        rw [show -c + x = x - c from by mach_mpoly [c, x], show -c + (c + δ) = δ from by mach_mpoly [c, δ]]
          at h2
        exact h2
      exact lt_irrefl_ax c
        (lt_of_lt_of_le_r hcx (hub x ⟨iv_letrans hac (le_of_lt_r hcx), hxb, hnbhd x habs⟩))
    · exact heq
    · exfalso
      obtain ⟨δ, hδ, hnbhd⟩ := pos_nbhd_of_continuousAt hcont_c hgt
      have hubδ : ∀ x, (fun x => a ≤ x ∧ x ≤ b ∧ f x < 0) x → x ≤ c - δ := by
        intro x hSx
        rcases lt_total (c - δ) x with h | h | h
        · exfalso
          have hxc : x ≤ c := hub x hSx
          have habs : abs (x - c) < δ := by
            rw [iv_absub hxc]
            have h2 := add_lt_add_left h δ
            rw [show δ + (c - δ) = c from by mach_mpoly [c, δ], show δ + x = x + δ from by mach_mpoly [x, δ]]
              at h2
            have h3 := add_lt_add_left h2 (-x)
            rw [show -x + c = c - x from by mach_mpoly [c, x], show -x + (x + δ) = δ from by mach_mpoly [x, δ]]
              at h3
            exact h3
          exact lt_irrefl_ax 0 (lt_trans_ax (hnbhd x habs) hSx.2.2)
        · exact (le_iff_lt_or_eq x (c - δ)).mpr (Or.inr h.symm)
        · exact le_of_lt_r h
      exact lt_irrefl_ax c (lt_of_le_of_lt_r (hlub (c - δ) hubδ) (iv_subself c hδ))
  have haltc : a < c := by
    rcases (le_iff_lt_or_eq a c).mp hac with h | h
    · exact h
    · exfalso; rw [h] at hfa; rw [hfc] at hfa; exact lt_irrefl_ax 0 hfa
  have hcltb : c < b := by
    rcases (le_iff_lt_or_eq c b).mp hcb with h | h
    · exact h
    · exfalso; rw [← h] at hfb; rw [hfc] at hfb; exact lt_irrefl_ax 0 hfb
  exact ⟨c, haltc, hcltb, hfc⟩

/-- **IVT for a differentiable function.** The form the Khovanskii parametrization needs: differentiability
on `[a,b]` gives continuity (`hasDerivAt_continuousAt`), so a sign change forces a zero. -/
theorem intermediate_value_of_hasDerivAt (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ z : Real, a ≤ z → z ≤ b → ∃ f' : Real, HasDerivAt f f' z)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c : Real, a < c ∧ c < b ∧ f c = 0 :=
  intermediate_value f a b hab
    (fun z hza hzb => (hdiff z hza hzb).elim (fun _ hf' => hasDerivAt_continuousAt hf')) hfa hfb

end Real
end MachLib
