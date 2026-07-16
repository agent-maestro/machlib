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

theorem iv_aon {t : Real} (h : t < 0) : abs t = -t := by
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

theorem iv_ltmin {a b c : Real} (h1 : c < a) (h2 : c < b) : c < min a b := by
  unfold min; split
  · exact h1
  · exact h2

theorem iv_ltmax {a b c : Real} (h1 : a < c) (h2 : b < c) : max a b < c := by
  unfold max; split
  · exact h2
  · exact h1

private theorem iv_lerefl (a : Real) : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

private theorem iv_letrans {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp h1 with h1 | h1
  · exact le_of_lt_r (lt_of_lt_of_le_r h1 h2)
  · rw [h1]; exact h2

theorem iv_ltadd (c : Real) {δ : Real} (h : 0 < δ) : c < c + δ := by
  have h2 := add_lt_add_left h c; rw [add_zero] at h2; exact h2

theorem iv_subself (c : Real) {δ : Real} (h : 0 < δ) : c - δ < c := by
  have h2 := add_lt_add_left (show -δ < 0 by
    have h3 := add_lt_add_left h (-δ); rw [add_zero, neg_add_self] at h3; exact h3) c
  rw [add_zero, ← sub_def] at h2; exact h2

/-- `x ≤ c ⟹ |x − c| = c − x`. -/
theorem iv_absub {x c : Real} (h : x ≤ c) : abs (x - c) = c - x := by
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

/-! ## Boundedness (Extreme Value Theorem, upper-bound half — from `sup_exists`)

`c = sup {x ∈ [a,b] : f bounded above on [a,x]}` — same completeness-axiom technique as
`intermediate_value`. Two facts about `c` close the proof: `c` itself is in the set (a bound on
some `[a,x₀]` with `x₀` close enough to `c`, glued to the local bound from continuity at `c`), and
`c = b` (else the local bound at `c` extends the set past `c`, contradicting `c = sup`). -/

private theorem iv_pn {v : Real} (h : v < 0) : 0 < -v := by
  have h2 := add_lt_add_left h (-v)
  rw [neg_add_self, add_zero] at h2
  exact h2

private theorem iv_le_abs_self (t : Real) : t ≤ abs t := by
  rcases lt_total t 0 with h | h | h
  · rw [iv_aon h]
    exact le_of_lt_r (lt_trans_ax h (iv_pn h))
  · rw [h, abs_of_nonneg (iv_lerefl 0)]
    exact iv_lerefl 0
  · rw [abs_of_nonneg (le_of_lt_r h)]
    exact iv_lerefl t

private theorem lt_of_abs_lt {t B : Real} (h : abs t < B) : t < B :=
  lt_of_le_of_lt_r (iv_le_abs_self t) h

/-- **Local boundedness from continuity.** A function continuous at `x` stays below `f x + 1` on
a neighborhood of `x` (the ε = 1 instance of `ContinuousAt`). -/
theorem bdd_above_nbhd_of_continuousAt {f : Real → Real} {x : Real} (hc : ContinuousAt f x) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y < f x + 1 := by
  obtain ⟨δ, hδ, hy⟩ := hc 1 zero_lt_one_ax
  refine ⟨δ, hδ, fun y hyδ => ?_⟩
  have hlt : f y - f x < 1 := lt_of_abs_lt (hy y hyδ)
  have h2 := add_lt_add_left hlt (f x)
  rwa [show f x + (f y - f x) = f y from by mach_mpoly [f x, f y]] at h2

/-- **Boundedness (Extreme Value Theorem, upper-bound half).** A function continuous at every
point of `[a,b]` is bounded above there. -/
theorem continuousAt_bddAbove_Icc (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∃ M : Real, ∀ x : Real, a ≤ x → x ≤ b → f x ≤ M := by
  have haS : (fun x => a ≤ x ∧ x ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x → f y ≤ M) a := by
    refine ⟨iv_lerefl a, hab, f a, fun y hya hy_le_a => ?_⟩
    have heq : a = y := le_antisymm hya hy_le_a
    rw [← heq]
    exact iv_lerefl (f a)
  have hne : ∃ x, (fun x => a ≤ x ∧ x ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x → f y ≤ M) x :=
    ⟨a, haS⟩
  have hbd : BoundedAbove (fun x => a ≤ x ∧ x ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x → f y ≤ M) :=
    ⟨b, fun x hx => hx.2.1⟩
  obtain ⟨c, hub, hlub⟩ := sup_exists _ hne hbd
  have hac : a ≤ c := hub a haS
  have hcb : c ≤ b := hlub b (fun x hx => hx.2.1)
  have hcont_c : ContinuousAt f c := hcont c hac hcb
  obtain ⟨δ, hδ, hnbhd⟩ := bdd_above_nbhd_of_continuousAt hcont_c
  -- Step 1: `c` itself is in the set — glue a bound on `[a, x₀]` (some `x₀ > c - δ`, which must
  -- exist since `c - δ` is too small to be an upper bound) to the local bound at `c`.
  have hex : ∃ x0, (a ≤ x0 ∧ x0 ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x0 → f y ≤ M) ∧ c - δ < x0 := by
    refine Classical.byContradiction (fun hcon => ?_)
    have hbound : ∀ x, (a ≤ x ∧ x ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x → f y ≤ M) → x ≤ c - δ := by
      intro x hSx
      rcases lt_total (c - δ) x with h | h | h
      · exact absurd ⟨x, hSx, h⟩ hcon
      · exact le_of_eq h.symm
      · exact le_of_lt_r h
    have hle : c ≤ c - δ := hlub (c - δ) hbound
    exact lt_irrefl_ax c (lt_of_le_of_lt_r hle (iv_subself c hδ))
  obtain ⟨x0, ⟨hax0, _hx0b, M0, hM0⟩, hcδx0⟩ := hex
  have hcS : ∃ M : Real, ∀ y, a ≤ y → y ≤ c → f y ≤ M := by
    refine ⟨max M0 (f c + 1), fun y hya hyc => ?_⟩
    rcases lt_total x0 y with hxy | hxy | hxy
    · have hcδy : c - δ < y := lt_trans_ax hcδx0 hxy
      have habs : abs (y - c) < δ := by
        rw [iv_absub hyc]
        have h2 := add_lt_add_left hcδy δ
        rw [show δ + (c - δ) = c from by mach_ring, add_comm δ y] at h2
        have h3 := add_lt_add_left h2 (-y)
        rw [show -y + c = c - y from by mach_mpoly [c, y],
            show -y + (y + δ) = δ from by mach_mpoly [y, δ]] at h3
        exact h3
      exact le_of_lt_r (lt_of_lt_of_le_r (hnbhd y habs) (le_max_right M0 (f c + 1)))
    · rw [← hxy]
      exact iv_letrans (hM0 x0 hax0 (iv_lerefl x0)) (le_max_left M0 (f c + 1))
    · exact iv_letrans (hM0 y hya (le_of_lt_r hxy)) (le_max_left M0 (f c + 1))
  -- Step 2: `c = b` — else the local bound at `c` extends the set past `c`, contradicting `c = sup`.
  have hceqb : c = b := by
    rcases (le_iff_lt_or_eq c b).mp hcb with hclt | hceq
    · exfalso
      obtain ⟨M, hM⟩ := hcS
      obtain ⟨c', hcc', hc'm⟩ := exists_between c (min (c + δ) b) (iv_ltmin (iv_ltadd c hδ) hclt)
      have hc'b : c' ≤ b := le_of_lt_r (lt_of_lt_of_le_r hc'm (min_le_right _ _))
      have hc'cδ : c' < c + δ := lt_of_lt_of_le_r hc'm (min_le_left _ _)
      have hc'S : (fun x => a ≤ x ∧ x ≤ b ∧ ∃ M : Real, ∀ y, a ≤ y → y ≤ x → f y ≤ M) c' := by
        refine ⟨iv_letrans hac (le_of_lt_r hcc'), hc'b, max M (f c + 1), fun y hya hyc' => ?_⟩
        rcases lt_total c y with hcy | hcy | hcy
        · have habs : abs (y - c) < δ := by
            rw [abs_of_nonneg (le_of_lt_r (sub_pos_of_lt hcy))]
            have h2 := add_lt_add_left (lt_of_le_of_lt_r hyc' hc'cδ) (-c)
            rw [show -c + y = y - c from by mach_mpoly [c, y],
                show -c + (c + δ) = δ from by mach_mpoly [c, δ]] at h2
            exact h2
          exact le_of_lt_r (lt_of_lt_of_le_r (hnbhd y habs) (le_max_right M (f c + 1)))
        · rw [← hcy]
          exact le_of_lt_r (lt_of_lt_of_le_r (iv_ltadd (f c) zero_lt_one_ax) (le_max_right M (f c + 1)))
        · exact iv_letrans (hM y hya (le_of_lt_r hcy)) (le_max_left M (f c + 1))
      exact lt_irrefl_ax c (lt_of_lt_of_le_r hcc' (hub c' hc'S))
    · exact hceq
  obtain ⟨M, hM⟩ := hcS
  refine ⟨M, fun x hxa hxb => ?_⟩
  rw [← hceqb] at hxb
  exact hM x hxa hxb

/-! ## Infimum (reflection of `sup_exists`)

`sup_exists` gives suprema; an infimum is the negation of the supremum of the negated set
(`inf S = -sup(-S)`) — standard reflection, no new axiom. -/

def BoundedBelow (p : Real → Prop) : Prop :=
  ∃ m : Real, ∀ x : Real, p x → m ≤ x

/-- **Infimum exists**, by reflecting through `sup_exists`. -/
theorem inf_exists (p : Real → Prop) (h_nonempty : ∃ x, p x) (h_bound : BoundedBelow p) :
    ∃ s : Real,
      (∀ x, p x → s ≤ x) ∧
      (∀ s', (∀ x, p x → s' ≤ x) → s' ≤ s) := by
  obtain ⟨m, hm⟩ := h_bound
  obtain ⟨x0, hx0⟩ := h_nonempty
  have hne' : ∃ y, (fun y => p (-y)) y :=
    ⟨-x0, by show p (-(-x0)); rw [show -(-x0) = x0 from by mach_ring]; exact hx0⟩
  have hbd' : BoundedAbove (fun y => p (-y)) := by
    refine ⟨-m, fun y hy => ?_⟩
    have h2 := neg_le_neg (hm (-y) hy)
    rwa [show -(-y) = y from by mach_ring] at h2
  obtain ⟨c, hub, hlub⟩ := sup_exists (fun y => p (-y)) hne' hbd'
  refine ⟨-c, ?_, ?_⟩
  · intro x hx
    have h1 : (fun y => p (-y)) (-x) := by
      show p (-(-x)); rw [show -(-x) = x from by mach_ring]; exact hx
    have h2 := neg_le_neg (hub (-x) h1)
    rwa [show -(-x) = x from by mach_ring] at h2
  · intro s' hs'
    have hub' : ∀ y, (fun y => p (-y)) y → y ≤ -s' := by
      intro y hy
      have h2 := neg_le_neg (hs' (-y) hy)
      rwa [show -(-y) = y from by mach_ring] at h2
    have h3 := neg_le_neg (hlub (-s') hub')
    rwa [show -(-s') = s' from by mach_ring] at h3

end Real
end MachLib
