import MachLib.IntermediateValue
import MachLib.Forge

/-!
# Extreme Value Theorem — attainment (Track C, item C9)

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Both external reviews
converged on "prove the general periodic-target barrier" as the natural next frontier: does
`no_tree_eq_target_of_not_tailSign` (`WitnessResidualContinuousTargetMetaLemma.lean`) already cover
EVERY nonconstant continuous periodic function for free, via `L := inf(f)`? Checked directly
(2026-07-22, "NEXT OBJECTIVES" entry): the ARGUMENT is right, but it needs the infimum to be
ATTAINED at a specific point, not merely a bound. `IntermediateValue.lean` already has boundedness
(`continuousAt_bddAbove_Icc`, upper-bound half of EVT) but not attainment — a genuinely separate
piece of analysis, confirmed by reading `continuousAt_bddAbove_Icc`'s own proof (cont. 75) before
attempting anything.

**The mechanism.** The classical `1/(M − f)` trick: suppose the least upper bound `L` of `f` on
`[a,b]` (built via `sup_exists`, same completeness axiom `intermediate_value`/`continuousAt_
bddAbove_Icc` already use) is never attained — i.e. `f x < L` everywhere on `[a,b]`. Then
`g x := 1/(L − f x)` is well-defined and continuous on ALL of `[a,b]` (§1 builds this continuity
composite from scratch — no generic `ContinuousAt` combinator library existed in this codebase
before this file). `g` is then itself bounded above by `continuousAt_bddAbove_Icc`, say by `K > 0`;
unwinding `g x ≤ K` gives `f x ≤ L − 1/K` for every `x`, so `L − 1/K` is ALSO an upper bound for
`f` — contradicting that `L` is the LEAST one, since `1/K > 0`. So the "never attained" assumption
is false: `f` attains `L` at some `c ∈ [a,b]`. §2 builds this for the max; §3 mirrors it for the min
via negation (`f`'s min is `-f`'s max, negated back).

`sorryAx`-free, no new axioms — everything here is derived from `sup_exists`/`ContinuousAt`, both
already load-bearing in `IntermediateValue.lean`.
-/

namespace MachLib
namespace Real

open MachLib

/-! ## §1 — Continuity of the reciprocal `1/(M − f)`, where `f` stays below `M` -/

private theorem lt_add_eps_nbhd_of_continuousAt {f : Real → Real} {x : Real} (hc : ContinuousAt f x)
    {ε : Real} (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y < f x + ε := by
  obtain ⟨δ, hδ, hy⟩ := hc ε hε
  refine ⟨δ, hδ, fun y hyδ => ?_⟩
  have hlt : f y - f x < ε := lt_of_abs_lt (hy y hyδ)
  have h2 := add_lt_add_left hlt (f x)
  rwa [show f x + (f y - f x) = f y from by mach_mpoly [f x, f y]] at h2

private theorem lt_of_sub_pos_local {a b : Real} (h : 0 < b - a) : a < b := by
  have h2 := add_lt_add_left h a
  have e1 : a + 0 = a := add_zero _
  have e2 : a + (b - a) = b := by mach_mpoly [a, b]
  rwa [e1, e2] at h2

private theorem div_lt_of_lt_mul_local {a b c : Real} (h : a < c * b) (hb : 0 < b) : a / b < c := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 < 1 / b := one_div_pos_of_pos hb
  have h2 : a * (1 / b) < c * b * (1 / b) := mul_lt_mul_of_pos_right h hbinv
  rw [mul_assoc c b (1 / b), mul_inv b hbne, mul_one_ax] at h2
  rwa [div_def a b hbne]

private theorem le_div_of_le_mul_local {a b c : Real} (h : a ≤ c * b) (hb : 0 < b) : a / b ≤ c := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 < 1 / b := one_div_pos_of_pos hb
  have h2 : a * (1 / b) ≤ c * b * (1 / b) := mul_le_mul_of_nonneg_right h (le_of_lt hbinv)
  rw [mul_assoc c b (1 / b), mul_inv b hbne, mul_one_ax] at h2
  rwa [div_def a b hbne]

private theorem abs_div_pos_local {a b : Real} (hb : 0 < b) : abs (a / b) = abs a / b := by
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [div_def a b hbne, abs_mul, abs_of_nonneg (le_of_lt (one_div_pos_of_pos hb)),
      div_def (abs a) b hbne]

private theorem div_mul_cancel_local {a b : Real} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_def a b hb, mul_assoc, mul_comm (1 / b) b, mul_inv b hb, mul_one_ax]

private theorem eq_div_of_mul_eq_local {x z k : Real} (hk : k ≠ 0) (h : x * k = z) : x = z / k := by
  rw [← h, mul_comm x k]
  exact (mul_div_cancel_left' hk).symm

private theorem dsd_ring_local (X Y Z : Real) : (X - Y) * Z = X * Z - Y * Z := by
  mach_mpoly [X, Y, Z]

private theorem div_sub_div_local {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - c * b) / (b * d) := by
  apply eq_div_of_mul_eq_local (mul_ne_zero hb hd)
  rw [dsd_ring_local (a / b) (c / d) (b * d),
      show a / b * (b * d) = a * d from by rw [← mul_assoc, div_mul_cancel_local hb],
      show c / d * (b * d) = c * b from by rw [mul_comm b d, ← mul_assoc, div_mul_cancel_local hd]]

private theorem mul_le_mul_local {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) : a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_right hab hc) (mul_le_mul_of_nonneg_left hcd (le_trans ha hab))

private theorem le_of_mul_le_mul_right_pos_local {a b c : Real} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  have h2 := mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hc))
  rw [mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax,
      mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax] at h2
  exact h2

private theorem div_le_div_iff_local {a b c d : Real} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have hbd : (0 : Real) < b * d := mul_pos hb hd
  have e1 : a / b * (b * d) = a * d := by rw [← mul_assoc, div_mul_cancel_local (ne_of_gt hb)]
  have e2 : c / d * (b * d) = c * b := by
    rw [mul_comm b d, ← mul_assoc, div_mul_cancel_local (ne_of_gt hd)]
  constructor
  · intro h
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hbd)
    rw [e1, e2] at h2; exact h2
  · intro h
    have key : a / b * (b * d) ≤ c / d * (b * d) := by rw [e1, e2]; exact h
    exact le_of_mul_le_mul_right_pos_local key hbd

private theorem div_le_div_pos_local {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) : a / d ≤ b / c := by
  have hdpos : 0 < d := lt_of_lt_of_le hc hcd
  rw [div_le_div_iff_local hdpos hc]
  exact mul_le_mul_local ha hab (le_of_lt hc) hcd

/-- Pure arithmetic identity, stated with fresh top-level parameters so `mach_mpoly` can close it
directly (the call sites below bind `m`/`y` inside a tactic proof, where `mach_mpoly` chokes on
raw atoms — see `TACTIC_NOTES.md`). -/
private theorem evt_shift1 (M m Fx0 : Real) : Fx0 + (M - Fx0 - m) = M - m := by
  mach_mpoly [M, m, Fx0]

private theorem evt_shift2 (M Fy Fx0 : Real) : (1 : Real) * (M - Fx0) - 1 * (M - Fy) = Fy - Fx0 := by
  mach_mpoly [M, Fy, Fx0]

/-- **Reciprocal continuity.** `x ↦ 1/(M − f x)` is continuous at `x0`, given `f` continuous at
`x0` and `f x0 < M` (so the denominator is positive there). Standard `ε`-`δ` estimate via the
identity `1/A − 1/B = (B−A)/(A·B)`: `exists_between` supplies a margin `m` strictly between `0`
and `M − f x0`; near `x0` (radius `δ1`, from continuity), the denominator `M − f y` stays above
`m`, which turns the numerator's closeness (radius `δ2`, target `ε·m²`) into the quotient's. -/
theorem continuousAt_inv_sub_of_lt {f : Real → Real} {x0 M : Real}
    (hc : ContinuousAt f x0) (hlt : f x0 < M) :
    ContinuousAt (fun y => 1 / (M - f y)) x0 := by
  have hd0pos : 0 < M - f x0 := sub_pos_of_lt hlt
  obtain ⟨m, hm0, hmd0⟩ := exists_between 0 (M - f x0) hd0pos
  have hεpos : 0 < (M - f x0) - m := sub_pos_of_lt hmd0
  obtain ⟨δ1, hδ1, hnbhd1⟩ := lt_add_eps_nbhd_of_continuousAt hc hεpos
  intro ε hε
  have hmm_pos : 0 < m * m := mul_pos hm0 hm0
  have hεmm_pos : 0 < ε * (m * m) := mul_pos hε hmm_pos
  obtain ⟨δ2, hδ2, hnbhd2⟩ := hc (ε * (m * m)) hεmm_pos
  refine ⟨min δ1 δ2, iv_ltmin hδ1 hδ2, fun y hy => ?_⟩
  have hy1 : abs (y - x0) < δ1 := lt_of_lt_of_le_r hy (min_le_left δ1 δ2)
  have hy2 : abs (y - x0) < δ2 := lt_of_lt_of_le_r hy (min_le_right δ1 δ2)
  have hfy_lt : f y < M - m := by
    have h := hnbhd1 y hy1
    have heq1 : f x0 + ((M - f x0) - m) = M - m := evt_shift1 M m (f x0)
    rwa [heq1] at h
  have hMy_gt_m : m < M - f y := by
    have h0 : 0 < (M - m) - f y := sub_pos_of_lt hfy_lt
    have h1 : (M - m) - f y = (M - f y) - m := by mach_ring
    rw [h1] at h0
    exact lt_of_sub_pos_local h0
  have hMx0_gt_m : m < M - f x0 := hmd0
  have hyden_pos : 0 < M - f y := lt_trans_ax hm0 hMy_gt_m
  have hx0den_pos : 0 < M - f x0 := lt_trans_ax hm0 hMx0_gt_m
  have hprod_pos : 0 < (M - f y) * (M - f x0) := mul_pos hyden_pos hx0den_pos
  show abs (1 / (M - f y) - 1 / (M - f x0)) < ε
  have hsub : 1 / (M - f y) - 1 / (M - f x0)
      = (1 * (M - f x0) - 1 * (M - f y)) / ((M - f y) * (M - f x0)) :=
    div_sub_div_local (ne_of_gt hyden_pos) (ne_of_gt hx0den_pos)
  have hnum : (1 : Real) * (M - f x0) - 1 * (M - f y) = f y - f x0 := evt_shift2 M (f y) (f x0)
  have heq2 : 1 / (M - f y) - 1 / (M - f x0) = (f y - f x0) / ((M - f y) * (M - f x0)) := by
    rw [hsub, hnum]
  rw [heq2, abs_div_pos_local hprod_pos]
  have hmm_le : m * m ≤ (M - f y) * (M - f x0) :=
    mul_le_mul_local (le_of_lt hm0) (le_of_lt hMy_gt_m) (le_of_lt hm0) (le_of_lt hMx0_gt_m)
  have hstep : abs (f y - f x0) / ((M - f y) * (M - f x0)) ≤ abs (f y - f x0) / (m * m) :=
    div_le_div_pos_local (abs_nonneg _) (le_refl _) hmm_pos hmm_le
  have hfinal : abs (f y - f x0) / (m * m) < ε :=
    div_lt_of_lt_mul_local (hnbhd2 y hy2) hmm_pos
  exact lt_of_le_of_lt_r hstep hfinal

/-! ## §2 — Extreme Value Theorem: max-attainment -/

private theorem neg_of_pos_local {v : Real} (h : 0 < v) : -v < 0 := by
  have h2 := add_lt_add_left h (-v)
  rw [add_zero, neg_add_self] at h2
  exact h2

private theorem evt_upper_shift (L Fx K : Real) (h : 1 / K ≤ L - Fx) : Fx ≤ L - 1 / K := by
  have h4 := add_le_add_left h Fx
  have e4 : Fx + (L - Fx) = L := by mach_mpoly [Fx, L]
  rw [e4] at h4
  have h5 := add_le_add_left h4 (-(1 / K))
  have e5a : -(1 / K) + (Fx + 1 / K) = Fx := by mach_mpoly [Fx, (1 : Real) / K]
  have e5b : -(1 / K) + L = L - 1 / K := by mach_mpoly [L, (1 : Real) / K]
  rwa [e5a, e5b] at h5

private theorem evt_shift3 (L K : Real) : -L + (L - 1 / K) = -(1 / K) := by
  mach_mpoly [L, (1 : Real) / K]

/-- **Extreme Value Theorem, max-attainment.** A function continuous on `[a,b]` attains its
supremum at some point of `[a,b]` — not just bounded (`continuousAt_bddAbove_Icc`), but the bound
is realized. Classical `1/(L−f)` argument: `L := sup` of `f`'s image on `[a,b]` (via `sup_exists`,
nonempty from `f a`, bounded via `continuousAt_bddAbove_Icc`). If `L` were never attained, `g :=
1/(L−f)` would be continuous everywhere on `[a,b]` (§1), hence bounded above by some `K > 0`
(itself via `continuousAt_bddAbove_Icc`); unwinding `g x ≤ K` gives `f x ≤ L − 1/K` for every `x`,
making `L − 1/K` a SMALLER upper bound than the least one `L` — contradiction. -/
theorem continuousAt_attains_max_Icc (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∃ c : Real, a ≤ c ∧ c ≤ b ∧ ∀ x : Real, a ≤ x → x ≤ b → f x ≤ f c := by
  obtain ⟨M0, hM0⟩ := continuousAt_bddAbove_Icc f a b hab hcont
  have hne : ∃ y : Real, ∃ x : Real, a ≤ x ∧ x ≤ b ∧ f x = y := ⟨f a, a, le_refl a, hab, rfl⟩
  have hbdd : BoundedAbove (fun y => ∃ x : Real, a ≤ x ∧ x ≤ b ∧ f x = y) := by
    refine ⟨M0, fun y hy => ?_⟩
    obtain ⟨x, hxa, hxb, hxy⟩ := hy
    rw [← hxy]; exact hM0 x hxa hxb
  obtain ⟨L, hub, hlub⟩ := sup_exists (fun y => ∃ x : Real, a ≤ x ∧ x ≤ b ∧ f x = y) hne hbdd
  have hfle : ∀ x : Real, a ≤ x → x ≤ b → f x ≤ L := fun x hxa hxb => hub (f x) ⟨x, hxa, hxb, rfl⟩
  have hattained : ∃ c : Real, a ≤ c ∧ c ≤ b ∧ f c = L := by
    refine Classical.byContradiction (fun hcon => ?_)
    have hstrict : ∀ x : Real, a ≤ x → x ≤ b → f x < L := by
      intro x hxa hxb
      rcases (le_iff_lt_or_eq (f x) L).mp (hfle x hxa hxb) with h | h
      · exact h
      · exact absurd ⟨x, hxa, hxb, h⟩ hcon
    have hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun y => 1 / (L - f y)) z :=
      fun z hza hzb => continuousAt_inv_sub_of_lt (hcont z hza hzb) (hstrict z hza hzb)
    obtain ⟨K, hK⟩ := continuousAt_bddAbove_Icc (fun y => 1 / (L - f y)) a b hab hcontg
    have hgapos : 0 < 1 / (L - f a) :=
      one_div_pos_of_pos (sub_pos_of_lt (hstrict a (le_refl a) hab))
    have hKpos : 0 < K := lt_of_lt_of_le_r hgapos (hK a (le_refl a) hab)
    have hupper : ∀ x : Real, a ≤ x → x ≤ b → f x ≤ L - 1 / K := by
      intro x hxa hxb
      have hgxK : 1 / (L - f x) ≤ K := hK x hxa hxb
      have hLfx_pos : 0 < L - f x := sub_pos_of_lt (hstrict x hxa hxb)
      have h1 : (1 : Real) ≤ K * (L - f x) := by
        have h2 : (1 / (L - f x)) * (L - f x) ≤ K * (L - f x) :=
          mul_le_mul_of_nonneg_right hgxK (le_of_lt hLfx_pos)
        rwa [div_mul_cancel_local (ne_of_gt hLfx_pos)] at h2
      have h1' : (1 : Real) ≤ (L - f x) * K := by rwa [mul_comm K (L - f x)] at h1
      have h3 : 1 / K ≤ L - f x := le_div_of_le_mul_local h1' hKpos
      exact evt_upper_shift L (f x) K h3
    have hLbound : L ≤ L - 1 / K := by
      refine hlub (L - 1 / K) (fun y hy => ?_)
      obtain ⟨x, hxa, hxb, hxy⟩ := hy
      rw [← hxy]; exact hupper x hxa hxb
    have hKrecip_pos : 0 < 1 / K := one_div_pos_of_pos hKpos
    have h6 := add_le_add_left hLbound (-L)
    rw [neg_add_self, evt_shift3 L K] at h6
    exact lt_irrefl_ax 0 (lt_of_le_of_lt_r h6 (neg_of_pos_local hKrecip_pos))
  obtain ⟨c, hca, hcb, hcL⟩ := hattained
  exact ⟨c, hca, hcb, fun x hxa hxb => hcL ▸ hfle x hxa hxb⟩

/-! ## §3 — Extreme Value Theorem: min-attainment, via negation -/

private theorem abs_neg_local (t : Real) : abs (-t) = abs t := by
  rcases lt_total t 0 with h | h | h
  · have hpos : 0 < -t := by
      have h2 := add_lt_add_left h (-t); rw [add_zero, neg_add_self] at h2; exact h2
    rw [abs_of_nonneg (le_of_lt_r hpos), iv_aon h]
  · rw [h, show -(0 : Real) = 0 from by mach_ring]
  · rw [iv_aon (neg_of_pos_local h), abs_of_nonneg (le_of_lt_r h), show -(-t) = t from by mach_ring]

private theorem continuousAt_neg_local (f : Real → Real) (x : Real) (hf : ContinuousAt f x) :
    ContinuousAt (fun y => -f y) x := by
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have e : (fun y => -f y) y - (fun y => -f y) x = -(f y - f x) := by
    show -f y - -f x = -(f y - f x)
    mach_ring
  rw [e, abs_neg_local]
  exact hδprop y hy

private theorem le_of_neg_le_neg_local {a b : Real} (h : -b ≤ -a) : a ≤ b := by
  have h2 := neg_le_neg h
  rwa [show -(-a) = a from by mach_ring, show -(-b) = b from by mach_ring] at h2

/-- **Extreme Value Theorem, min-attainment.** Mirror of `continuousAt_attains_max_Icc` via
`f`'s min `=` `-f`'s max, negated back. -/
theorem continuousAt_attains_min_Icc (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∃ c : Real, a ≤ c ∧ c ≤ b ∧ ∀ x : Real, a ≤ x → x ≤ b → f c ≤ f x := by
  have hcontn : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun y => -f y) z :=
    fun z hza hzb => continuousAt_neg_local f z (hcont z hza hzb)
  obtain ⟨c, hca, hcb, hmax⟩ := continuousAt_attains_max_Icc (fun y => -f y) a b hab hcontn
  refine ⟨c, hca, hcb, fun x hxa hxb => ?_⟩
  have h : (fun y => -f y) x ≤ (fun y => -f y) c := hmax x hxa hxb
  exact le_of_neg_le_neg_local h

end Real
end MachLib
