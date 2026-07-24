import MachLib.IntermediateValue
import MachLib.Forge
import MachLib.FPModel
import MachLib.TrigLipschitz
import MachLib.Linarith
import MachLib.CertcomTotalErrorFloor
import MachLib.LyapunovSafety

/-!
# Heine-Cantor: continuity on `[a,b]` is uniform

MachLib has no compactness / finite-subcover / sequential (Bolzano-Weierstrass) machinery, so the
textbook proofs of Heine-Cantor are unavailable. This file proves it anyway, via the SAME
"supremum of a locally-defined property, extend past the supremum, contradiction" technique
`IntermediateValue.lean`'s own IVT proof already uses (`c := sup{x | P holds on [a,x]}`, show `P`
extends slightly past `c` via continuity AT `c`, contradicting `c` being an upper bound of the set
unless `c = b`). No axiom is added — the whole argument is built from `sup_exists` and the ε-δ
(fully transparent) definition of `ContinuousAt`.

This unblocks Riemann integration for CONTINUOUS (not just monotone) integrands: uniform
continuity is exactly what bounds the Darboux gap `upperSum − lowerSum` uniformly across a fine
enough partition, the way monotonicity did directly in `RiemannIntegralMonotone.lean`.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — Small reusable inequality helpers -/

private theorem abs_lt_of (t B : Real) (h1 : t < B) (h2 : -t < B) : abs t < B := by
  unfold abs; split
  · exact h1
  · exact h2

private theorem sub_lt_of_lt_add (c w bound : Real) (h : c - bound < w) : c - w < bound := by
  have h2 := add_lt_add_left h (bound - w)
  rw [show bound - w + (c - bound) = c - w from by mach_mpoly [c, w, bound],
    show bound - w + w = bound from by mach_mpoly [w, bound]] at h2
  exact h2

private theorem sub_le_of_le_add (w c bound : Real) (h : w ≤ c + bound) : w - c ≤ bound := by
  have h2 := add_le_add_left h (-c)
  rw [show -c + w = w - c from by mach_mpoly [c, w],
    show -c + (c + bound) = bound from by mach_mpoly [c, bound]] at h2
  exact h2

private theorem add_lt_add_of_lt_le (a b c d : Real) (h1 : a < b) (h2 : c ≤ d) : a + c < b + d := by
  have s1 : c + a < c + b := add_lt_add_left h1 c
  rw [add_comm c a, add_comm c b] at s1
  exact lt_of_lt_of_le s1 (add_le_add_left h2 b)

private theorem half_add_half (X : Real) : X / (1 + 1) + X / (1 + 1) = X := by
  rw [← show (1 + 1) * (X / (1 + 1)) = X / (1 + 1) + X / (1 + 1) from by mach_mpoly [(X / (1 + 1) : Real)]]
  exact mul_div_cancel_left two_ne_zero

/-- Two values each within `ε/2` of a common third value are within `ε` of each other. -/
private theorem combine_fvals (fy fz fc ε : Real)
    (h1 : abs (fy - fc) < ε / (1 + 1)) (h2 : abs (fz - fc) < ε / (1 + 1)) :
    abs (fy - fz) < ε := by
  have hyz' : abs (fy - fz) ≤ abs (fy - fc) + abs (fc - fz) := by
    rw [show fy - fz = (fy - fc) + (fc - fz) from by mach_mpoly [fy, fz, fc]]
    exact abs_add (fy - fc) (fc - fz)
  have hfcz : abs (fc - fz) < ε / (1 + 1) := by rwa [abs_sub_comm] at h2
  have hsum : abs (fy - fc) + abs (fc - fz) < ε := by
    have := add_lt_add_of_lt_le (abs (fy - fc)) (ε / (1 + 1)) (abs (fc - fz)) (ε / (1 + 1))
      h1 (le_of_lt hfcz)
    rwa [half_add_half] at this
  exact lt_of_le_of_lt hyz' hsum

/-- `UCProp f a b ε x`: uniform continuity of `f` within `ε` holds on `[a,x]` (and `x ∈ [a,b]`). -/
private def UCProp (f : Real → Real) (a b ε x : Real) : Prop :=
  a ≤ x ∧ x ≤ b ∧ ∃ δ : Real, 0 < δ ∧ ∀ y z : Real, a ≤ y → y ≤ x → a ≤ z → z ≤ x →
    abs (y - z) < δ → abs (f y - f z) < ε

/-! ## §2 — Heine-Cantor -/

/-- **Heine-Cantor.** `f` continuous at every point of `[a,b]` is uniformly continuous on `[a,b]`. -/
theorem heine_cantor_uniform_continuity {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (ε : Real) (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧
      ∀ y z : Real, a ≤ y → y ≤ b → a ≤ z → z ≤ b →
        abs (y - z) < δ → abs (f y - f z) < ε := by
  have haS : UCProp f a b ε a := by
    refine ⟨le_refl a, hab, 1, one_pos, fun y z hya hyx hza hzx _ => ?_⟩
    rw [le_antisymm hyx hya, le_antisymm hzx hza, sub_self]
    show abs 0 < ε
    rwa [abs_zero]
  have hne : ∃ x, UCProp f a b ε x := ⟨a, haS⟩
  have hbdd : BoundedAbove (UCProp f a b ε) := ⟨b, fun x hx => hx.2.1⟩
  obtain ⟨c, hub, hlub⟩ := sup_exists (UCProp f a b ε) hne hbdd
  have hca : a ≤ c := hub a haS
  have hcb : c ≤ b := hlub b (fun x hx => hx.2.1)
  have hεhalf : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  obtain ⟨δc, hδc, hδcy⟩ := hcont c hca hcb (ε / (1 + 1)) hεhalf
  have hδc2 : 0 < δc / (1 + 1) := div_pos_of_pos_pos hδc two_pos
  have hx0 : ∃ x0, UCProp f a b ε x0 ∧ c - δc / (1 + 1) < x0 := by
    apply Classical.byContradiction
    intro hcon
    have hbd' : ∀ x, UCProp f a b ε x → x ≤ c - δc / (1 + 1) := by
      intro x hx
      apply Classical.byContradiction
      intro hxcon
      exact hcon ⟨x, hx, lt_of_not_le hxcon⟩
    have hle := hlub (c - δc / (1 + 1)) hbd'
    have hlt : c - δc / (1 + 1) < c := by
      have h2 := add_lt_add_left hδc2 (c - δc / (1 + 1))
      rw [add_zero, show c - δc / (1 + 1) + δc / (1 + 1) = c from by mach_mpoly [c, δc]] at h2
      exact h2
    exact lt_irrefl_ax c (lt_of_le_of_lt hle hlt)
  obtain ⟨x0, hx0S, hx0gt⟩ := hx0
  obtain ⟨hx0a, hx0b, δx0, hδx0, hδx0y⟩ := hx0S
  have hδpos : 0 < min (δc / (1 + 1)) δx0 := by
    rcases le_total_real (δc / (1 + 1)) δx0 with h | h
    · have heq : min (δc / (1 + 1)) δx0 = δc / (1 + 1) :=
        le_antisymm (min_le_left _ _) (le_min (le_refl _) h)
      rw [heq]; exact hδc2
    · have heq : min (δc / (1 + 1)) δx0 = δx0 :=
        le_antisymm (min_le_right _ _) (le_min h (le_refl _))
      rw [heq]; exact hδx0
  let δ := min (δc / (1 + 1)) δx0
  have hδled2 : δ ≤ δc / (1 + 1) := min_le_left _ _
  have hδlex0 : δ ≤ δx0 := min_le_right _ _
  have hx1c : min b (c + δc / (1 + 1)) ≤ c + δc / (1 + 1) := min_le_right _ _
  have hcx1 : c ≤ min b (c + δc / (1 + 1)) := by
    apply le_min hcb
    have h2 := add_lt_add_left hδc2 c
    rw [add_zero] at h2
    exact le_of_lt h2
  let x1 := min b (c + δc / (1 + 1))
  have hx1b : x1 ≤ b := min_le_left _ _
  have hx1a : a ≤ x1 := le_trans hca hcx1
  have hnear : ∀ w, a ≤ w → w ≤ x1 → x0 ≤ w → abs (w - c) ≤ δc / (1 + 1) := by
    intro w hwa hwx1 hwx0
    apply abs_le_of
    · exact sub_le_of_le_add w c (δc / (1 + 1)) (le_trans hwx1 hx1c)
    · show -(w - c) ≤ δc / (1 + 1)
      rw [show -(w - c) = c - w from by mach_mpoly [w, c]]
      exact le_of_lt (sub_lt_of_lt_add c w (δc / (1 + 1)) (lt_of_lt_of_le hx0gt hwx0))
  have hnear2 : ∀ v w, a ≤ v → v ≤ x1 → x0 ≤ w → w ≤ x1 → abs (v - w) < δ → abs (v - c) < δc := by
    intro v w hva hvx1 hwx0 hwx1 hvw
    have h1 : abs (w - c) ≤ δc / (1 + 1) := hnear w (le_trans hx0a hwx0) hwx1 hwx0
    have h2 : abs (v - c) ≤ abs (v - w) + abs (w - c) := by
      rw [show v - c = (v - w) + (w - c) from by mach_mpoly [v, w, c]]
      exact abs_add (v - w) (w - c)
    have h3 : abs (v - w) < δc / (1 + 1) := lt_of_lt_of_le hvw hδled2
    have h4 : abs (v - w) + abs (w - c) < δc / (1 + 1) + δc / (1 + 1) :=
      add_lt_add_of_lt_le (abs (v - w)) (δc / (1 + 1)) (abs (w - c)) (δc / (1 + 1)) h3 h1
    rw [half_add_half] at h4
    exact lt_of_le_of_lt h2 h4
  have hδcHalf : δc / (1 + 1) < δc := by
    have h5 := add_lt_add_left hδc2 (δc / (1 + 1))
    rw [add_zero, half_add_half] at h5
    exact h5
  have hx1S : UCProp f a b ε x1 := by
    refine ⟨hx1a, hx1b, δ, hδpos, ?_⟩
    intro y z hya hyx1 hza hzx1 hyz
    rcases le_total_real y x0 with hyx0 | hyx0
    · rcases le_total_real z x0 with hzx0 | hzx0
      · exact hδx0y y z hya hyx0 hza hzx0 (lt_of_lt_of_le hyz hδlex0)
      · have hzc : abs (z - c) < δc :=
          lt_of_le_of_lt (hnear z (le_trans hx0a hzx0) hzx1 hzx0) hδcHalf
        have hyc : abs (y - c) < δc := hnear2 y z hya hyx1 hzx0 hzx1 hyz
        exact combine_fvals (f y) (f z) (f c) ε (hδcy y hyc) (hδcy z hzc)
    · rcases le_total_real z x0 with hzx0 | hzx0
      · have hyc : abs (y - c) < δc :=
          lt_of_le_of_lt (hnear y (le_trans hx0a hyx0) hyx1 hyx0) hδcHalf
        have hzy : abs (z - y) < δ := by rwa [abs_sub_comm] at hyz
        have hzc : abs (z - c) < δc := hnear2 z y hza hzx1 hyx0 hyx1 hzy
        exact combine_fvals (f y) (f z) (f c) ε (hδcy y hyc) (hδcy z hzc)
      · have hyc : abs (y - c) < δc :=
          lt_of_le_of_lt (hnear y (le_trans hx0a hyx0) hyx1 hyx0) hδcHalf
        have hzc : abs (z - c) < δc :=
          lt_of_le_of_lt (hnear z (le_trans hx0a hzx0) hzx1 hzx0) hδcHalf
        exact combine_fvals (f y) (f z) (f c) ε (hδcy y hyc) (hδcy z hzc)
  have hx1lec : x1 ≤ c := hub x1 hx1S
  have hx1eqc : x1 = c := le_antisymm hx1lec hcx1
  have hceqb : c = b := by
    rcases le_total_real b (c + δc / (1 + 1)) with hbK | hKb
    · have : x1 = b := le_antisymm hx1b (le_min (le_refl b) hbK)
      rw [← hx1eqc, this]
    · have hKx1 : c + δc / (1 + 1) ≤ x1 := le_min hKb (le_refl _)
      rw [hx1eqc] at hKx1
      have h2 := add_lt_add_left hδc2 c
      rw [add_zero] at h2
      exact False.elim (lt_irrefl_ax c (lt_of_lt_of_le h2 hKx1))
  rw [hx1eqc, hceqb] at hx1S
  obtain ⟨_, _, δf, hδf, hδfy⟩ := hx1S
  exact ⟨δf, hδf, fun y z hya hyb hza hzb => hδfy y z hya hyb hza hzb⟩

end Real
end MachLib
