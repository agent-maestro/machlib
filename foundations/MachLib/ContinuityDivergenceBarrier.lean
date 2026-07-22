import MachLib.LogDivergenceWall

/-!
# Compression: the reusable continuity-vs-divergence barrier behind C1

Per external review: `no_tree_eq_log_positive_side_given_validon` (C1) never actually used the EML
tree or `EMLPfaffianValidOn` beyond the ONE fact they supply — continuity of `t.eval` AT the point
`0`. Everything downstream is a general fact about ANY function continuous at a point versus ANY
target unbounded approaching that point from one side. Extracted here: `no_continuousAt_eq_
unboundedBelowNearRight`, with `no_tree_eq_log_positive_side_given_validon` re-derived as a
corollary. Matches the review's own phrasing almost verbatim: "a function represented by a tree
continuous at a finite point cannot equal a target that is unbounded along a sequence converging
to that point."

This is genuinely target- and tree-agnostic — nothing here mentions `EMLTree`, `log`, or
`EMLPfaffianValidOn`. Any future non-representability argument that produces `ContinuousAt g x0`
by whatever means (not necessarily `EMLPfaffianValidOn`) and pairs it with a target unbounded near
`x0` gets this barrier for free.
-/

namespace MachLib
namespace Real

open MachLib

/-- `TARGET` is unbounded BELOW approaching `x0` from the right — the shape `log_unbounded_below`
supplies at `x0 = 0`, generalized to an arbitrary base point. -/
def UnboundedBelowNearRight (TARGET : Real → Real) (x0 : Real) : Prop :=
  ∀ M : Real, ∃ δ : Real, 0 < δ ∧ ∀ y : Real, x0 < y → y < x0 + δ → TARGET y < M

/-- **The general continuity-vs-divergence barrier.** A function `g` continuous AT `x0` cannot
equal, on any right-neighborhood of `x0` up to some `b`, a target that is unbounded below
approaching `x0` from the right. Identical mechanism to `no_tree_eq_log_positive_side_given_
validon`: continuity gives a local lower bound on `g`; unboundedness gives a point where `TARGET`
dips below that bound; `heq` forces them equal there — contradiction. -/
theorem no_continuousAt_eq_unboundedBelowNearRight
    (g : Real → Real) (x0 : Real) (hcont : ContinuousAt g x0)
    (TARGET : Real → Real) (hunbdd : UnboundedBelowNearRight TARGET x0)
    (b : Real) (hb : x0 < b)
    (heq : ∀ x : Real, x0 < x → x < b → g x = TARGET x) : False := by
  obtain ⟨δ, hδpos, hδ⟩ := bdd_below_nbhd_of_continuousAt hcont
  obtain ⟨δ', hδ'pos, hδ'⟩ := hunbdd (g x0 - 1)
  have hbx0 : 0 < b - x0 := by
    have h := add_lt_add_left hb (-x0)
    rwa [neg_add_self, show -x0 + b = b - x0 from by mach_ring] at h
  obtain ⟨M, hMpos, hMδ, hMδ', hMbx0⟩ := exists_pos_le_three δ δ' (b - x0) hδpos hδ'pos hbx0
  obtain ⟨yy, hyy0, hyyM⟩ := exists_between 0 M hMpos
  have hyyδ : yy < δ := lt_of_lt_of_le hyyM hMδ
  have hyyδ' : yy < δ' := lt_of_lt_of_le hyyM hMδ'
  have hyybx0 : yy < b - x0 := lt_of_lt_of_le hyyM hMbx0
  have hyx0 : x0 < x0 + yy := by
    have h := add_lt_add_left hyy0 x0
    rwa [add_zero] at h
  have hey : x0 + yy - x0 = yy := by
    rw [sub_def, add_assoc, add_left_comm, add_neg, add_zero]
  have habsy : abs (x0 + yy - x0) < δ := by
    rw [hey]; rwa [abs_of_nonneg (nonneg_of_pos hyy0)]
  have hyδ' : x0 + yy < x0 + δ' := add_lt_add_left hyyδ' x0
  have hyb : x0 + yy < b := by
    have h := add_lt_add_left hyybx0 x0
    rw [sub_def, add_left_comm, add_neg, add_zero] at h
    exact h
  have hlower : g x0 - 1 < g (x0 + yy) := hδ (x0 + yy) habsy
  have hupper : TARGET (x0 + yy) < g x0 - 1 := hδ' (x0 + yy) hyx0 hyδ'
  rw [heq (x0 + yy) hyx0 hyb] at hlower
  exact lt_irrefl_ax (TARGET (x0 + yy)) (lt_trans_ax hupper hlower)

/-- `Real.log`'s `UnboundedBelowNearRight` at `x0 = 0` — a one-line repackaging of the already-
proven `log_unbounded_below`. -/
private theorem log_unboundedBelowNearRight : UnboundedBelowNearRight Real.log 0 := by
  intro M
  obtain ⟨δ, hδpos, hδ⟩ := log_unbounded_below M
  refine ⟨δ, hδpos, fun y hy0 hyδ => hδ y hy0 ?_⟩
  rwa [zero_add] at hyδ

/-- **`log` as a corollary**, re-deriving `no_tree_eq_log_positive_side_given_validon` from the
general barrier — confirms the extraction is genuinely uniform, not a bigger different thing. -/
theorem no_tree_eq_log_positive_side_given_validon_via_barrier (t : EMLTree) (a b : Real)
    (ha : a < 0) (hb : 0 < b) (hvalidon : EMLPfaffianValidOn t a b)
    (heq : ∀ x : Real, 0 < x → x < b → t.eval x = Real.log x) : False :=
  no_continuousAt_eq_unboundedBelowNearRight t.eval 0
    (eml_validon_continuousAt t a b hvalidon 0 ha hb) Real.log log_unboundedBelowNearRight b hb
    heq

end Real
end MachLib
