import MachLib.EMLPfaffian
import MachLib.Forge
import MachLib.AnalyticFiniteZerosReal
import MachLib.Lemmas

/-!
# The log-divergence wall: no valid EML tree equals `log` near a point it's valid across

Track C, item C1 (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`, "NEXT OBJECTIVES" section). Cheapest
and most independent of the Track C proposals — deliberately a DIFFERENT obstruction type than
every prior result in the Option D arc. `TailSign` (the mechanism behind `sin`/`nestedTarget`)
counts sign changes; this counts nothing. It observes that `EMLPfaffianValidOn t a b` with `a < 0 <
b` forces `t.eval` to be well-behaved (differentiable, hence continuous) AT `x = 0` itself — a single
finite value — while `Real.log x → -∞` as `x → 0⁺`. A function with a finite limit at `0` cannot
coincide, on any neighborhood of `0⁺`, with one that diverges there. No zero-counting, no Khovanskii
chain, no TailSign machinery.

**Relationship to prior work, checked before writing anything.** `EMLPfaffian.lean`'s own docstring
(the "Sin-equality forces validity" section) documents an EARLIER, HARDER investigation from the
same file: propagating validity/regularity DOWN from a tree's root into arbitrarily nested interior
subtrees, in order to prove `EMLPfaffianValidOn` FROM a `t.eval = sin` hypothesis. That investigation
is now moot (cont. 65 discharged the axiom vacuously — no tree equals `sin` at all) and, separately,
was never closed (the flagged circularity: bounding `exp(s1.eval) - log(s2.eval)` doesn't bound
`s1.eval`/`s2.eval` individually). **This file does not touch that circularity.** It runs the
OPPOSITE direction: START from validity (given, not derived) and conclude non-representability of
`log` — the same shape as every closed Option D result (`no_tree_eq_sin_unconditional` also starts
from nothing and concludes non-representability), just via a different mechanism, and for a target
(`log`, near a point where its argument's own sign is exactly what `EMLPfaffianValidOn`'s recursive
positivity clause is already about) where that mechanism is unusually cheap.

Also checked and unrelated: two OLDER, MUCH heavier arcs referenced in agent memory
(`project_log_hard_fixedD_pivot`, `project_log_g0_analytic_discharge`, both dated 2026-07-08,
predating Option D) retire a *different* axiom (`PfaffianFunction.zero_count_bound_classical`, the
general classical Khovanskii zero-count bound) via a full Pfaffian-chain Wronskian descent. `log_hard`
closed there; `exp_hard` remains open and is flagged multi-week/high-risk. Neither is needed here —
this file's argument doesn't touch zero-counting at all.
-/

namespace MachLib

open MachLib.Real

/-- **Validity gives a derivative, by structural induction — same recursive shape as
`eml_pfaffian_isvalidat_of_validon` (`EMLPfaffian.lean`), concluding `HasDerivAt` instead of
`IsValidAt`.** The derivative's exact value is never used downstream (only its existence, to invoke
`hasDerivAt_continuousAt`), so it's left existentially bound rather than tracked in closed form. -/
theorem eml_validon_hasDerivAt (t : EMLTree) (a b : Real) (hvalidon : EMLPfaffianValidOn t a b) :
    ∀ x : Real, a < x → x < b → ∃ d : Real, HasDerivAt t.eval d x := by
  intro x hxa hxb
  induction t with
  | const c => exact ⟨0, HasDerivAt_const c x⟩
  | var => exact ⟨1, HasDerivAt_id x⟩
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨hv1, hv2, hpos⟩ := hvalidon
    obtain ⟨d1, hd1⟩ := ih1 hv1
    obtain ⟨d2, hd2⟩ := ih2 hv2
    have ht2pos : 0 < t2.eval x := hpos x hxa hxb
    have hexp : HasDerivAt (fun y => Real.exp (t1.eval y)) (Real.exp (t1.eval x) * d1) x :=
      HasDerivAt_comp Real.exp t1.eval d1 (Real.exp (t1.eval x)) x hd1 (HasDerivAt_exp (t1.eval x))
    have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (1 / t2.eval x * d2) x :=
      HasDerivAt_comp Real.log t2.eval d2 (1 / t2.eval x) x hd2 (HasDerivAt_log_pos (t2.eval x) ht2pos)
    refine ⟨Real.exp (t1.eval x) * d1 - 1 / t2.eval x * d2, ?_⟩
    show HasDerivAt (fun y => Real.exp (t1.eval y) - Real.log (t2.eval y)) _ x
    exact HasDerivAt_sub _ _ _ _ x hexp hlog

/-- **Corollary: validity gives continuity**, via the codebase's own differentiable-implies-
continuous bridge (`hasDerivAt_continuousAt`, `IntermediateValue.lean`). -/
theorem eml_validon_continuousAt (t : EMLTree) (a b : Real) (hvalidon : EMLPfaffianValidOn t a b)
    (x : Real) (hxa : a < x) (hxb : x < b) : ContinuousAt t.eval x :=
  have ⟨_, hd⟩ := eml_validon_hasDerivAt t a b hvalidon x hxa hxb
  hasDerivAt_continuousAt hd

/-- A positive lower bound for three positives, via nested trichotomy — mirrors `lt_of_lt_both`
(`WitnessResidualEventualValidTailSign.lean`), same style, opposite (min, not max) direction. -/
private theorem exists_pos_le_two (p q : Real) (hp : 0 < p) (hq : 0 < q) :
    ∃ M : Real, 0 < M ∧ M ≤ p ∧ M ≤ q := by
  rcases lt_total p q with h | h | h
  · exact ⟨p, hp, le_refl p, le_of_lt h⟩
  · exact ⟨p, hp, le_refl p, h ▸ le_refl p⟩
  · exact ⟨q, hq, le_of_lt h, le_refl q⟩

private theorem exists_pos_le_three (p q r : Real) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ∃ M : Real, 0 < M ∧ M ≤ p ∧ M ≤ q ∧ M ≤ r := by
  obtain ⟨M1, hM1pos, hM1p, hM1q⟩ := exists_pos_le_two p q hp hq
  obtain ⟨M2, hM2pos, hM2M1, hM2r⟩ := exists_pos_le_two M1 r hM1pos hr
  exact ⟨M2, hM2pos, le_trans hM2M1 hM1p, le_trans hM2M1 hM1q, hM2r⟩

/-- **The wall itself.** No finite EML tree, valid on an interval containing `0` as an INTERIOR
point, equals `Real.log` throughout the positive side of that interval. Proof: continuity of
`t.eval` at `0` (from validity) gives a neighborhood on which `t.eval` stays within `1` of
`t.eval 0` — a FINITE bound. `log_unbounded_below` gives a neighborhood, approaching `0` from the
positive side, on which `Real.log` dips below `t.eval 0 - 1`. Take a point in the intersection of
both neighborhoods (and inside `(0, b)`, via `exists_pos_le_three` + `exists_between`): `t.eval`
there is `> t.eval 0 - 1` (continuity) while `Real.log` there is `< t.eval 0 - 1` (divergence) —
contradicting `heq`, which forces them equal. -/
theorem no_tree_eq_log_positive_side_given_validon (t : EMLTree) (a b : Real)
    (ha : a < 0) (hb : 0 < b) (hvalidon : EMLPfaffianValidOn t a b)
    (heq : ∀ x : Real, 0 < x → x < b → t.eval x = Real.log x) : False := by
  have hcont : ContinuousAt t.eval 0 := eml_validon_continuousAt t a b hvalidon 0 ha hb
  obtain ⟨δ, hδpos, hδ⟩ := bdd_below_nbhd_of_continuousAt hcont
  obtain ⟨δ', hδ'pos, hδ'⟩ := log_unbounded_below (t.eval 0 - 1)
  obtain ⟨M, hMpos, hMδ, hMδ', hMb⟩ := exists_pos_le_three δ δ' b hδpos hδ'pos hb
  obtain ⟨y, hy0, hyM⟩ := exists_between 0 M hMpos
  have hyδ : y < δ := lt_of_lt_of_le hyM hMδ
  have hyδ' : y < δ' := lt_of_lt_of_le hyM hMδ'
  have hyb : y < b := lt_of_lt_of_le hyM hMb
  have habsy : abs (y - 0) < δ := by
    rw [sub_zero]; rwa [abs_of_nonneg (nonneg_of_pos hy0)]
  have hlower : t.eval 0 - 1 < t.eval y := hδ y habsy
  have hupper : Real.log y < t.eval 0 - 1 := hδ' y hy0 hyδ'
  rw [heq y hy0 hyb] at hlower
  exact lt_irrefl_ax (Real.log y) (lt_trans_ax hupper hlower)
