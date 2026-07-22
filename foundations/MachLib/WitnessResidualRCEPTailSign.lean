import MachLib.WitnessResidualTailSign
import MachLib.WitnessResidualTargetGeneric

open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

/-! # `RightChildrenEverywherePositive` trees eventually settle: the missing building block, built

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 56 closed the tail
sign stabilization route's EASY half (`B` eventually non-positive, `tailSign_eml_of_B_eventually_nonpos`)
and characterized the HARD half precisely: the `B` eventually positive case needs `A` to be more
than merely "eventually fixed-sign" — it needs `A` eventually agreeing with SOME
`RightChildrenEverywherePositive`-style representation, so the Khovanskii zero-counting machinery
can apply to it. This file builds the piece that makes that machinery usable at all:
**`RightChildrenEverywherePositive T ⟹ TailSign T.eval`** — proven completely, not assumed.

**The mechanism, worked out on paper before writing anything.** Assume, for contradiction, that a
`RightChildrenEverywherePositive` tree `T` does NOT eventually settle. Unfolding the negation
gives three facts: for every `R`, there's a point past `R` where `T.eval ≤ 0`, a point past `R`
where `T.eval ≥ 0`, and a point past `R` where `T.eval ≠ 0`. `RightChildrenEverywherePositive`
gives `EMLNoCrossingAt` EVERYWHERE (positive right children are trivially nonzero), hence
`T.eval` is differentiable everywhere (`eml_hasDerivAt_of_no_crossing`) — enough to run
`intermediate_value_of_hasDerivAt` between a `≤0` point and a `≥0` point past any `R`, producing a
GENUINE zero. Iterating this construction (`rcepZero`, via `Exists.choose` over a recursively
defined sequence) gives arbitrarily many, strictly increasing, hence DISTINCT zeros. Meanwhile
`RightChildrenEverywherePositive` also gives GLOBAL `EMLPfaffianValidOn` (no interval restriction
needed at all — the reusable fact from cont. 29), so `enc_combinedBound` applies on ANY interval
chosen AFTER the fact, with a bound `M` fixed purely by `T`'s own structure. Constructing `M + 1`
distinct zeros, all inside one interval, directly violates that bound — `omega` closes it.

**Why the interval can be chosen AFTER the zeros, not before.** Every earlier use of
`enc_combinedBound` in this arc (`no_tree_eq_target_given_validon`, etc.) needed to pick the
interval big enough BEFORE knowing where the relevant points would land, because validity there
was only available on `(0, b)` for a `b` tied to the SAME computation producing the bound.
`RightChildrenEverywherePositive` sidesteps this entirely: validity holds on `(0, b)` for
literally ANY `b`, so the zeros can be constructed FIRST (wherever the IVT process happens to put
them) and the interval built AFTERWARD to contain all of them plus one genuinely nonzero witness
point (`enc_combinedBound`'s own non-degeneracy hypothesis — needed separately from the
constructed zeros, since those are zero by definition; derived from `¬TailSign.zero`'s own
negation, the same style as the other two negated facts).

**What this does and does not close.** `rcep_tailSign` is a complete, standalone, reusable fact —
useful anywhere `RightChildrenEverywherePositive` shows up in this arc, not just for `TailSign`.
It does NOT by itself close the `B` eventually positive case of `WitnessResidualTailSign.lean`'s
own induction: that still needs the recursive "eventually agrees with an RCEP tree" construction
(building, by structural recursion, a genuinely simpler representative tree for cases where deeper
right children clamp permanently) flagged as substantial follow-on engineering in that file. This
file is the building block that construction will need to invoke once it reaches a fully
`RightChildrenEverywherePositive` tail — a real, verified piece of the eventual full closure, not
the closure itself.

`sorryAx`-free, verified via a genuinely fresh rebuild for all thirteen theorems in this file. No
`eml_pfaffian_validon_from_sin_equality` dependence — the axiom footprint matches this arc's
standard Khovanskii trusted base exactly (`IsAnalyticOnReals`/`analytic_*`/`rolle_ct`/`sup_exists`,
the `HasDerivAt` family). -/

namespace MachLib
namespace Real

theorem rcep_no_crossing :
    ∀ (T : EMLTree), RightChildrenEverywherePositive T →
      ∀ x : Real, MachLib.EMLNoCrossingAt T x := by
  intro T
  induction T with
  | const c => intro _ x; trivial
  | var => intro _ x; trivial
  | eml t1 t2 ih1 ih2 =>
    intro hT x
    obtain ⟨h1, h2, h3⟩ := hT
    exact ⟨ih1 h1 x, ih2 h2 x, ne_of_gt (h3 x)⟩

/-- Given a genuine sign change (`≤0` at `x1`, `>0` at `x2 > x1`), a `RightChildrenEverywherePositive`
tree has a zero somewhere in `[x1, x2)` — via IVT when the sign change is strict, or `x1` itself
when it's already exactly zero. -/
theorem rcep_zero_between (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (x1 x2 : Real) (hx1x2 : x1 < x2) (h1 : T.eval x1 ≤ 0) (h2 : 0 < T.eval x2) :
    ∃ z : Real, x1 ≤ z ∧ z < x2 ∧ T.eval z = 0 := by
  rcases lt_total (T.eval x1) 0 with hlt | heq | hgt
  · have hdiff : ∀ z : Real, x1 ≤ z → z ≤ x2 → ∃ f' : Real, HasDerivAt T.eval f' z :=
      fun z _ _ => eml_hasDerivAt_of_no_crossing T z (rcep_no_crossing T hT z)
    obtain ⟨c, hc1, hc2, hc3⟩ := intermediate_value_of_hasDerivAt T.eval x1 x2 hx1x2 hdiff hlt h2
    exact ⟨c, le_of_lt hc1, hc2, hc3⟩
  · exact ⟨x1, le_refl x1, hx1x2, heq⟩
  · exfalso; exact lt_irrefl_ax 0 (lt_of_lt_of_le hgt h1)

/-- Given `hnp`/`hnn` (points of each sign arbitrarily far out), there's a zero past ANY `R`. -/
theorem rcep_zero_past (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x)
    (R : Real) : ∃ z : Real, R < z ∧ T.eval z = 0 := by
  obtain ⟨x1, hx1R, hx1⟩ := hnp R
  obtain ⟨x2, hx2x1, hx2⟩ := hnn x1
  rcases lt_total (T.eval x2) 0 with hlt | heq | hgt
  · exfalso; exact lt_irrefl_ax 0 (lt_of_le_of_lt hx2 hlt)
  · exact ⟨x2, lt_trans_ax hx1R hx2x1, heq⟩
  · obtain ⟨z, hz1, hz2, hz3⟩ := rcep_zero_between T hT x1 x2 hx2x1 hx1 hgt
    exact ⟨z, lt_of_lt_of_le hx1R hz1, hz3⟩

/-- A strictly increasing sequence of zeros, one per `Nat`, past `1` (chosen instead of `0` so the
whole sequence stays `> 1`, matching the interval choice `enc_combinedBound` needs later). -/
noncomputable def rcepZero (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) : Nat → Real
  | 0 => (rcep_zero_past T hT hnp hnn 1).choose
  | (k + 1) =>
      (rcep_zero_past T hT hnp hnn (rcepZero T hT hnp hnn k)).choose

theorem rcepZero_zero_gt_one (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) :
    (1 : Real) < rcepZero T hT hnp hnn 0 :=
  (rcep_zero_past T hT hnp hnn 1).choose_spec.1

theorem rcepZero_succ_gt (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (k : Nat) :
    rcepZero T hT hnp hnn k < rcepZero T hT hnp hnn (k + 1) :=
  (rcep_zero_past T hT hnp hnn (rcepZero T hT hnp hnn k)).choose_spec.1

theorem rcepZero_strictMono (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) {i j : Nat} (hij : i < j) :
    rcepZero T hT hnp hnn i < rcepZero T hT hnp hnn j := by
  induction j with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact lt_trans_ax (ih hlt) (rcepZero_succ_gt T hT hnp hnn m)
    · have hie : i = m := by omega
      rw [hie]
      exact rcepZero_succ_gt T hT hnp hnn m

theorem rcepZero_eval_zero (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (k : Nat) :
    T.eval (rcepZero T hT hnp hnn k) = 0 := by
  cases k with
  | zero => exact (rcep_zero_past T hT hnp hnn 1).choose_spec.2
  | succ m => exact (rcep_zero_past T hT hnp hnn (rcepZero T hT hnp hnn m)).choose_spec.2

theorem rcepZeros_list_nodup (T : EMLTree) (hT : RightChildrenEverywherePositive T)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (M : Nat) :
    ((List.range (M + 1)).map (rcepZero T hT hnp hnn)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (rcepZero T hT hnp hnn))
  exact (List.nodup_range (M + 1)).map (rcepZero T hT hnp hnn)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := rcepZero_strictMono T hT hnp hnn hlt
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := rcepZero_strictMono T hT hnp hnn hlt2
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

theorem rcep_hnp_of_not_tailSign (T : EMLTree) (hcon : ¬ TailSign T.eval) :
    ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0 := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.pos ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, by
    rcases lt_total (T.eval x) 0 with h | h | h
    · exact le_of_lt h
    · exact le_of_eq h
    · exact absurd h hcon3⟩

theorem rcep_hnn_of_not_tailSign (T : EMLTree) (hcon : ¬ TailSign T.eval) :
    ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.neg ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, by
    rcases lt_total (T.eval x) 0 with h | h | h
    · exact absurd h hcon3
    · exact le_of_eq h.symm
    · exact le_of_lt h⟩

theorem rcep_hnz_of_not_tailSign (T : EMLTree) (hcon : ¬ TailSign T.eval) :
    ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≠ 0 := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.zero ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, hcon3⟩

/-- `x < x + c` for `c > 0`, a small helper used repeatedly below to avoid re-deriving the same
`add_lt_add_left`/`add_zero` shuffle each time. -/
theorem lt_add_pos (x c : Real) (hc : 0 < c) : x < x + c := by
  have h := add_lt_add_left hc x
  rwa [add_zero] at h

/-- **The payoff**: any `RightChildrenEverywherePositive` tree eventually settles into one fixed
sign. Contradiction route: assuming not, construct arbitrarily many distinct zeros via IVT
(`rcepZero`) plus one genuinely nonzero witness (`rcep_hnz_of_not_tailSign` — needed for
`enc_combinedBound`'s own non-degeneracy hypothesis, distinct from the zeros themselves), pick an
interval containing `M + 1` of the zeros AND the nonzero witness (`M` from `combinedBoundE`, fixed
by `T`'s own structure, chosen BEFORE any of these points — the interval is chosen AFTER, since
validity holds unconditionally for any interval here), and violate `enc_combinedBound`'s own
bound. -/
theorem rcep_tailSign (T : EMLTree) (hT : RightChildrenEverywherePositive T) :
    TailSign T.eval := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hnp := rcep_hnp_of_not_tailSign T hcon
  have hnn := rcep_hnn_of_not_tailSign T hcon
  have hnz := rcep_hnz_of_not_tailSign T hcon
  have hvalidon : ∀ b : Real, 0 < b → EMLPfaffianValidOn T 0 b :=
    fun b _ => EMLPfaffianValidOn_of_right_children_everywhere_positive hT 0 b
  let p := (enc T emlEmptyChain).2
  let M := combinedBoundE (len T 0) (enc T emlEmptyChain).1 (encTags T emlEmptyChain ()) p
  let z := rcepZero T hT hnp hnn
  have hz0gt1 : (1 : Real) < z 0 := rcepZero_zero_gt_one T hT hnp hnn
  have hzmono : ∀ i j : Nat, i < j → z i < z j := fun i j hij => rcepZero_strictMono T hT hnp hnn hij
  have hzMgt1 : (1 : Real) < z M := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0]; exact hz0gt1
    · exact lt_trans_ax hz0gt1 (hzmono 0 M hMpos)
  obtain ⟨w, hw1, hwne⟩ := hnz 1
  -- inner interval (1, b) with b past BOTH z M and w
  let b : Real := z M + w + 1
  have hzM_lt_b : z M < b := by
    have hw1pos : (0 : Real) < w + 1 :=
      lt_trans_ax (lt_trans_ax zero_lt_one_ax hw1) (lt_add_pos w 1 zero_lt_one_ax)
    have := lt_add_pos (z M) (w + 1) hw1pos
    rwa [← add_assoc] at this
  have hw_lt_b : w < b := by
    have hzM1pos : (0 : Real) < z M + 1 :=
      lt_trans_ax (lt_trans_ax zero_lt_one_ax hzMgt1) (lt_add_pos (z M) 1 zero_lt_one_ax)
    have hstep : w < w + (z M + 1) := lt_add_pos w (z M + 1) hzM1pos
    have hcomm : w + (z M + 1) = z M + w + 1 := by mach_ring
    rwa [hcomm] at hstep
  have hinner_ab : (1 : Real) < b := lt_trans_ax hzMgt1 hzM_lt_b
  have houter_lt : b < b + 1 := lt_add_pos b 1 zero_lt_one_ax
  have hbouter_pos : (0 : Real) < b + 1 :=
    lt_trans_ax (lt_trans_ax zero_lt_one_ax hinner_ab) houter_lt
  have hvalidon_here : EMLPfaffianValidOn T 0 (b + 1) := hvalidon (b + 1) hbouter_pos
  have hlogPos : LogArgPosOn T (Icc 1 b) :=
    logArgPosOn_Icc_of_validOn T 0 (b + 1) 1 b zero_lt_one_ax houter_lt hvalidon_here
  have hne : ∃ v : Real, (1 : Real) < v ∧ v < b ∧
      (pfaffianChainFn (enc T emlEmptyChain).1 p).eval v ≠ 0 := by
    refine ⟨w, hw1, hw_lt_b, ?_⟩
    show MultiPoly.eval p w ((enc T emlEmptyChain).1.chainValues w) ≠ 0
    have heval : MultiPoly.eval p w ((enc T emlEmptyChain).1.chainValues w)
        = T.eval w := enc_eval T emlEmptyChain w
    rw [heval]; exact hwne
  have hbound := enc_combinedBound T emlEmptyChain () 1 b hinner_ab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p hne
  let zeros : List Real := (List.range (M + 1)).map z
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ v ∈ zeros,
      (1 : Real) < v ∧ v < b ∧
        (pfaffianChainFn (enc T emlEmptyChain).1 p).eval v = 0 := by
    intro v hv
    simp only [zeros, List.mem_map, List.mem_range] at hv
    obtain ⟨i, hilt, hveq⟩ := hv
    refine ⟨?_, ?_, ?_⟩
    · rw [← hveq]
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · rw [hi0]; exact hz0gt1
      · exact lt_trans_ax hz0gt1 (hzmono 0 i hipos)
    · rw [← hveq]
      rcases Nat.lt_or_ge i M with hlt | hge
      · exact lt_trans_ax (hzmono i M hlt) hzM_lt_b
      · have hiM : i = M := by omega
        rw [hiM]; exact hzM_lt_b
    · rw [← hveq]
      show MultiPoly.eval p (z i) ((enc T emlEmptyChain).1.chainValues (z i)) = 0
      have heval : MultiPoly.eval p (z i) ((enc T emlEmptyChain).1.chainValues (z i))
          = T.eval (z i) := enc_eval T emlEmptyChain (z i)
      rw [heval]; exact rcepZero_eval_zero T hT hnp hnn i
  have hzeros_nodup : zeros.Nodup := rcepZeros_list_nodup T hT hnp hnn M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end Real
end MachLib
