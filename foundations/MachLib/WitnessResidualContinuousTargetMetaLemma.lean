import MachLib.WitnessResidualRecurringTargetMetaLemma

/-!
# The stronger meta-lemma: no finite EML tree equals any continuous target with no `TailSign`

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 70 extracted
`no_tree_eq_recurring_target_fully_unconditional`, parametrized by an EXPLICIT `Nat`-indexed
recurring-zero family `Z` and recurring-witness family `W` — exactly what `nestedTarget cs`
supplies in closed form. Both external reviews of that round also named a STRICTLY more general
form: instead of requiring an explicit, closed-form zero family, require only that `TARGET` is
CONTINUOUS and has no `TailSign` relative to some level `L` (`¬TailSign (fun x => TARGET x - L)`)
— exactly the shape `rcep_tailSign`/`evalid_tailSign` (cont. 57-58) already use for EML trees,
but never built for an ARBITRARY continuous function. This file builds it.

**What changes from the explicit-family version.** Instead of a given `Z : Nat → Real`, the zero
sequence is CONSTRUCTED via the Intermediate Value Theorem (`intermediate_value`, plain
`ContinuousAt`-based — no derivative needed, unlike `rcep_zero_between`'s EML-tree version, which
needed `HasDerivAt` via tree structure). `¬TailSign (fun x => TARGET x - L)` unfolds into exactly
the three "arbitrarily far out" facts `rcep_hnp_of_not_tailSign`/`rcep_hnn_of_not_tailSign`/
`rcep_hnz_of_not_tailSign` already derive — checked directly, their proofs never touch the EML
tree structure at all, only treat `T.eval` as an opaque function, so they generalize to an
arbitrary `f : Real → Real` with ZERO changes beyond the signature.

**Payoff.** `no_tree_eq_target_of_not_tailSign` — no finite EML tree equals `TARGET`, given only
`TARGET`'s continuity and `¬TailSign (TARGET - L)` for some `L`. This SUBSUMES `no_tree_eq_
recurring_target_fully_unconditional` (an explicit zero family trivially gives `¬TailSign`) and,
via it, `no_tree_eq_sin_unconditional`/`no_tree_eq_nestedTarget_fully_unconditional` — though
re-deriving those AS instances of this file is not attempted here (their existing, more direct
proofs stay as the primary route; this file's value is in reaching targets that DON'T have an
explicit closed-form zero family, which the earlier form couldn't touch at all).
-/

open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

namespace MachLib
namespace Real

/-- Pure `Real`-arithmetic identity, proven STANDALONE (no `Real → Real`-typed variable in
context) — `mach_ring` fails to close this exact identity when a function-typed variable like
`f : Real → Real` sits in the local context alongside it, even though it's irrelevant to the goal
(reproduced directly, isolated: the same statement closes fine with only `Real` variables in
scope, and fails the moment an unrelated `f : Real → Real` is added). Proven here, then APPLIED
below rather than inlining `mach_ring` into the polluted context. -/
private theorem sub_sub_cancel_shift (u v c : Real) : u - c - (v - c) = u - v := by
  mach_mpoly [u, v, c]

/-- `ContinuousAt (fun y => f y - c) x` from `ContinuousAt f x` — the constant cancels in the
`|Δf|` bound, so the SAME `δ` witnesses continuity of the shifted function. -/
theorem continuousAt_sub_const {f : Real → Real} {x : Real} (hf : ContinuousAt f x) (c : Real) :
    ContinuousAt (fun y => f y - c) x := by
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h := hδprop y hy
  have e : (fun y => f y - c) y - (fun y => f y - c) x = f y - f x := by
    show (f y - c) - (f x - c) = f y - f x
    exact sub_sub_cancel_shift (f y) (f x) c
  rw [e]
  exact h

/-- `¬TailSign f` gives arbitrarily-far-out non-positive points — the SAME proof
`rcep_hnp_of_not_tailSign` uses for `T.eval`, generalized: it never touched the tree structure,
only treated its argument as an opaque function. -/
theorem hnp_of_not_tailSign (f : Real → Real) (hcon : ¬ TailSign f) :
    ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0 := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.pos ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, by
    rcases lt_total (f x) 0 with h | h | h
    · exact le_of_lt h
    · exact le_of_eq h
    · exact absurd h hcon3⟩

theorem hnn_of_not_tailSign (f : Real → Real) (hcon : ¬ TailSign f) :
    ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.neg ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, by
    rcases lt_total (f x) 0 with h | h | h
    · exact absurd h hcon3
    · exact le_of_eq h.symm
    · exact le_of_lt h⟩

theorem hnz_of_not_tailSign (f : Real → Real) (hcon : ¬ TailSign f) :
    ∀ R : Real, ∃ x : Real, R < x ∧ f x ≠ 0 := by
  intro R
  refine Classical.byContradiction (fun hcon2 => ?_)
  apply hcon
  refine TailSign.zero ⟨R, fun x hx => ?_⟩
  refine Classical.byContradiction (fun hcon3 => ?_)
  exact hcon2 ⟨x, hx, hcon3⟩

/-- **The IVT-based zero construction, for an ARBITRARY continuous function.** Mirrors
`rcep_zero_between` exactly, but uses plain `ContinuousAt`-based `intermediate_value` instead of
`HasDerivAt`-based `intermediate_value_of_hasDerivAt` — no derivative needed, only continuity,
which is available for a raw function without any tree-structure argument. -/
theorem target_zero_between (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (x1 x2 : Real) (hx1x2 : x1 < x2) (h1 : f x1 ≤ 0) (h2 : 0 < f x2) :
    ∃ z : Real, x1 ≤ z ∧ z < x2 ∧ f z = 0 := by
  rcases lt_total (f x1) 0 with hlt | heq | hgt
  · obtain ⟨c, hc1, hc2, hc3⟩ :=
      intermediate_value f x1 x2 hx1x2 (fun z _ _ => hcont z) hlt h2
    exact ⟨c, le_of_lt hc1, hc2, hc3⟩
  · exact ⟨x1, le_refl x1, hx1x2, heq⟩
  · exfalso; exact lt_irrefl_ax 0 (lt_of_lt_of_le hgt h1)

/-- Given `hnp`/`hnn`, there's a zero of `f` past any `R`. -/
theorem target_zero_past (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x)
    (R : Real) : ∃ z : Real, R < z ∧ f z = 0 := by
  obtain ⟨x1, hx1R, hx1⟩ := hnp R
  obtain ⟨x2, hx2x1, hx2⟩ := hnn x1
  rcases lt_total (f x2) 0 with hlt | heq | hgt
  · exfalso; exact lt_irrefl_ax 0 (lt_of_le_of_lt hx2 hlt)
  · exact ⟨x2, lt_trans_ax hx1R hx2x1, heq⟩
  · obtain ⟨z, hz1, hz2, hz3⟩ := target_zero_between f hcont x1 x2 hx2x1 hx1 hgt
    exact ⟨z, lt_of_lt_of_le hx1R hz1, hz3⟩

/-- A strictly increasing sequence of zeros of `f`, one per `Nat`, past `1`. -/
noncomputable def targetZero (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) : Nat → Real
  | 0 => (target_zero_past f hcont hnp hnn 1).choose
  | (k + 1) => (target_zero_past f hcont hnp hnn (targetZero f hcont hnp hnn k)).choose

theorem targetZero_succ_gt (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) (k : Nat) :
    targetZero f hcont hnp hnn k < targetZero f hcont hnp hnn (k + 1) :=
  (target_zero_past f hcont hnp hnn (targetZero f hcont hnp hnn k)).choose_spec.1

theorem targetZero_strictMono (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) {i j : Nat} (hij : i < j) :
    targetZero f hcont hnp hnn i < targetZero f hcont hnp hnn j := by
  induction j with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact lt_trans_ax (ih hlt) (targetZero_succ_gt f hcont hnp hnn m)
    · have hie : i = m := by omega
      rw [hie]
      exact targetZero_succ_gt f hcont hnp hnn m

theorem targetZero_eval_zero (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) (k : Nat) :
    f (targetZero f hcont hnp hnn k) = 0 := by
  cases k with
  | zero => exact (target_zero_past f hcont hnp hnn 1).choose_spec.2
  | succ m => exact (target_zero_past f hcont hnp hnn (targetZero f hcont hnp hnn m)).choose_spec.2

theorem targetZeros_list_nodup (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) (M : Nat) :
    ((List.range (M + 1)).map (targetZero f hcont hnp hnn)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (targetZero f hcont hnp hnn))
  exact (List.nodup_range (M + 1)).map (targetZero f hcont hnp hnn)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := targetZero_strictMono f hcont hnp hnn hlt
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := targetZero_strictMono f hcont hnp hnn hlt2
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-- **The same construction, seeded past an ARBITRARY threshold `a0` instead of the fixed `1`.**
Needed because the final theorem must place the WHOLE zero sequence past `max(a, R)` — `a` from
`eml_eventually_valid_repr`'s validity threshold, `R` from its matching threshold — neither of
which is fixed in advance. Mirrors `evalid_zero_past`'s exact design (`WitnessResidualEventualValid
TailSign.lean`, cont. 58): bakes `a0 < z` directly into its OWN conclusion (via `lt_of_lt_both`,
picking a point exceeding both `R` and `a0`) so the recursive definition below is self-sufficient,
never needing an external "the previous zero exceeds `a0`" side-proof at the call site. -/
theorem target_zero_past_from (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x)
    (R : Real) : ∃ z : Real, R < z ∧ a0 < z ∧ f z = 0 := by
  obtain ⟨M, hRM, ha0M⟩ := lt_of_lt_both R a0
  obtain ⟨x1, hx1M, hx1⟩ := hnp M
  have hax1 : a0 < x1 := lt_trans_ax ha0M hx1M
  obtain ⟨x2, hx2x1, hx2⟩ := hnn x1
  rcases lt_total (f x2) 0 with hlt | heq | hgt
  · exfalso; exact lt_irrefl_ax 0 (lt_of_le_of_lt hx2 hlt)
  · exact ⟨x2, lt_trans_ax (lt_trans_ax hRM hx1M) hx2x1, lt_trans_ax hax1 hx2x1, heq⟩
  · obtain ⟨z, hz1, hz2, hz3⟩ := target_zero_between f hcont x1 x2 hx2x1 hx1 hgt
    exact ⟨z, lt_of_lt_of_le (lt_trans_ax hRM hx1M) hz1, lt_of_lt_of_le hax1 hz1, hz3⟩

noncomputable def targetZeroFrom (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) : Nat → Real
  | 0 => (target_zero_past_from f hcont a0 hnp hnn (a0 + 1)).choose
  | (k + 1) =>
      (target_zero_past_from f hcont a0 hnp hnn (targetZeroFrom f hcont a0 hnp hnn k)).choose

theorem targetZeroFrom_zero_gt_a0_add_one (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) :
    a0 + 1 < targetZeroFrom f hcont a0 hnp hnn 0 :=
  (target_zero_past_from f hcont a0 hnp hnn (a0 + 1)).choose_spec.1

theorem targetZeroFrom_succ_gt (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) (k : Nat) :
    targetZeroFrom f hcont a0 hnp hnn k < targetZeroFrom f hcont a0 hnp hnn (k + 1) :=
  (target_zero_past_from f hcont a0 hnp hnn
    (targetZeroFrom f hcont a0 hnp hnn k)).choose_spec.1

theorem targetZeroFrom_strictMono (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) {i j : Nat} (hij : i < j) :
    targetZeroFrom f hcont a0 hnp hnn i < targetZeroFrom f hcont a0 hnp hnn j := by
  induction j with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact lt_trans_ax (ih hlt) (targetZeroFrom_succ_gt f hcont a0 hnp hnn m)
    · have hie : i = m := by omega
      rw [hie]
      exact targetZeroFrom_succ_gt f hcont a0 hnp hnn m

theorem targetZeroFrom_eval_zero (f : Real → Real) (hcont : ∀ x : Real, ContinuousAt f x)
    (a0 : Real)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ f x) (k : Nat) :
    f (targetZeroFrom f hcont a0 hnp hnn k) = 0 := by
  cases k with
  | zero => exact (target_zero_past_from f hcont a0 hnp hnn (a0 + 1)).choose_spec.2.2
  | succ m =>
      exact (target_zero_past_from f hcont a0 hnp hnn
        (targetZeroFrom f hcont a0 hnp hnn m)).choose_spec.2.2

/-- **The stronger meta-lemma.** No finite EML tree equals `TARGET`, given only continuity and
`¬TailSign (fun x => TARGET x - L)` for some `L`. Combines `eml_eventually_valid_repr` (validity
on a tail from `a`, matching `T` past `R`) with an IVT-constructed zero sequence of `TARGET - L`
seeded past `max(a, R)` — the zero sequence and Trep's validity live in the SAME region by
construction, so `enc_combinedBound` applies directly, mirroring `evalid_tailSign`'s own assembly
(cont. 58) with the EML-tree-derived zero sequence replaced by a target-derived one. -/
theorem no_tree_eq_target_of_not_tailSign
    (TARGET : Real → Real) (L : Real) (hcont : ∀ x : Real, ContinuousAt TARGET x)
    (hnts : ¬ TailSign (fun x => TARGET x - L))
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = TARGET x) : False := by
  obtain ⟨Trep, a, hvalid, R, heqR⟩ := eml_eventually_valid_repr T
  let f : Real → Real := fun x => TARGET x - L
  have hcontf : ∀ x : Real, ContinuousAt f x := fun x => continuousAt_sub_const (hcont x) L
  have hnp := hnp_of_not_tailSign f hnts
  have hnn := hnn_of_not_tailSign f hnts
  have hnz := hnz_of_not_tailSign f hnts
  obtain ⟨a0, haa0, hRa0⟩ := lt_of_lt_both a R
  let p := (enc Trep emlEmptyChain).2
  let p' := MultiPoly.sub p (MultiPoly.const L)
  let M := combinedBoundE (len Trep 0) (enc Trep emlEmptyChain).1 (encTags Trep emlEmptyChain ()) p'
  let z := targetZeroFrom f hcontf a0 hnp hnn
  have hz0gtA1 : a0 + 1 < z 0 := targetZeroFrom_zero_gt_a0_add_one f hcontf a0 hnp hnn
  have hzmono : ∀ i j : Nat, i < j → z i < z j :=
    fun i j hij => targetZeroFrom_strictMono f hcontf a0 hnp hnn hij
  have hzMgtA1 : a0 + 1 < z M := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0]; exact hz0gtA1
    · exact lt_trans_ax hz0gtA1 (hzmono 0 M hMpos)
  obtain ⟨w, hwA1, hwne⟩ := hnz (a0 + 1)
  obtain ⟨b, hzM_lt_b, hw_lt_b⟩ := lt_of_lt_both (z M) w
  have hinner_ab : a0 + 1 < b := lt_trans_ax hzMgtA1 hzM_lt_b
  have houter_lt : b < b + 1 := lt_add_pos b 1 zero_lt_one_ax
  have ha_lt_b1 : a < b + 1 :=
    lt_trans_ax haa0 (lt_trans_ax (lt_trans_ax (lt_add_pos a0 1 zero_lt_one_ax) hinner_ab)
      houter_lt)
  have hvalidon_here : EMLPfaffianValidOn Trep a (b + 1) := hvalid (b + 1) ha_lt_b1
  have hlogPos : LogArgPosOn Trep (Icc (a0 + 1) b) :=
    logArgPosOn_Icc_of_validOn Trep a (b + 1) (a0 + 1) b
      (lt_trans_ax haa0 (lt_add_pos a0 1 zero_lt_one_ax)) houter_lt hvalidon_here
  have hRa0add1 : R < a0 + 1 := lt_trans_ax hRa0 (lt_add_pos a0 1 zero_lt_one_ax)
  have hne : ∃ v : Real, (a0 + 1 : Real) < v ∧ v < b ∧
      (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval v ≠ 0 := by
    refine ⟨w, hwA1, hw_lt_b, ?_⟩
    show MultiPoly.eval p' w ((enc Trep emlEmptyChain).1.chainValues w) ≠ 0
    show MultiPoly.eval p w ((enc Trep emlEmptyChain).1.chainValues w) - L ≠ 0
    have heval : MultiPoly.eval p w ((enc Trep emlEmptyChain).1.chainValues w)
        = Trep.eval w := enc_eval Trep emlEmptyChain w
    rw [heval, heqR w (lt_trans_ax hRa0add1 hwA1), heq]
    intro hz
    have e : TARGET w - L = 0 := hz
    exact hwne e
  have hbound := enc_combinedBound Trep emlEmptyChain () (a0 + 1) b hinner_ab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p' hne
  let zeros : List Real := (List.range (M + 1)).map z
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ v ∈ zeros,
      (a0 + 1 : Real) < v ∧ v < b ∧
        (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval v = 0 := by
    intro v hv
    simp only [zeros, List.mem_map, List.mem_range] at hv
    obtain ⟨i, hilt, hveq⟩ := hv
    have hRvi : R < z i := by
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · rw [hi0]; exact lt_trans_ax hRa0add1 hz0gtA1
      · exact lt_trans_ax hRa0add1 (lt_trans_ax hz0gtA1 (hzmono 0 i hipos))
    refine ⟨?_, ?_, ?_⟩
    · rw [← hveq]
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · rw [hi0]; exact hz0gtA1
      · exact lt_trans_ax hz0gtA1 (hzmono 0 i hipos)
    · rw [← hveq]
      rcases Nat.lt_or_ge i M with hlt | hge
      · exact lt_trans_ax (hzmono i M hlt) hzM_lt_b
      · have hiM : i = M := by omega
        rw [hiM]; exact hzM_lt_b
    · rw [← hveq]
      show MultiPoly.eval p (z i) ((enc Trep emlEmptyChain).1.chainValues (z i)) - L = 0
      have heval : MultiPoly.eval p (z i) ((enc Trep emlEmptyChain).1.chainValues (z i))
          = Trep.eval (z i) := enc_eval Trep emlEmptyChain (z i)
      rw [heval, heqR (z i) hRvi, heq]
      have hfz : f (z i) = 0 := targetZeroFrom_eval_zero f hcontf a0 hnp hnn i
      exact hfz
  have hzeros_nodup : zeros.Nodup := by
    show List.Pairwise (· ≠ ·) zeros
    exact (List.nodup_range (M + 1)).map z
      (fun i j (_hij_neq : i ≠ j) => by
        intro hij_eq
        rcases Nat.lt_or_ge i j with hlt | hge
        · have h := hzmono i j hlt
          rw [hij_eq] at h
          exact lt_irrefl_ax _ h
        · have hlt2 : j < i := by omega
          have h := hzmono j i hlt2
          rw [← hij_eq] at h
          exact lt_irrefl_ax _ h)
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

/-- **Sanity check: `sin` instantiates cleanly.** `TARGET := sin`, `L := 0` — `sin` is continuous
everywhere (`hasDerivAt_continuousAt` composed with `HasDerivAt_sin`), and `¬TailSign (fun x =>
sin x - 0)` reduces to `sin_not_tailSign` (cont. 56) via `sub_zero`. Confirms this file's stronger
form genuinely reaches the same conclusion cont. 58 reached a different way, not merely a
plausible-looking generalization. -/
theorem no_tree_eq_sin_unconditional_via_continuous_meta (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = Real.sin x) : False := by
  have hcont : ∀ x : Real, ContinuousAt Real.sin x :=
    fun x => hasDerivAt_continuousAt (HasDerivAt_sin x)
  have hnts : ¬ TailSign (fun x : Real => Real.sin x - 0) := by
    intro h
    apply sin_not_tailSign
    have heq0 : ∀ x : Real, (fun x : Real => Real.sin x - 0) x = Real.sin x := fun x => sub_zero _
    exact tailSign_congr_eventually 0 (fun x _ => heq0 x) h
  exact no_tree_eq_target_of_not_tailSign Real.sin 0 hcont hnts T heq

end Real
end MachLib
