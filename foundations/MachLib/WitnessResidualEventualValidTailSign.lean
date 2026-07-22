import MachLib.WitnessResidualRCEPTailSign

/-!
**Tail-restricted generalization of `rcep_tailSign`.** `RightChildrenEverywherePositive`
gives `EMLPfaffianValidOn` starting from `0` unconditionally; this file only needs validity on
tails past an arbitrary fixed `a`, which is what the harder "B eventually positive" case of
`WitnessResidualTailSign.lean`'s own induction can actually supply (there is no way to build a
substitute tree that is both globally sign-definite and agrees with the original on the tail —
see `EML_WITNESS_FINDING_DECISION_2026_07_15.md` cont.57-58). The zero-sequence/IVT machinery
below mirrors `WitnessResidualRCEPTailSign.lean` almost exactly, parametrized by `a` throughout;
the one genuine change is how the interval endpoint `b` is built (`lt_of_lt_both` picks a point
exceeding two given reals directly, instead of RCEP's `z M + w + 1` additive trick, since that
trick relied on `w` and `z M` both being `> 0` — true there because everything sat past `1`, but
not available here since `a` may be arbitrarily negative).
-/

open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

namespace MachLib
namespace Real

theorem emlPfaffianValidOn_no_crossing :
    ∀ (T : EMLTree) {a b x : Real}, a < x → x < b →
      EMLPfaffianValidOn T a b → MachLib.EMLNoCrossingAt T x := by
  intro T
  induction T with
  | const c => intro _ _ _ _ _ _; trivial
  | var => intro _ _ _ _ _ _; trivial
  | eml t1 t2 ih1 ih2 =>
    intro a b x ha hb hvalidon
    obtain ⟨h1, h2, h3⟩ := hvalidon
    exact ⟨ih1 ha hb h1, ih2 ha hb h2, ne_of_gt (h3 x ha hb)⟩

theorem evalid_zero_between (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (x1 x2 : Real) (ha1 : a < x1) (hx1x2 : x1 < x2) (h1 : T.eval x1 ≤ 0) (h2 : 0 < T.eval x2) :
    ∃ z : Real, x1 ≤ z ∧ z < x2 ∧ T.eval z = 0 := by
  rcases lt_total (T.eval x1) 0 with hlt | heq | hgt
  · have hb : a < x2 + 1 := lt_trans_ax ha1 (lt_trans_ax hx1x2 (lt_add_pos x2 1 zero_lt_one_ax))
    have hv := hvalidon (x2 + 1) hb
    have hdiff : ∀ z : Real, x1 ≤ z → z ≤ x2 → ∃ f' : Real, HasDerivAt T.eval f' z := by
      intro z hz1 hz2
      have haz : a < z := lt_of_lt_of_le ha1 hz1
      have hzb : z < x2 + 1 := lt_of_le_of_lt hz2 (lt_add_pos x2 1 zero_lt_one_ax)
      exact eml_hasDerivAt_of_no_crossing T z (emlPfaffianValidOn_no_crossing T haz hzb hv)
    obtain ⟨c, hc1, hc2, hc3⟩ := intermediate_value_of_hasDerivAt T.eval x1 x2 hx1x2 hdiff hlt h2
    exact ⟨c, le_of_lt hc1, hc2, hc3⟩
  · exact ⟨x1, le_refl x1, hx1x2, heq⟩
  · exfalso; exact lt_irrefl_ax 0 (lt_of_lt_of_le hgt h1)

/-- Given a point strictly bigger than BOTH `R` and `a`, always constructible via a 3-way case
split — avoids ever needing `max` directly. -/
theorem lt_of_lt_both (R a : Real) : ∃ M : Real, R < M ∧ a < M := by
  rcases lt_total R a with h | h | h
  · exact ⟨a + 1, lt_trans_ax h (lt_add_pos a 1 zero_lt_one_ax), lt_add_pos a 1 zero_lt_one_ax⟩
  · exact ⟨a + 1, by rw [h]; exact lt_add_pos a 1 zero_lt_one_ax, lt_add_pos a 1 zero_lt_one_ax⟩
  · exact ⟨R + 1, lt_add_pos R 1 zero_lt_one_ax, lt_trans_ax h (lt_add_pos R 1 zero_lt_one_ax)⟩

/-- Unlike the RCEP version, this bakes `a < z` directly into its OWN conclusion (not just `R < z`)
so the recursive zero-sequence built from it never needs an external "the previous zero is past
`a`" side-proof at the call site — it's available immediately from `.choose_spec`. -/
theorem evalid_zero_past (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x)
    (R : Real) : ∃ z : Real, R < z ∧ a < z ∧ T.eval z = 0 := by
  obtain ⟨M, hRM, haM⟩ := lt_of_lt_both R a
  obtain ⟨x1, hx1M, hx1⟩ := hnp M
  have hax1 : a < x1 := lt_trans_ax haM hx1M
  obtain ⟨x2, hx2x1, hx2⟩ := hnn x1
  rcases lt_total (T.eval x2) 0 with hlt | heq | hgt
  · exfalso; exact lt_irrefl_ax 0 (lt_of_le_of_lt hx2 hlt)
  · exact ⟨x2, lt_trans_ax (lt_trans_ax hRM hx1M) hx2x1, lt_trans_ax hax1 hx2x1, heq⟩
  · obtain ⟨z, hz1, hz2, hz3⟩ := evalid_zero_between T a hvalidon x1 x2 hax1 hx2x1 hx1 hgt
    exact ⟨z, lt_of_lt_of_le (lt_trans_ax hRM hx1M) hz1,
      lt_of_lt_of_le hax1 hz1, hz3⟩

noncomputable def evalidZero (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) : Nat → Real
  | 0 => (evalid_zero_past T a hvalidon hnp hnn (a + 1)).choose
  | (k + 1) => (evalid_zero_past T a hvalidon hnp hnn (evalidZero T a hvalidon hnp hnn k)).choose

theorem evalidZero_gt_a (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (k : Nat) :
    a < evalidZero T a hvalidon hnp hnn k := by
  cases k with
  | zero => exact (evalid_zero_past T a hvalidon hnp hnn (a + 1)).choose_spec.2.1
  | succ m =>
      exact (evalid_zero_past T a hvalidon hnp hnn (evalidZero T a hvalidon hnp hnn m)).choose_spec.2.1

/-- The first zero lands strictly past `a + 1`, not just past `a` — mirrors `rcepZero`'s own
choice to seed past `1` rather than `0`, so the inner interval `(a+1, b)` needed by
`logArgPosOn_Icc_of_validOn` (which requires a STRICT `a < a'`) is available directly. -/
theorem evalidZero_zero_gt_a_add_one (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) :
    a + 1 < evalidZero T a hvalidon hnp hnn 0 :=
  (evalid_zero_past T a hvalidon hnp hnn (a + 1)).choose_spec.1

theorem evalidZero_succ_gt (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (k : Nat) :
    evalidZero T a hvalidon hnp hnn k < evalidZero T a hvalidon hnp hnn (k + 1) :=
  (evalid_zero_past T a hvalidon hnp hnn (evalidZero T a hvalidon hnp hnn k)).choose_spec.1

theorem evalidZero_strictMono (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) {i j : Nat} (hij : i < j) :
    evalidZero T a hvalidon hnp hnn i < evalidZero T a hvalidon hnp hnn j := by
  induction j with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact lt_trans_ax (ih hlt) (evalidZero_succ_gt T a hvalidon hnp hnn m)
    · have hie : i = m := by omega
      rw [hie]
      exact evalidZero_succ_gt T a hvalidon hnp hnn m

theorem evalidZero_eval_zero (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (k : Nat) :
    T.eval (evalidZero T a hvalidon hnp hnn k) = 0 := by
  cases k with
  | zero => exact (evalid_zero_past T a hvalidon hnp hnn (a + 1)).choose_spec.2.2
  | succ m =>
      exact (evalid_zero_past T a hvalidon hnp hnn (evalidZero T a hvalidon hnp hnn m)).choose_spec.2.2

theorem evalidZeros_list_nodup (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b)
    (hnp : ∀ R : Real, ∃ x : Real, R < x ∧ T.eval x ≤ 0)
    (hnn : ∀ R : Real, ∃ x : Real, R < x ∧ 0 ≤ T.eval x) (M : Nat) :
    ((List.range (M + 1)).map (evalidZero T a hvalidon hnp hnn)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (evalidZero T a hvalidon hnp hnn))
  exact (List.nodup_range (M + 1)).map (evalidZero T a hvalidon hnp hnn)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := evalidZero_strictMono T a hvalidon hnp hnn hlt
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := evalidZero_strictMono T a hvalidon hnp hnn hlt2
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-- **Tail-restricted generalization of `rcep_tailSign`.** Validity need only hold on tails
starting from an ARBITRARY fixed `a` (not `0`), so this covers trees that only become
well-behaved eventually rather than globally. Mirrors `rcep_tailSign`'s IVT/zero-sequence
contradiction argument exactly, but the interval endpoint `b` is built via `lt_of_lt_both`
(exceeds both `z M` and `w` directly) instead of the additive `z M + w + 1` trick RCEP used —
that trick relied on `w`, `z M` both being `> 0` (true there since everything sat past `1`), which
is no longer available here since `a` (and hence `w`, `z M`) may be arbitrarily negative. -/
theorem evalid_tailSign (T : EMLTree) (a : Real)
    (hvalidon : ∀ b : Real, a < b → EMLPfaffianValidOn T a b) :
    TailSign T.eval := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hnp := rcep_hnp_of_not_tailSign T hcon
  have hnn := rcep_hnn_of_not_tailSign T hcon
  have hnz := rcep_hnz_of_not_tailSign T hcon
  let p := (enc T emlEmptyChain).2
  let M := combinedBoundE (len T 0) (enc T emlEmptyChain).1 (encTags T emlEmptyChain ()) p
  let z := evalidZero T a hvalidon hnp hnn
  have hz0gtA1 : a + 1 < z 0 := evalidZero_zero_gt_a_add_one T a hvalidon hnp hnn
  have hzmono : ∀ i j : Nat, i < j → z i < z j :=
    fun i j hij => evalidZero_strictMono T a hvalidon hnp hnn hij
  have hzMgtA1 : a + 1 < z M := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0]; exact hz0gtA1
    · exact lt_trans_ax hz0gtA1 (hzmono 0 M hMpos)
  obtain ⟨w, hwA1, hwne⟩ := hnz (a + 1)
  obtain ⟨b, hzM_lt_b, hw_lt_b⟩ := lt_of_lt_both (z M) w
  have hinner_ab : a + 1 < b := lt_trans_ax hzMgtA1 hzM_lt_b
  have houter_lt : b < b + 1 := lt_add_pos b 1 zero_lt_one_ax
  have ha_lt_b1 : a < b + 1 :=
    lt_trans_ax (lt_trans_ax (lt_add_pos a 1 zero_lt_one_ax) hinner_ab) houter_lt
  have hvalidon_here : EMLPfaffianValidOn T a (b + 1) := hvalidon (b + 1) ha_lt_b1
  have hlogPos : LogArgPosOn T (Icc (a + 1) b) :=
    logArgPosOn_Icc_of_validOn T a (b + 1) (a + 1) b (lt_add_pos a 1 zero_lt_one_ax)
      houter_lt hvalidon_here
  have hne : ∃ v : Real, (a + 1 : Real) < v ∧ v < b ∧
      (pfaffianChainFn (enc T emlEmptyChain).1 p).eval v ≠ 0 := by
    refine ⟨w, hwA1, hw_lt_b, ?_⟩
    show MultiPoly.eval p w ((enc T emlEmptyChain).1.chainValues w) ≠ 0
    have heval : MultiPoly.eval p w ((enc T emlEmptyChain).1.chainValues w)
        = T.eval w := enc_eval T emlEmptyChain w
    rw [heval]; exact hwne
  have hbound := enc_combinedBound T emlEmptyChain () (a + 1) b hinner_ab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p hne
  let zeros : List Real := (List.range (M + 1)).map z
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ v ∈ zeros,
      (a + 1 : Real) < v ∧ v < b ∧
        (pfaffianChainFn (enc T emlEmptyChain).1 p).eval v = 0 := by
    intro v hv
    simp only [zeros, List.mem_map, List.mem_range] at hv
    obtain ⟨i, hilt, hveq⟩ := hv
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
      show MultiPoly.eval p (z i) ((enc T emlEmptyChain).1.chainValues (z i)) = 0
      have heval : MultiPoly.eval p (z i) ((enc T emlEmptyChain).1.chainValues (z i))
          = T.eval (z i) := enc_eval T emlEmptyChain (z i)
      rw [heval]; exact evalidZero_eval_zero T a hvalidon hnp hnn i
  have hzeros_nodup : zeros.Nodup := evalidZeros_list_nodup T a hvalidon hnp hnn M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end Real
end MachLib
