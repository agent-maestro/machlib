import MachLib.EMLExplicitBoundComposition
import MachLib.EMLEncoderDescent
import MachLib.EMLEncoderAnalytic

/-!
# Bridging the concrete EML encoder to the explicit composed descent

`enc` (`EMLEncoder.lean`) builds a chain purely from an `EMLTree`, with no `(a,b)` dependence
anywhere in its construction — confirmed by reading `stepCC`/`stepCD`/`encEmlStepR`: the reciprocal
level's relation is literally `r' = -(cTD w)·r²`, a fixed polynomial expression, and its witness `v`
is literally `liftLastY w`. This file makes that explicit: `encTags` builds the `ChainTags` for
`enc t chain` by literal recursion over `t`, mirroring `enc`'s own recursion and using EXACTLY the
witnesses `encEmlStepR_IsExpLogRecipW`'s (existing, existential) proof already names — so no
`Classical.choice` is needed anywhere, and the resulting bound (via `combined_descent_3_explicit`) is
provably independent of `(a,b)`.
-/

namespace MachLib.EMLExplicitBound

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

/-! ## Triangularity descends through `enc` (unconditional — no type hypothesis needed) -/

/-- **`chainExtend` preserves triangularity, unconditionally.** Old columns keep their triangularity
through `liftLastY` (`degreeY_liftLastY_of_lt`); the new column's own top-freedom at OLD indices is
automatic (`degreeY_top_liftLastY`); and the new relation's triangularity requirement (`j.val > n`
for `j : Fin (n+1)`) is vacuous since `n` is the maximum index. Unlike `chainExtend_IsExpLogRecipW`,
no `hnew` shape hypothesis is needed at all — triangularity never depends on the new relation's shape. -/
theorem chainExtend_isTriangular {n : Nat} (c : PfaffianChain n) (hTri : c.IsTriangular)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) :
    (chainExtend c ne nr).IsTriangular := by
  intro i j hij
  by_cases hi : i.val < n
  · rw [chainExtend_relations_of_lt c ne nr i hi]
    by_cases hj : j.val < n
    · rw [degreeY_liftLastY_of_lt j hj (c.relations ⟨i.val, hi⟩)]
      exact hTri ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
    · have hjeq : j = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
        apply Fin.ext; show j.val = n; have := j.isLt; omega
      rw [hjeq]; exact degreeY_top_liftLastY _
  · exfalso
    have hival : i.val = n := by have := i.isLt; omega
    have hjlt := j.isLt
    omega

/-- **`enc` preserves triangularity.** By induction on `t`, applying `chainExtend_isTriangular` three
times per `eml` node (recip/log/exp, exactly `encEmlStepR`'s three `chainExtend` layers). -/
theorem enc_isTriangular (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N), chain.IsTriangular → (enc t chain).1.IsTriangular := by
  induction t with
  | const c => intro N chain hchain; exact hchain
  | var => intro N chain hchain; exact hchain
  | eml t1 t2 ih1 ih2 =>
    intro N chain hchain
    have h1 : (enc t1 (enc t2 chain).1).1.IsTriangular := ih1 (enc t2 chain).1 (ih2 chain hchain)
    show (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
      (encLift t1 (enc t2 chain).2)).IsTriangular
    unfold encEmlStepR stepCD stepCC
    exact chainExtend_isTriangular _ (chainExtend_isTriangular _ (chainExtend_isTriangular _ h1 _ _) _ _) _ _

/-! ## The structural tags for `enc t chain` -/

/-- **The `ChainTags` for `enc t chain`.** Literal recursion mirroring `enc`'s own recursion. At an
`eml` node, the three new levels (recip/log/exp, `encEmlStepR`'s three `chainExtend` layers) get the
EXACT witnesses `encEmlStepR_IsExpLogRecipW`'s (existential) proof already names: `v := liftLastY w`
for the reciprocal level, no witness for the log level, `G := liftLastY (cTD (stepCD cb w)
(liftLastYBy 2 b1))` for the exponential level. -/
noncomputable def encTags : (t : EMLTree) → {N : Nat} → PfaffianChain N → ChainTags N → ChainTags (len t N)
  | .const _, _, _, tags => tags
  | .var, _, _, tags => tags
  | .eml t1 t2, _, chain, tags =>
      let tags1 := encTags t1 (enc t2 chain).1 (encTags t2 chain tags)
      let cb := (enc t1 (enc t2 chain).1).1
      let b1 := (enc t1 (enc t2 chain).1).2
      let w := encLift t1 (enc t2 chain).2
      (ChainTypeTag.expTag
          (MultiPoly.liftLastY (chainTotalDeriv (stepCD cb w) (liftLastYBy 2 b1))),
        (ChainTypeTag.logTag,
          (ChainTypeTag.recipTag (MultiPoly.liftLastY w), tags1)))

/-! ## Per-level structural validity (mirrors `encEmlStepR_IsExpLogRecipW`'s three blocks) -/

theorem stepCC_ChainTagValid {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) :
    ChainTagValid (stepCC cb w) (ChainTypeTag.recipTag (MultiPoly.liftLastY w)) := by
  intro j hj
  have hjeq : j = (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) := by
    apply Fin.ext; show j.val = M; have := j.isLt; omega
  rw [hjeq]; exact degreeY_top_liftLastY w

theorem stepCD_ChainTagValid {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) :
    ChainTagValid (stepCD cb w) ChainTypeTag.logTag := by
  have dmul : ∀ {k : Nat} (i : Fin k) (p q : MultiPoly k),
      MultiPoly.degreeY i (MultiPoly.mul p q)
        = MultiPoly.degreeY i p + MultiPoly.degreeY i q := fun _ _ _ => rfl
  show MultiPoly.degreeY (⟨M + 1, Nat.lt_succ_self (M + 1)⟩ : Fin (M + 2))
      ((stepCD cb w).relations (⟨M + 1, Nat.lt_succ_self (M + 1)⟩ : Fin (M + 2))) = 0
  unfold stepCD
  rw [chainExtend_relations_last (stepCC cb w) _ _, dmul, degreeY_top_liftLastY, Nat.zero_add]
  show (if (⟨M + 1, Nat.lt_succ_self (M + 1)⟩ : Fin (M + 2)) = (⟨M, by omega⟩ : Fin (M + 2))
      then (1 : Nat) else 0) = 0
  rw [if_neg (Fin.ne_of_val_ne (Nat.succ_ne_self M))]

theorem encEmlStepR_ChainTagValid {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M) :
    ChainTagValid (encEmlStepR cb b1 w)
      (ChainTypeTag.expTag (MultiPoly.liftLastY (chainTotalDeriv (stepCD cb w) (liftLastYBy 2 b1)))) := by
  refine ⟨degreeY_top_liftLastY _, ?_⟩
  unfold encEmlStepR
  exact chainExtend_relations_last _ _ _

/-- **`ChainTagsValid` for `encTags`.** By induction on `t`, peeling the three new levels off via
`chainExtend_chainRestrict` (the round-trip: restricting an extension returns the chain it extended)
and discharging each with the corresponding per-level lemma above. -/
theorem encTags_valid (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (tags : ChainTags N),
      ChainTagsValid N chain tags → ChainTagsValid (len t N) (enc t chain).1 (encTags t chain tags) := by
  induction t with
  | const c => intro N chain tags h; exact h
  | var => intro N chain tags h; exact h
  | eml t1 t2 ih1 ih2 =>
    intro N chain tags h
    have h1 := ih1 (enc t2 chain).1 (encTags t2 chain tags) (ih2 chain tags h)
    have hR1 : chainRestrict (stepCC (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2))
        = (enc t1 (enc t2 chain).1).1 := chainExtend_chainRestrict _ _ _
    have hR2 : chainRestrict (stepCD (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2))
        = stepCC (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2) :=
      chainExtend_chainRestrict _ _ _
    have hR3 : chainRestrict (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
        (encLift t1 (enc t2 chain).2))
        = stepCD (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2) :=
      chainExtend_chainRestrict _ _ _
    show ChainTagsValid (len t1 (len t2 N) + 3)
        (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
          (encLift t1 (enc t2 chain).2))
        (ChainTypeTag.expTag
            (MultiPoly.liftLastY (chainTotalDeriv (stepCD (enc t1 (enc t2 chain).1).1
              (encLift t1 (enc t2 chain).2)) (liftLastYBy 2 (enc t1 (enc t2 chain).1).2))),
          (ChainTypeTag.logTag,
            (ChainTypeTag.recipTag (MultiPoly.liftLastY (encLift t1 (enc t2 chain).2)),
              encTags t1 (enc t2 chain).1 (encTags t2 chain tags))))
    refine ⟨encEmlStepR_ChainTagValid _ _ _, ?_⟩
    rw [hR3]
    refine ⟨stepCD_ChainTagValid _ _, ?_⟩
    rw [hR2]
    refine ⟨stepCC_ChainTagValid _ _, ?_⟩
    rw [hR1]
    exact h1

/-! ## Per-level `(a,b)`-dependent validity -/

theorem stepCC_ChainTagValidAB {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) (a b : Real)
    (hwpos : ∀ x, a < x → x < b → 0 < MultiPoly.eval w x (cb.chainValues x)) :
    ChainTagValidAB (stepCC cb w) a b (ChainTypeTag.recipTag (MultiPoly.liftLastY w)) := by
  unfold stepCC
  refine ⟨?_, ?_⟩
  · intro x hxa hxb
    rw [chainExtend_evals_last cb _ _, eval_liftLastY_chainExtend cb _ _ w x]
    show (1 / MultiPoly.eval w x (cb.chainValues x)) * MultiPoly.eval w x (cb.chainValues x) = 1
    exact div_mul_cancel (ne_of_gt (hwpos x hxa hxb))
  · intro x hxa hxb
    rw [eval_liftLastY_chainExtend cb _ _ w x]; exact hwpos x hxa hxb

theorem encEmlStepR_ChainTagValidAB {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M) (a b : Real) :
    ChainTagValidAB (encEmlStepR cb b1 w) a b
      (ChainTypeTag.expTag (MultiPoly.liftLastY (chainTotalDeriv (stepCD cb w) (liftLastYBy 2 b1)))) := by
  intro z _ _
  show MultiPoly.eval (MultiPoly.varY (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))) z
      ((encEmlStepR cb b1 w).chainValues z) ≠ 0
  have heval : MultiPoly.eval (MultiPoly.varY (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))) z
      ((encEmlStepR cb b1 w).chainValues z)
      = (encEmlStepR cb b1 w).evals (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3)) z := by
    rw [MultiPoly.eval_varY]; rfl
  rw [heval]
  unfold encEmlStepR
  rw [chainExtend_evals_last]
  exact ne_of_gt (Real.exp_pos _)

/-- **`ChainTagsValidAB` for `encTags`.** Same shape as `encTags_valid`, threading `LogArgPos`'s
per-`eml`-node positivity fact (`hposLog`) into `hwpos` via `enc_encLift_eval`/`enc_eval` (exactly
`enc_IsExpLogRecipW`'s own derivation). -/
theorem encTags_validAB (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (tags : ChainTags N) (a b : Real),
      ChainTagsValidAB N chain a b tags → LogArgPos t a b →
      ChainTagsValidAB (len t N) (enc t chain).1 a b (encTags t chain tags) := by
  induction t with
  | const c => intro N chain tags a b h _; exact h
  | var => intro N chain tags a b h _; exact h
  | eml t1 t2 ih1 ih2 =>
    intro N chain tags a b h hlog
    obtain ⟨hlog1, hlog2, hposLog⟩ := hlog
    have h1 := ih1 (enc t2 chain).1 (encTags t2 chain tags) a b (ih2 chain tags a b h hlog2) hlog1
    have hwpos : ∀ x, a < x → x < b → 0 < MultiPoly.eval (encLift t1 (enc t2 chain).2) x
        ((enc t1 (enc t2 chain).1).1.chainValues x) := by
      intro x hxa hxb
      rw [enc_encLift_eval t1 t2 chain x (t2.eval x) (enc_eval t2 chain x)]
      exact hposLog x hxa hxb
    have hR1 : chainRestrict (stepCC (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2))
        = (enc t1 (enc t2 chain).1).1 := chainExtend_chainRestrict _ _ _
    have hR2 : chainRestrict (stepCD (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2))
        = stepCC (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2) :=
      chainExtend_chainRestrict _ _ _
    have hR3 : chainRestrict (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
        (encLift t1 (enc t2 chain).2))
        = stepCD (enc t1 (enc t2 chain).1).1 (encLift t1 (enc t2 chain).2) :=
      chainExtend_chainRestrict _ _ _
    show ChainTagsValidAB (len t1 (len t2 N) + 3)
        (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
          (encLift t1 (enc t2 chain).2)) a b
        (ChainTypeTag.expTag
            (MultiPoly.liftLastY (chainTotalDeriv (stepCD (enc t1 (enc t2 chain).1).1
              (encLift t1 (enc t2 chain).2)) (liftLastYBy 2 (enc t1 (enc t2 chain).1).2))),
          (ChainTypeTag.logTag,
            (ChainTypeTag.recipTag (MultiPoly.liftLastY (encLift t1 (enc t2 chain).2)),
              encTags t1 (enc t2 chain).1 (encTags t2 chain tags))))
    refine ⟨encEmlStepR_ChainTagValidAB _ _ _ a b, ?_⟩
    rw [hR3]
    refine ⟨trivial, ?_⟩
    rw [hR2]
    refine ⟨stepCC_ChainTagValidAB _ _ a b hwpos, ?_⟩
    rw [hR1]
    exact h1

/-! ## The explicit bound for any EML-tree-derived chain -/

/-- **The explicit bound for `enc t chain`.** Assembles `encTags`/`encTags_valid`/`encTags_validAB`/
`enc_isTriangular` with the encoder's own `enc_coherent_and_hAnalytic` (coherence + analyticity, behind
the single closed-interval `LogArgPosOn` hypothesis) and feeds `combined_descent_3_explicit`. The
resulting bound `combinedBoundE (len t N) (enc t chain).1 (encTags t chain tags) p` is, by
construction, a function of the chain's structure and `p`'s degrees ALONE — it never mentions `a` or
`b`, closing AXIOM_AUDIT_V2.md §2c(2) item (i) for concrete EML-tree chains. -/
theorem enc_combinedBound (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (tags : ChainTags N)
    (a b : Real) (hab : a < b)
    (hValid : ChainTagsValid N chain tags) (hValidAB : ChainTagsValidAB N chain a b tags)
    (hTri : chain.IsTriangular) (hcoh : chain.IsCoherentOn a b)
    (han : ∀ i, IsAnalyticOnReals (fun x => chain.evals i x) (Icc a b))
    (hpos : LogArgPosOn t (Icc a b))
    (p : MultiPoly (len t N))
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (enc t chain).1 p).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn (enc t chain).1 p) a b
      (combinedBoundE (len t N) (enc t chain).1 (encTags t chain tags) p) := by
  obtain ⟨hcohEnc, hAnEnc⟩ := enc_coherent_and_hAnalytic t chain a b hcoh han hpos
  exact combined_descent_3_explicit a b hab (len t N) (enc t chain).1 (encTags t chain tags)
    (encTags_valid t chain tags hValid)
    (encTags_validAB t chain tags a b hValidAB (LogArgPos_of_LogArgPosOn_Icc a b t hpos))
    (enc_isTriangular t chain hTri) hcohEnc hAnEnc p hne

end MachLib.EMLExplicitBound
