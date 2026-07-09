import MachLib.IterExpDepthNDegreeX

/-!
# Depth-N `degreeY` +1-growth tower (the A-bound side of the chain-N explicit bound)

Step 2 of the chain-N explicit-bound build, A-bound half (`chainN-explicit-bound-design.md` §6). The
explicit bound's inner (`cdegYAt`) components GROW under reduce — a reduce replaces each `varY i` by the
chain relation `prodVarYUpTo i` (a product of `y`s), so any lower `degreeY_j` rises by at most 1. This
per-reduce `+1` is exactly what forces the level-indexed budget (chain-2's `degreeY0_chain2Reduce_le`),
and it is the growth accounting the design flagged as the research mile. Here we prove the growth FACTS
at depth-N (mechanical mirrors of the chain-2 lemmas); turning them into the closing budget is step 4.

  * `degreeY_prodVarYUpTo_eq`  — `degreeY_j(prodVarYUpTo k) = [j ≤ k]` (each tower relation has each y
                                 to degree ≤ 1); `_le_one` corollary.
  * `degreeY_chainTotalDeriv_iterExp_growth` — cTD grows any `degreeY_j` by ≤ 1 (mirror of chain-2).
  * `degreeY_liftLastY_low'`   — `liftLastY` preserves lower-index `degreeY` (index re-embedding).
  * `degreeY_gradedTop_le_one`, `degreeY_fullMult_le_one` — the reduce multiplier has every `degreeY ≤ 1`.
  * `degreeY_chainNReduce_growth_le` / `_fullMult_growth_le` — the reduce grows `degreeY_j` by ≤ 1.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2CanonMeasure

/-- Each tower relation `prodVarYUpTo k = y₀·…·y_k` contains `y_j` iff `j ≤ k`, to degree exactly 1. -/
theorem degreeY_prodVarYUpTo_eq {N : Nat} (i : Fin N) : ∀ (k : Nat) (hk : k < N),
    MultiPoly.degreeY i (prodVarYUpTo k hk) = if i.val ≤ k then 1 else 0
  | 0, hk => by
      show (if i = (⟨0, hk⟩ : Fin N) then 1 else 0) = if i.val ≤ 0 then 1 else 0
      by_cases h : i.val = 0
      · rw [if_pos (Fin.ext h), if_pos (by omega)]
      · rw [if_neg (fun he => h (congrArg Fin.val he)), if_neg (by omega)]
  | k + 1, hk => by
      show MultiPoly.degreeY i (prodVarYUpTo k (Nat.lt_of_succ_lt hk))
          + MultiPoly.degreeY i (MultiPoly.varY (⟨k + 1, hk⟩ : Fin N))
          = if i.val ≤ k + 1 then 1 else 0
      rw [degreeY_prodVarYUpTo_eq i k (Nat.lt_of_succ_lt hk)]
      show (if i.val ≤ k then 1 else 0) + (if i = (⟨k + 1, hk⟩ : Fin N) then 1 else 0)
          = if i.val ≤ k + 1 then 1 else 0
      by_cases h1 : i.val ≤ k
      · rw [if_pos h1, if_neg (fun he => by have hv : i.val = k + 1 := congrArg Fin.val he; omega),
            if_pos (by omega)]
      · by_cases h2 : i.val = k + 1
        · rw [if_neg h1, if_pos (Fin.ext h2), if_pos (by omega)]
        · rw [if_neg h1, if_neg (fun he => h2 (congrArg Fin.val he)), if_neg (by omega)]

/-- Corollary: every `degreeY` of a tower relation is `≤ 1`. -/
theorem degreeY_prodVarYUpTo_le_one {N : Nat} (i : Fin N) (k : Nat) (hk : k < N) :
    MultiPoly.degreeY i (prodVarYUpTo k hk) ≤ 1 := by
  rw [degreeY_prodVarYUpTo_eq i k hk]; split <;> omega

/-- **degreeY grows by at most 1 under `chainTotalDeriv`** (iterated-exp chain, any index). Structural
mirror of `degreeY0_chainTotalDeriv_le`: each `varY j` becomes `prodVarYUpTo j` (`degreeY ≤ 1`), the `+1`
slack absorbing it; the product rule keeps the bound additive. -/
theorem degreeY_chainTotalDeriv_iterExp_growth {n : Nat} (i : Fin n) :
    ∀ q : MultiPoly n,
      MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) q) ≤ MultiPoly.degreeY i q + 1
  | .const _ => Nat.zero_le _
  | .varX => Nat.zero_le _
  | .varY j => by
      show MultiPoly.degreeY i (prodVarYUpTo j.val j.isLt) ≤ MultiPoly.degreeY i (MultiPoly.varY j) + 1
      exact Nat.le_trans (degreeY_prodVarYUpTo_le_one i j.val j.isLt) (by omega)
  | .add p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) p))
              (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) q))
          ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact Nat.le_trans (degreeY_chainTotalDeriv_iterExp_growth i p)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · exact Nat.le_trans (degreeY_chainTotalDeriv_iterExp_growth i q)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | .sub p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) p))
              (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) q))
          ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact Nat.le_trans (degreeY_chainTotalDeriv_iterExp_growth i p)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · exact Nat.le_trans (degreeY_chainTotalDeriv_iterExp_growth i q)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | .mul p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) p) + MultiPoly.degreeY i q)
              (MultiPoly.degreeY i p + MultiPoly.degreeY i (chainTotalDeriv (IterExpChain n) q))
          ≤ MultiPoly.degreeY i p + MultiPoly.degreeY i q + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · have := degreeY_chainTotalDeriv_iterExp_growth i p; omega
      · have := degreeY_chainTotalDeriv_iterExp_growth i q; omega

/-- `liftLastY` preserves the `degreeY` of a below-top index (the variable is re-embedded at the same val). -/
theorem degreeY_liftLastY_low' {n : Nat} (i : Fin (n + 1)) (hi : i.val < n) :
    ∀ x : MultiPoly n,
      MultiPoly.degreeY i (MultiPoly.liftLastY x) = MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) x
  | .const _ => rfl
  | .varX => rfl
  | .varY j => by
      show (if i = (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) then 1 else 0)
          = (if (⟨i.val, hi⟩ : Fin n) = j then 1 else 0)
      by_cases h : i.val = j.val
      · rw [if_pos (show i = (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) from Fin.ext h),
            if_pos (show (⟨i.val, hi⟩ : Fin n) = j from Fin.ext h)]
      · rw [if_neg (show ¬ i = (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) from
              fun he => h (congrArg Fin.val he)),
            if_neg (show ¬ (⟨i.val, hi⟩ : Fin n) = j from
              fun he => h (congrArg Fin.val he))]
  | .add p q => by
      show Nat.max (MultiPoly.degreeY i (MultiPoly.liftLastY p)) (MultiPoly.degreeY i (MultiPoly.liftLastY q))
          = Nat.max (MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) p) (MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) q)
      rw [degreeY_liftLastY_low' i hi p, degreeY_liftLastY_low' i hi q]
  | .sub p q => by
      show Nat.max (MultiPoly.degreeY i (MultiPoly.liftLastY p)) (MultiPoly.degreeY i (MultiPoly.liftLastY q))
          = Nat.max (MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) p) (MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) q)
      rw [degreeY_liftLastY_low' i hi p, degreeY_liftLastY_low' i hi q]
  | .mul p q => by
      show MultiPoly.degreeY i (MultiPoly.liftLastY p) + MultiPoly.degreeY i (MultiPoly.liftLastY q)
          = MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) p + MultiPoly.degreeY (⟨i.val, hi⟩ : Fin n) q
      rw [degreeY_liftLastY_low' i hi p, degreeY_liftLastY_low' i hi q]

/-- The graded multiplier has every `degreeY ≤ 1` (`Ffac M` is a tower relation). -/
theorem degreeY_gradedTop_le_one (M : Nat) (j : Fin (M + 2)) (q : MultiPoly (M + 2)) (i : Fin (M + 2)) :
    MultiPoly.degreeY i (gradedTop M j q) ≤ 1 := by
  show (0 : Nat) + MultiPoly.degreeY i (Ffac M) ≤ 1
  rw [Nat.zero_add]
  exact degreeY_prodVarYUpTo_le_one i M (by omega)

/-- **The reduce multiplier `fullMult M q` has every `degreeY ≤ 1`** (induction on depth): each level is a
graded top term (`≤ 1`) plus the `liftLastY` of the lower multiplier (`≤ 1` by IH, index-preserved). -/
theorem degreeY_fullMult_le_one : ∀ (M : Nat) (q : MultiPoly (M + 2)) (i : Fin (M + 2)),
    MultiPoly.degreeY i (fullMult M q) ≤ 1
  | 0, q, i => by
      show Nat.max (MultiPoly.degreeY i (gradedTop 0 (⟨1, by omega⟩ : Fin 2) q))
          (MultiPoly.degreeY i (MultiPoly.const (MachLib.Real.natCast
            (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))))) ≤ 1
      refine Nat.max_le.mpr ⟨degreeY_gradedTop_le_one 0 _ q i, ?_⟩
      show (0 : Nat) ≤ 1
      omega
  | M + 1, q, i => by
      show Nat.max (MultiPoly.degreeY i (gradedTop (M + 1) (⟨M + 2, by omega⟩ : Fin (M + 3)) q))
          (MultiPoly.degreeY i (MultiPoly.liftLastY (fullMult M (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) q))))) ≤ 1
      refine Nat.max_le.mpr ⟨degreeY_gradedTop_le_one (M + 1) _ q i, ?_⟩
      by_cases hi : i.val < M + 2
      · rw [degreeY_liftLastY_low' i hi]
        exact degreeY_fullMult_le_one M _ ⟨i.val, hi⟩
      · have hz : MultiPoly.degreeY i (MultiPoly.liftLastY (fullMult M (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) q)))) = 0 := by
          rw [show i = (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3)) from
            Fin.ext (show i.val = M + 2 from by omega)]
          exact degreeY_top_liftLastY _
        rw [hz]; omega

/-- **The reduce grows any `degreeY` by at most 1**, given an `x`-multiplier with that `degreeY ≤ 1`:
`chainNReduce M m p = cTD(p) − m·p`, the cTD term by the growth lemma, the product term by `degreeY m ≤ 1`. -/
theorem degreeY_chainNReduce_growth_le (M : Nat) (m p : MultiPoly (M + 2)) (i : Fin (M + 2))
    (hm : MultiPoly.degreeY i m ≤ 1) :
    MultiPoly.degreeY i (chainNReduce M m p) ≤ MultiPoly.degreeY i p + 1 := by
  unfold chainNReduce
  refine Nat.max_le.mpr ⟨degreeY_chainTotalDeriv_iterExp_growth i p, ?_⟩
  show MultiPoly.degreeY i m + MultiPoly.degreeY i p ≤ MultiPoly.degreeY i p + 1
  omega

/-- The actual reduce (multiplier `fullMult M p`) grows any `degreeY` by at most 1. -/
theorem degreeY_chainNReduce_fullMult_growth_le (M : Nat) (p : MultiPoly (M + 2)) (i : Fin (M + 2)) :
    MultiPoly.degreeY i (chainNReduce M (fullMult M p) p) ≤ MultiPoly.degreeY i p + 1 :=
  degreeY_chainNReduce_growth_le M (fullMult M p) p i (degreeY_fullMult_le_one M p i)

end MachLib.IterExpDepthN
