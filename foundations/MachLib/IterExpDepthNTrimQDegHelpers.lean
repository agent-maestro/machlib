import MachLib.IterExpDepthNDegreeYTrimLift
import MachLib.IterExpDepthNEstablishHnz
import MachLib.IterExpDepthNDegreeX
import MachLib.IterExpDepthNDegreeY
import MachLib.IterExpDepthNAssembly
import MachLib.ChainExp2ExplicitABound

/-!
# Chain-N explicit bound — degree-chaining helpers for the `q'` (phantom-trim) degree bounds

The lift arm needs the phantom-trim `q'` from `establish_hnz_or_trim` to be degree-bounded by `q`. `q'` is
one of `dropLeadingYAt`, `liftInner k q inner'`, `liftLastY inner'` (with `inner'` degree-bounded by
`dropLastY(lcY_top q)` recursively). These helpers chain those shapes' degrees back to `q`:

  * `degreeX_inner_le` / `degreeY_inner_le` — `dropLastY(lcY_top q)`'s degrees `≤ q`'s.
  * `degreeX/Y_liftInner_q_le`, `degreeX/Y_liftLastY_q_le` — the reconstruction shapes, given `inner'` bounds.
  * `degreeY_dropLeadingYAt_le_all` — the trim shape, all indices (using `_lt` at the trim index).
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ChainExp2Explicit
open MachLib.ChainExp2Trim

/-- `dropLastY(lcY_top q)`'s `degreeX ≤ degreeX q`. -/
theorem degreeX_inner_le (k : Nat) (q : MultiPoly (k + 3)) :
    degreeX (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) ≤ degreeX q := by
  rw [degreeX_dropLastY]
  exact degreeX_leadingCoeffY_le (⟨k + 2, by omega⟩ : Fin (k + 3)) q

/-- `dropLastY(lcY_top q)`'s `degreeY jt' ≤ degreeY (embed jt') q`. -/
theorem degreeY_inner_le (k : Nat) (q : MultiPoly (k + 3)) (jt' : Fin (k + 2)) :
    degreeY jt' (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
      ≤ degreeY (⟨jt'.val, Nat.lt_succ_of_lt jt'.isLt⟩ : Fin (k + 3)) q := by
  rw [degreeY_dropLastY_eq_prev (k + 2) (⟨jt'.val, Nat.lt_succ_of_lt jt'.isLt⟩ : Fin (k + 3)) jt' rfl]
  exact degreeY_leadingCoeffY_le (⟨k + 2, by omega⟩ : Fin (k + 3))
    (⟨jt'.val, Nat.lt_succ_of_lt jt'.isLt⟩ : Fin (k + 3)) q

/-- `liftInner k q inner'`'s `degreeX ≤ degreeX q`, given `inner'` bounded by the inner poly. -/
theorem degreeX_liftInner_q_le (k : Nat) (q : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hinX : degreeX inner' ≤ degreeX (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) :
    degreeX (liftInner k q inner') ≤ degreeX q := by
  refine Nat.le_trans (degreeX_liftInner_le k q inner') (Nat.max_le.mpr ⟨Nat.le_refl _, ?_⟩)
  exact Nat.le_trans hinX (degreeX_inner_le k q)

/-- `liftInner k q inner'`'s `degreeY jt ≤ degreeY jt q` (all `jt`), given `inner'` bounded. -/
theorem degreeY_liftInner_q_le (k : Nat) (q : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hinY : ∀ jt' : Fin (k + 2), degreeY jt' inner'
      ≤ degreeY jt' (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) :
    ∀ jt : Fin (k + 3), degreeY jt (liftInner k q inner') ≤ degreeY jt q := by
  intro jt
  by_cases hjt : jt = (⟨k + 2, by omega⟩ : Fin (k + 3))
  · subst hjt; exact Nat.le_of_eq (degreeYtop_liftInner k q inner')
  · refine Nat.le_trans (degreeY_liftInner_le_ne k jt hjt q inner') (Nat.max_le.mpr ⟨Nat.le_refl _, ?_⟩)
    have hjtlt : jt.val < k + 2 := by
      have h1 := jt.isLt
      have h2 : jt.val ≠ k + 2 := fun h => hjt (Fin.ext h)
      omega
    rw [degreeY_liftLastY_low' jt hjtlt inner']
    exact Nat.le_trans (hinY ⟨jt.val, hjtlt⟩) (Nat.le_trans (degreeY_inner_le k q ⟨jt.val, hjtlt⟩)
      (Nat.le_of_eq (congrArg (fun i => degreeY i q)
        (Fin.ext rfl : (⟨jt.val, Nat.lt_succ_of_lt hjtlt⟩ : Fin (k + 3)) = jt))))

/-- `liftLastY inner'`'s `degreeX ≤ degreeX q`, given `inner'` bounded. -/
theorem degreeX_liftLastY_q_le (k : Nat) (q : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hinX : degreeX inner' ≤ degreeX (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) :
    degreeX (liftLastY inner') ≤ degreeX q := by
  rw [degreeX_liftLastY]
  exact Nat.le_trans hinX (degreeX_inner_le k q)

/-- `liftLastY inner'`'s `degreeY jt ≤ degreeY jt q` (all `jt`), given `inner'` bounded. -/
theorem degreeY_liftLastY_q_le (k : Nat) (q : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hinY : ∀ jt' : Fin (k + 2), degreeY jt' inner'
      ≤ degreeY jt' (dropLastY (leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) :
    ∀ jt : Fin (k + 3), degreeY jt (liftLastY inner') ≤ degreeY jt q := by
  intro jt
  by_cases hjt : jt.val < k + 2
  · rw [degreeY_liftLastY_low' jt hjt inner']
    exact Nat.le_trans (hinY ⟨jt.val, hjt⟩) (Nat.le_trans (degreeY_inner_le k q ⟨jt.val, hjt⟩)
      (Nat.le_of_eq (congrArg (fun i => degreeY i q)
        (Fin.ext rfl : (⟨jt.val, Nat.lt_succ_of_lt hjt⟩ : Fin (k + 3)) = jt))))
  · have hjtop : jt = (⟨k + 2, Nat.lt_succ_self (k + 2)⟩ : Fin (k + 3)) :=
      Fin.ext (show jt.val = k + 2 by have := jt.isLt; omega)
    rw [hjtop, degreeY_top_liftLastY]
    exact Nat.zero_le _

/-- `dropLeadingYAt i q`'s `degreeY jt ≤ degreeY jt q` for ALL `jt` (using `_lt` at the trim index `i`,
which needs `degreeY i q > 0`). -/
theorem degreeY_dropLeadingYAt_le_all {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hpos : 0 < degreeY i q) : ∀ jt : Fin n, degreeY jt (dropLeadingYAt i q) ≤ degreeY jt q := by
  intro jt
  by_cases hjt : jt = i
  · subst hjt; exact Nat.le_of_lt (degreeY_dropLeadingYAt_lt jt q hpos)
  · exact degreeY_dropLeadingYAt_le_ne i jt hjt q

open MachLib.Real
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CdegY1
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2NoZeros
open MachLib.ChainExp2Capstone

/-- **`establish_hnz_or_trim` strengthened with `q'`'s degree bounds.** Same dichotomy, but the phantom-trim
`q'` (a `dropLeadingYAt`/`liftInner`/`liftLastY`) additionally has `degreeX`/`degreeY` bounded by `q`'s —
what the lift arm of the outer WF wrap needs. Recursion mirrors `establish_hnz_or_trim`, threading the
degree bounds through the four `q'` shapes via the helpers above. -/
theorem establish_hnz_or_trim_deg : ∀ (k : Nat) (q : MultiPoly (k + 2)), canonZeroB q = false →
    hnzTower k q ∨ ∃ q' : MultiPoly (k + 2),
      (∀ (x : Real) (env : Fin (k + 2) → Real), MultiPoly.eval q' x env = MultiPoly.eval q x env)
        ∧ synOrder k q' q
        ∧ MultiPoly.degreeX q' ≤ MultiPoly.degreeX q
        ∧ (∀ jt : Fin (k + 2), MultiPoly.degreeY jt q' ≤ MultiPoly.degreeY jt q) := by
  intro k
  induction k with
  | zero =>
    intro q hq
    by_cases hnz : hnzTower 0 q
    · exact Or.inl hnz
    · right
      have hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 = 0 := by
        rcases Nat.eq_zero_or_pos
          (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 with h | h
        · exact h
        · exact absurd (Nat.pos_iff_ne_zero.mp h) hnz
      have hlc0 : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) x env = 0 :=
        smc2_zero_eval_zero _ (MultiPoly.degreeY_leadingCoeffY _ _) hcz
      have hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
        rcases Nat.eq_zero_or_pos (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) with hd0 | hp
        · exfalso
          have hqself := leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) q hd0
          have hq0 : canonZeroB q = true :=
            canonZeroB_true_of_eval_zero q (fun x env => by rw [← hqself]; exact hlc0 x env)
          rw [hq0] at hq; exact absurd hq (by decide)
        · exact hp
      have hlast : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) q
              (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q) x env]
        exact hlc0 x env
      refine ⟨dropLeadingYAt (⟨1, by omega⟩ : Fin 2) q,
        fun x env => eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q) hlast x env,
        nestedOrder_of_fst (degreeY_dropLeadingYAt_lt (⟨1, by omega⟩ : Fin 2) q hpos),
        degreeX_dropLeadingYAt_le _ q,
        degreeY_dropLeadingYAt_le_all (⟨1, by omega⟩ : Fin 2) q hpos⟩
  | succ k ih =>
    intro q hq
    by_cases hnz : hnzTower (k + 1) q
    · exact Or.inl hnz
    · right
      by_cases htop : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false
      · have hinner_nz : canonZeroB (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) = false := by
          cases h : canonZeroB (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
          · rfl
          · exfalso
            have hlc0 := dropLastY_eval_zero_of_yfree
              (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
              (MultiPoly.degreeY_leadingCoeffY _ _) ((canonZeroB_true_iff _).mp h)
            rw [canonZeroB_true_of_eval_zero _ hlc0] at htop; exact absurd htop (by decide)
        rcases ih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
          hinner_nz with hin | ⟨inner', hin_eval, hin_syn, hin_degX, hin_degY⟩
        · exact absurd hin hnz
        · have hswap : ∀ (x : Real) (env : Fin (k + 3) → Real),
              MultiPoly.eval (liftLastY inner') x env
                = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q).getLast
                  (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) x env := by
            intro x env
            rw [eval_liftLastY inner' x env, hin_eval x _,
                eval_dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
                  (MultiPoly.degreeY_leadingCoeffY _ _) x env]
            exact eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
              (⟨k + 2, by omega⟩ : Fin (k + 3)) q
              (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q) x env
          by_cases hdpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
          · refine ⟨liftInner k q inner', fun x env => eval_liftInner k q inner' hswap x env, ?_,
              degreeX_liftInner_q_le k q inner' hin_degX,
              degreeY_liftInner_q_le k q inner' hin_degY⟩
            show nestedOrder (k + 3) (synMeasure (k + 1) (liftInner k q inner')) (synMeasure (k + 1) q)
            rw [synMeasure_liftInner k q inner' hdpos]
            exact nestedOrder_of_snd rfl hin_syn
          · have hd0 : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q = 0 :=
              Nat.le_zero.mp (Nat.not_lt.mp hdpos)
            refine ⟨liftLastY inner', fun x env => ?_, ?_,
              degreeX_liftLastY_q_le k q inner' hin_degX,
              degreeY_liftLastY_q_le k q inner' hin_degY⟩
            · rw [hswap x env]
              exact (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
                (⟨k + 2, by omega⟩ : Fin (k + 3)) q
                (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q) x env).symm.trans
                (by rw [leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) q hd0])
            · show nestedOrder (k + 3) (synMeasure (k + 1) (liftLastY inner')) (synMeasure (k + 1) q)
              rw [synMeasure_liftLastY k inner']
              refine nestedOrder_of_snd (by simp only [synMeasure]; rw [hd0]) ?_
              exact hin_syn
      · have htop_ph : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = true := by
          cases h : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
          · exact absurd h htop
          · rfl
        have hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q := by
          rcases Nat.eq_zero_or_pos (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) with hd0 | hp
          · exfalso
            have hqself := leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) q hd0
            rw [hqself] at htop_ph
            rw [htop_ph] at hq; exact absurd hq (by decide)
          · exact hp
        have hlast : ∀ (x : Real) (env : Fin (k + 3) → Real),
            MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q).getLast
              (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) x env = 0 := by
          intro x env
          rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨k + 2, by omega⟩ : Fin (k + 3)) q
                (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q) x env]
          exact (canonZeroB_true_iff _).mp htop_ph x env
        refine ⟨dropLeadingYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
          fun x env => eval_dropLeadingYAt_of_last_canonically_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) q
            (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q) hlast x env,
          nestedOrder_of_fst (degreeY_dropLeadingYAt_lt (⟨k + 2, by omega⟩ : Fin (k + 3)) q hpos),
          degreeX_dropLeadingYAt_le _ q,
          degreeY_dropLeadingYAt_le_all (⟨k + 2, by omega⟩ : Fin (k + 3)) q hpos⟩

end MachLib.IterExpDepthN
