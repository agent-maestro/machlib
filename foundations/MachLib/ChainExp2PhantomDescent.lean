import MachLib.ChainExp2SingleExpDescent
import MachLib.ChainExp2CTDCongr
import MachLib.ChainExp2Trim
import MachLib.ChainExp2Descent

/-!
# The phantom-top reduce descent (Seam A.5) — general reduce descent via `dropLeadingYAt` + Seam A

The htop reduce descent (`chain2Reduce_nestedLT_canon_htop`) handles the case where `lcY₁ p`'s top
`y₀`-coefficient is not canonically zero. This file lifts it to the **general** case (any `lcY₁ p` that is
not canonically zero), including the phantom-top case that arises from non-canonical `lcY₁` ASTs of prior
reduces. The tool is `chainTotalDeriv` eval-congruence (Seam A): a phantom top `y₀`-term of `lcY₁ p` is
canonically zero, so dropping it (`dropLeadingYAt ⟨0⟩`) is eval-preserving, and the reduce of the trimmed
poly is eval-equal to the reduce of `lcY₁ p` — bridged by cTD-congruence. Strong induction on `degreeY₀`
peels phantom tops until htop holds.

Path B: `ChainExp2SDR` + single-exp untouched.
-/

namespace MachLib.ChainExp2PhantomDescent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR
open MachLib.PolynomialCanonical
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2SingleExpDescent
open MachLib.ChainExp2CTDCongr
open MachLib.ChainExp2YPIT
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2Descent

/-! ### `y₁`-freeness is preserved by the `y₀`-machinery -/

/-- The `y₀`-coefficients of a `y₁`-free poly are themselves `y₁`-free (cross-index version of
`yCoeffsAt_entries_degreeY_zero`; the list ops are index-generic, so they carry `degreeY ⟨1⟩`). -/
theorem yCoeffsAt0_entries_degreeY1_zero (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    ∀ c ∈ MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q,
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c = 0 := by
  induction q with
  | const c =>
    intro _ c' hc'
    change c' ∈ ([MultiPoly.const c] : List (MultiPoly 2)) at hc'
    cases hc' with
    | head => rfl
    | tail _ h => exact absurd h (List.not_mem_nil _)
  | varX =>
    intro _ c' hc'
    change c' ∈ ([MultiPoly.varX] : List (MultiPoly 2)) at hc'
    cases hc' with
    | head => rfl
    | tail _ h => exact absurd h (List.not_mem_nil _)
  | varY j =>
    intro hy1 c' hc'
    by_cases hji : j = (⟨0, by omega⟩ : Fin 2)
    · change c' ∈ (if j = (⟨0, by omega⟩ : Fin 2)
                    then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly 2))
                    else ([MultiPoly.varY j] : List (MultiPoly 2))) at hc'
      simp [hji] at hc'
      cases hc' with
      | inl h => rw [h]; rfl
      | inr h => rw [h]; rfl
    · change c' ∈ (if j = (⟨0, by omega⟩ : Fin 2)
                    then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly 2))
                    else ([MultiPoly.varY j] : List (MultiPoly 2))) at hc'
      rw [if_neg hji, List.mem_singleton] at hc'
      rw [hc']
      exact hy1
  | add p q ihp ihq =>
    intro hy1 c hc
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_left _ _
      have : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_right _ _
      have : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      omega
    change c ∈ listAddN (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) p)
                        (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q) at hc
    exact listAddN_entries_degreeY_zero (⟨1, by omega⟩ : Fin 2) _ _ (ihp hp1) (ihq hq1) c hc
  | sub p q ihp ihq =>
    intro hy1 c hc
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_left _ _
      have : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_right _ _
      have : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      omega
    change c ∈ listSubN (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) p)
                        (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q) at hc
    exact listSubN_entries_degreeY_zero (⟨1, by omega⟩ : Fin 2) _ _ (ihp hp1) (ihq hq1) c hc
  | mul p q ihp ihq =>
    intro hy1 c hc
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
           + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
           + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    change c ∈ listMulN (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) p)
                        (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q) at hc
    exact listMulN_entries_degreeY_zero (⟨1, by omega⟩ : Fin 2) _ _ (ihp hp1) (ihq hq1) c hc

/-- `pow (varY ⟨0⟩) k` is `y₁`-free. -/
private theorem degreeY1_pow_varY0 (k : Nat) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k)
      = 0 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
            (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k')) = 0
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
        + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k') = 0
    rw [ih]
    rfl

/-- `reconstructY ⟨0⟩` of `y₁`-free entries is `y₁`-free. -/
theorem degreeY1_reconstructY0_zero (L : List (MultiPoly 2))
    (hL : ∀ c ∈ L, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c = 0) (k : Nat) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (reconstructY (⟨0, by omega⟩ : Fin 2) L k) = 0 := by
  induction L generalizing k with
  | nil => rw [reconstructY_nil]; rfl
  | cons c cs ih =>
    rw [reconstructY_cons]
    show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                   (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k)))
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                   (reconstructY (⟨0, by omega⟩ : Fin 2) cs (k + 1))) = 0
    have hhead : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                   (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k)) = 0 := by
      show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c
          + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
              (MultiPoly.pow (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) k) = 0
      rw [hL c (List.mem_cons_self _ _), degreeY1_pow_varY0]
    have htail : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                   (reconstructY (⟨0, by omega⟩ : Fin 2) cs (k + 1)) = 0 :=
      ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')) (k + 1)
    rw [hhead, htail]; exact Nat.max_self 0

/-- `dropLeadingYAt ⟨0⟩` preserves `y₁`-freeness. -/
theorem degreeY1_dropLeadingYAt0_zero (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MachLib.ChainExp2Trim.dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) = 0 := by
  show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
        (reconstructY (⟨0, by omega⟩ : Fin 2)
          (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).dropLast 0) = 0
  apply degreeY1_reconstructY0_zero
  intro c hc
  exact yCoeffsAt0_entries_degreeY1_zero q hy1 c (List.dropLast_subset _ hc)

/-! ### The general reduce descent (any not-canonically-zero `q`) -/

/-- The single-exp reduce with the **canonical** multiplier `c = cdegY0 q` (the right choice when `q` has
a phantom top; for htop `q` it agrees with `seReduce`). -/
noncomputable def seReduceCanon (q : MultiPoly 2) : MultiPoly 2 :=
  MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q)
    (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q))) q)

/-- `polyTrueDegreeStrict` of the projected `const 0` is `0`. -/
private theorem trueDeg_mP2PFL_const0_zero :
    polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.const 0 : MultiPoly 2))) = 0 := by
  apply polyTrueDegreeStrict_of_canonicallyZero
  have := coeffCanonZeroB_const0
  unfold coeffCanonZeroB at this
  exact of_decide_eq_true this

/-- The top `y₀`-coefficient of a `y₁`-free `q` is `y`-free (needed to lift `coeffCanonZeroB`'s env-0
condition to all envs for `dropLeadingYAt`). -/
private theorem y0top_yfree (q : MultiPoly 2) (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (y0top q) = 0
    ∧ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (y0top q) = 0 := by
  refine ⟨?_, ?_⟩
  · exact yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) q _
      (List.getLast_mem (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q))
  · exact yCoeffsAt0_entries_degreeY1_zero q hy1 _
      (List.getLast_mem (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q))

/-- **The general single-exp canonical reduce descent** (strong induction on `degreeY₀`): for a `y₁`-free
`q` that is not canonically zero (`(singleExpMeasureCanon q).2 ≠ 0`), the canonical reduce strictly
descends the canonical measure. Phantom tops are peeled by `dropLeadingYAt ⟨0⟩` (eval-preserving) and
bridged by `chainTotalDeriv` eval-congruence (Seam A) until htop holds. -/
theorem singleExpMeasureCanon_seReduceCanon_lt :
    ∀ (D : Nat) (q : MultiPoly 2), MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = D →
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
      (singleExpMeasureCanon q).2 ≠ 0 →
      LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
        (singleExpMeasureCanon (seReduceCanon q)) (singleExpMeasureCanon q) := by
  intro D
  induction D using Nat.strongRecOn with
  | ind D ih =>
    intro q hD hy1 hnz
    by_cases htop : coeffCanonZeroB (y0top q) = false
    · -- htop: canonical multiplier = syntactic multiplier; use the htop descent.
      have hbase_eq : seReduceCanon q = seReduce q := by
        show MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q)
              (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q))) q)
           = MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q)
              (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
                (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) q)
        rw [cdegY0_eq_degreeY0_of_top q htop]
      rw [hbase_eq]
      exact singleExpMeasureCanon_seReduce_lt q hy1 htop
    · -- phantom top: peel one canonically-zero top y₀-term and recurse.
      have htop_true : coeffCanonZeroB (y0top q) = true := by
        cases h : coeffCanonZeroB (y0top q) with
        | false => exact absurd h htop
        | true => rfl
      -- degreeY₀ q > 0 (else canonLcY0 q = const 0, forcing (smc q).2 = 0).
      have hpos : 0 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q :=
        Nat.pos_of_ne_zero (fun hdeg0 => hnz (by
          show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q))) = 0
          rw [canonLcY0_eq_const0_of_top_deg0 q htop_true hdeg0]
          exact trueDeg_mP2PFL_const0_zero))
      -- q' := dropLeadingYAt ⟨0⟩ q, eval-equal to q, smaller degreeY₀, y₁-free.
      let q' := MachLib.ChainExp2Trim.dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q
      have hyfree := y0top_yfree q hy1
      have hcz0 : ∀ (x : Real), MultiPoly.eval (y0top q) x (fun _ => 0) = 0 := by
        have hcanon : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (y0top q))) := by
          have := htop_true; unfold coeffCanonZeroB at this; exact of_decide_eq_true this
        intro x
        exact (canonZero_iff_eval_zero_at_0 (y0top q)).mp hcanon x
      have hlastzero : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).getLast
            (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q)) x env = 0 := by
        intro x env
        show MultiPoly.eval (y0top q) x env = 0
        have hstep0 : MultiPoly.eval (y0top q) x env
                    = MultiPoly.eval (y0top q) x
                        (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) := by
          apply eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) (y0top q) x env _ _ hyfree.1
          intro j hj
          show env j = (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j)
          rw [if_neg hj]
        have hstep1 : MultiPoly.eval (y0top q) x
                        (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j)
                    = MultiPoly.eval (y0top q) x (fun _ => 0) := by
          apply eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) (y0top q) x _ (fun _ => 0) _ hyfree.2
          intro j hj
          show (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) = 0
          by_cases hj0 : j = (⟨0, by omega⟩ : Fin 2)
          · rw [if_pos hj0]
          · exfalso
            have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have h1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
            have := j.isLt
            omega
        rw [hstep0, hstep1]; exact hcz0 x
      have hq'q : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval q' x env = MultiPoly.eval q x env := fun x env =>
        MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero
          (⟨0, by omega⟩ : Fin 2) q (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlastzero x env
      have hqq' : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval q x env = MultiPoly.eval q' x env := fun x env => (hq'q x env).symm
      have hy1' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q' = 0 :=
        degreeY1_dropLeadingYAt0_zero q hy1
      have hdeg' : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q'
                 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q :=
        MachLib.ChainExp2Trim.degreeY_dropLeadingYAt_lt (⟨0, by omega⟩ : Fin 2) q hpos
      have hcd' : cdegY0 q' = cdegY0 q := cdegY0_eq_of_eval_eq q' q hq'q
      have hmeq : singleExpMeasureCanon q' = singleExpMeasureCanon q :=
        singleExpMeasureCanon_eq_of_eval_eq q' q hq'q
      have hnz' : (singleExpMeasureCanon q').2 ≠ 0 := by rw [hmeq]; exact hnz
      -- IH on q'.
      have hih := ih (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q') (hD ▸ hdeg') q' rfl hy1' hnz'
      -- seReduceCanon q ~eval seReduceCanon q' (cTD-congruence + cdegY0 q = cdegY0 q' + eval q = eval q').
      have hred_eq : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval (seReduceCanon q) x env = MultiPoly.eval (seReduceCanon q') x env := by
        intro x env
        show MultiPoly.eval (MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q)
                (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q))) q)) x env
           = MultiPoly.eval (MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q')
                (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q'))) q')) x env
        rw [MultiPoly.eval_sub, MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul,
            MultiPoly.eval_const, MultiPoly.eval_const,
            eval_cTD_congr_y1free q q' hy1 hy1' hqq' x env, hcd', hq'q x env]
      have hred_meq : singleExpMeasureCanon (seReduceCanon q) = singleExpMeasureCanon (seReduceCanon q') :=
        singleExpMeasureCanon_eq_of_eval_eq _ _ hred_eq
      rw [hred_meq, hmeq.symm]
      exact hih

/-! ### The general reduce `nestedLT` descent (closes the phantom-top case) -/

/-- **The canonical `nestedLT` descent of the correct reduce — GENERAL case.** For any `p` whose
`y₁`-leading coefficient is not canonically zero, `chain2Reduce (cdegY0(lcY₁ p)) p` strictly descends the
canonical chain-2 measure. Combines with `chain2Reduce_nestedLT_canon_htop`: this handles the phantom-top
case too (via Seam A), so every non-canonically-zero `lcY₁ p` reduces. -/
theorem chain2Reduce_nestedLT_canon (p : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0) :
    nestedLT
      (chain2MeasureCanon (chain2Reduce
        (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      (chain2MeasureCanon p) := by
  apply chain2Reduce_nestedLT_canon_of_snd
  show LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
        (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chain2Reduce (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p)))
        (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
  have hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
               (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p
  have heq : singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
        (chain2Reduce (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      = singleExpMeasureCanon (seReduceCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) := by
    apply singleExpMeasureCanon_eq_of_eval_eq
    intro x env
    rw [chain2Reduce_lcY1_eval]
    show MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
          - MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
            * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) x env
        = MultiPoly.eval (seReduceCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
    unfold seReduceCanon
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_const]
  rw [heq]
  exact singleExpMeasureCanon_seReduceCanon_lt
    (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
    (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) rfl hy1 hnz

end MachLib.ChainExp2PhantomDescent
