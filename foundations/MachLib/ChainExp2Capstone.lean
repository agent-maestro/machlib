import MachLib.ChainExp2Bound
import MachLib.ChainExp2PhantomDescent
import MachLib.ChainExp2PathC

/-!
# Seam C — buildChain2Reducer + the chain-2 Khovanskii bound

Assembles the descent (`chain2Reduce_nestedLT_canon`) + the trim + the chain-2 zero-count bound
(`chain2_zero_count_bound`) into: every `p` reduces (by well-founded recursion on `chain2OrderCanon`) to a
`y₁`-free `g`, so `#zeros(chain2Fn p) ≤ (#zeros bound of g) + k`. Conditional on the `y₁`-free base bound
(single-exp finiteness); the base bridge is the last piece.

Path B: single-exp framework + `ChainExp2SDR` untouched.
-/

namespace MachLib.ChainExp2Capstone

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Reducer
open MachLib.PolynomialCanonical
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2SingleExpDescent
open MachLib.ChainExp2CTDCongr
open MachLib.ChainExp2YPIT
open MachLib.ChainExp2PhantomDescent
open MachLib.ChainExp2Bound
open MachLib.ChainExp2PathC

/-! ### The `(smc q).2 = 0 → eval q ≡ 0` bridge (for the trim's eval-equality) -/

/-- The head of a `dropWhile` fails the predicate. -/
private theorem dropWhile_head_neg {α : Type} (p : α → Bool) :
    ∀ (M : List α) (a : α) (rest : List α), M.dropWhile p = a :: rest → p a = false
  | [], a, rest, h => by simp at h
  | c :: cs, a, rest, h => by
    rw [List.dropWhile_cons] at h
    cases hpc : p c with
    | true => rw [hpc, if_pos rfl] at h; exact dropWhile_head_neg p cs a rest h
    | false =>
      rw [hpc, if_neg (by simp)] at h
      injection h with hca _
      rw [← hca]; exact hpc

/-- If `dropWhile p M = []` then every entry of `M` satisfies `p`. -/
private theorem dropWhile_nil_all {α : Type} (p : α → Bool) :
    ∀ (M : List α), M.dropWhile p = [] → ∀ c ∈ M, p c = true
  | [], _, c, hc => absurd hc (List.not_mem_nil c)
  | a :: as, h, c, hc => by
    rw [List.dropWhile_cons] at h
    cases hpa : p a with
    | false => rw [hpa, if_neg (by simp)] at h; simp at h
    | true =>
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hpa
      · rw [hpa, if_pos rfl] at h; exact dropWhile_nil_all p as h c hc'

/-- Horner evaluation of a list all of whose entries evaluate to `0` is `0`. -/
private theorem listEvalAuxN_zero_of_entries_zero {n : Nat} (i : Fin n) (L : List (MultiPoly n))
    (x : Real) (env : Fin n → Real) (hL : ∀ c ∈ L, MultiPoly.eval c x env = 0) (k : Nat) :
    listEvalAuxN i L k x env = 0 := by
  induction L generalizing k with
  | nil => rfl
  | cons c cs ih =>
    show MultiPoly.eval c x env * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env
           + listEvalAuxN i cs (k + 1) x env = 0
    rw [hL c (List.mem_cons_self _ _),
        ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')) (k + 1)]
    mach_ring

/-- **If `q`'s canonical inner second component is `0`, `q` evaluates to `0` everywhere** (for `y₁`-free
`q`). `(smc q).2 = 0` means `canonLcY0 q` is canonically zero, which forces the whole `dropWhile` to be
empty, i.e. every `y₀`-coefficient of `q` is canonically zero; each is `y`-free, so eval-vanishes at every
env; the Horner sum is `0`. -/
theorem smc2_zero_eval_zero (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0)
    (h : (singleExpMeasureCanon q).2 = 0) :
    ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q x env = 0 := by
  -- (smc q).2 = 0 ⇒ canonLcY0 q canonically zero.
  have h' : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q))) = 0 := h
  have hcanon_cz : coeffCanonZeroB (canonLcY0 q) = true := by
    show decide (CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))) = true
    rw [decide_eq_true_iff]
    by_cases hcz : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
    · exact hcz
    · exfalso; rw [polyTrueDegreeStrict_of_not_canonicallyZero _ hcz] at h'; omega
  -- ⇒ the dropWhile is empty ⇒ all yCoeffsAt entries canonically zero.
  have hall : ∀ c ∈ MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q, coeffCanonZeroB c = true := by
    have hnil : (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB = [] := by
      rcases hdw : (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB
        with _ | ⟨a, rest⟩
      · rfl
      · exfalso
        have hpa : coeffCanonZeroB a = false :=
          dropWhile_head_neg coeffCanonZeroB _ a rest hdw
        have hcl : canonLcY0 q = a := by unfold canonLcY0; rw [hdw]; rfl
        rw [hcl, hpa] at hcanon_cz
        simp at hcanon_cz
    intro c hc
    exact dropWhile_nil_all coeffCanonZeroB _ hnil c (List.mem_reverse.mpr hc)
  -- each entry is y-free ⇒ eval-vanishes everywhere.
  intro x env
  rw [← eval_yCoeffsAt (⟨0, by omega⟩ : Fin 2) q x env]
  show listEvalAuxN (⟨0, by omega⟩ : Fin 2) (MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q) 0 x env = 0
  apply listEvalAuxN_zero_of_entries_zero
  intro c hc
  have hc0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) c = 0 :=
    yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) q c hc
  have hc1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c = 0 :=
    yCoeffsAt0_entries_degreeY1_zero q hy1 c hc
  have hcz : ∀ y : Real, MultiPoly.eval c y (fun _ => 0) = 0 := by
    have := hall c hc; unfold coeffCanonZeroB at this
    exact fun y => (canonZero_iff_eval_zero_at_0 c).mp (of_decide_eq_true this) y
  -- env-independence (c is y-free): eval c x env = eval c x 0 = 0.
  have hstep0 : MultiPoly.eval c x env
              = MultiPoly.eval c x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) := by
    apply eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) c x env _ _ hc0
    intro j hj; show env j = (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j); rw [if_neg hj]
  have hstep1 : MultiPoly.eval c x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j)
              = MultiPoly.eval c x (fun _ => 0) := by
    apply eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) c x _ (fun _ => 0) _ hc1
    intro j hj
    show (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) = 0
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin 2)
    · rw [if_pos hj0]
    · exfalso
      have h0 : j.val ≠ 0 := fun hv => hj0 (Fin.ext hv)
      have h1 : j.val ≠ 1 := fun hv => hj (Fin.ext hv)
      have := j.isLt; omega
  rw [hstep0, hstep1]; exact hcz x

/-! ### The trim step's eval-equality and measure descent -/

/-- The trim's last-`y₁`-coefficient vanishes everywhere (from `(smc (lcY₁ p)).2 = 0`). -/
private theorem chain2_trim_last_zero (p : MultiPoly 2)
    (hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0) :
    ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).getLast
        (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p)) x env = 0 := by
  intro x env
  rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) p
        (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p) x env]
  exact smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
    (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz x env

/-- Trim eval-equality: `chain2Fn p` and `chain2Fn (dropLeadingYAt ⟨1⟩ p)` agree everywhere. -/
theorem chain2_trim_eval (p : MultiPoly 2)
    (hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0) :
    ∀ z : Real, (chain2Fn p).eval z = (chain2Fn (MachLib.ChainExp2Trim.dropLeadingYAt
      (⟨1, by omega⟩ : Fin 2) p)).eval z := by
  intro z
  exact (MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero
    (⟨1, by omega⟩ : Fin 2) p (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p)
    (chain2_trim_last_zero p hcz) z ((IterExpChain 2).chainValues z)).symm

/-- Trim measure descent: `dropLeadingYAt ⟨1⟩ p` drops the first (`degreeY₁`) component. -/
theorem chain2_trim_order (p : MultiPoly 2)
    (hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≠ 0) :
    chain2OrderCanon (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) p := by
  refine Or.inl ?_
  exact MachLib.ChainExp2Trim.degreeY_dropLeadingYAt_lt (⟨1, by omega⟩ : Fin 2) p
    (Nat.pos_of_ne_zero hd1)

/-! ### buildChain2Reducer — every `p` reduces to a `y₁`-free `g` -/

/-- **buildChain2Reducer.** By well-founded recursion on `chain2OrderCanon`, every `p` reduces (via
poly-multiplier reduces and trims) to a `y₁`-free `g`. Dispatch: `degreeY₁ = 0` → done; else
`lcY₁ p` canonically zero → trim (`degreeY₁` drops); else → reduce (`chain2Reduce_nestedLT_canon`). -/
theorem buildChain2Reducer (p : MultiPoly 2) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0
      ∧ Chain2Reducible p g k := by
  refine WellFounded.induction
    (C := fun q => ∃ (g : MultiPoly 2) (k : Nat),
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧ Chain2Reducible q g k)
    chain2OrderCanon_wf p ?_
  intro p ih
  by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0
  · exact ⟨p, 0, hd1, Chain2Reducible.refl p⟩
  · by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0
    · -- trim
      obtain ⟨g, k, hg, hwit⟩ :=
        ih (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) (chain2_trim_order p hd1)
      exact ⟨g, k, hg, Chain2Reducible.congr p _ g k (chain2_trim_eval p hcz) hwit⟩
    · -- reduce
      obtain ⟨g, k, hg, hwit⟩ :=
        ih (chain2Reduce (MachLib.Real.natCast
              (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p)
          (chain2Reduce_nestedLT_canon p hcz)
      exact ⟨g, k + 1, hg, Chain2Reducible.reduce p g k _ hwit⟩

/-! ### The chain-2 bound reduced to the `y₁`-free base -/

/-- **Chain-2 zero counts reduce to the `y₁`-free (single-exp) base.** For every `p` there is a `y₁`-free
`g` and a step count `k` such that any bound `N` on `g`'s zeros gives the bound `N + k` on `p`'s zeros.
Combined with single-exp finiteness of the `y₁`-free `g`, this is a finite Khovanskii bound for chain-2 —
`#print axioms`-clean of `zero_count_bound_classical`. -/
theorem chain2_reduces_to_y1free (p : MultiPoly 2) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ∀ (a b : Real), a < b → ∀ (N : Nat),
        (∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn g).eval z = 0) → zeros.length ≤ N) →
        ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N + k := by
  obtain ⟨g, k, hg, hwit⟩ := buildChain2Reducer p
  exact ⟨g, k, hg, fun a b hab N hN_bound => chain2_zero_count_bound p g k hwit a b hab N hN_bound⟩

/-! ### The `y₁`-free base bound (single-exp integration) -/

/-- `(IterExpChain 2).dropLast` and `SingleExpChain` have the same chain values (both `y₀ = eˣ`). -/
theorem iterExp2_dropLast_chainValues (z : Real) :
    (PfaffianChainMod.PfaffianChain.dropLast (IterExpChain 2)).chainValues z
      = SingleExpChain.chainValues z := by
  funext i
  show (IterExpChain 2).evals ⟨i.val, by omega⟩ z = Real.exp z
  rw [IterExpChain_evals]
  show iterExp i.val z = Real.exp z
  have hi : i.val = 0 := by have := i.isLt; omega
  rw [hi]; rfl

/-- Along the chain, `chain2Fn g` (with `g` `y₁`-free) equals the single-exp function
`⟨1, SingleExpChain, dropLastY g⟩`. -/
theorem chain2Fn_y1free_eval_eq_singleExp (g : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0) (z : Real) :
    (chain2Fn g).eval z
      = (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn).eval z := by
  rw [← PfaffianFn.dropLast_eval (chain2Fn g) rfl hy1 z]
  show MultiPoly.eval (MultiPoly.dropLastY g) z
        ((PfaffianChainMod.PfaffianChain.dropLast (IterExpChain 2)).chainValues z)
     = MultiPoly.eval (MultiPoly.dropLastY g) z (SingleExpChain.chainValues z)
  rw [iterExp2_dropLast_chainValues]

/-- **The `y₁`-free base bound.** A `y₁`-free `g` is a single exponential; its zero count is bounded by
the (already dirty-axiom-clean) single-exp Khovanskii bound, given the standard non-vanishing/terminal
condition. Transferred to `chain2Fn g` via the chain equality. -/
theorem base_bound_y1free (g : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0)
    (sdr_other : PfaffianFn.StepwiseDecreaseReducer) (a b : Real) (hab : a < b)
    (h_term : ∀ g' k, g'.n = 0 →
       PfaffianFn.IsKhovanskiiReducible
         (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' k →
       ∃ x : Real, g'.eval x ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn g).eval z = 0) → zeros.length ≤ N := by
  obtain ⟨N, hN⟩ := singleExp_khovanskii_bound (MultiPoly.dropLastY g) sdr_other a b hab h_term
  refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z hzmem
  exact ⟨ha, hb', by rw [← chain2Fn_y1free_eval_eq_singleExp g hy1 z]; exact hzero⟩

/-- **Chain-2 Khovanskii bound (assembled).** For every chain-2 `p` there is a `y₁`-free single-exp
reduct `g` and step count `k` such that, given the standard non-vanishing/terminal condition on `g`,
`p`'s zeros are finitely bounded — `#print axioms`-clean of `zero_count_bound_classical`. -/
theorem chain2_khovanskii_bound (p : MultiPoly 2)
    (sdr_other : PfaffianFn.StepwiseDecreaseReducer) (a b : Real) (hab : a < b) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N) := by
  obtain ⟨g, k, hg, hred⟩ := chain2_reduces_to_y1free p
  refine ⟨g, k, hg, fun h_term => ?_⟩
  obtain ⟨N, hN⟩ := base_bound_y1free g hg sdr_other a b hab h_term
  exact ⟨N + k, fun zeros hnd hz => hred a b hab N hN zeros hnd hz⟩

end MachLib.ChainExp2Capstone
