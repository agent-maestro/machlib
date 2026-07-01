import MachLib.ChainExp2LcY0CTD
import MachLib.ChainExp2CanonMeasure
import MachLib.ChainExp2CdegInv

/-!
# The single-exp canonical descent (Piece 3, step 2 — the last deep proof)

Goal: `singleExpMeasureCanon (seReduce q) <ₗ singleExpMeasureCanon q` for a `y₁`-free `q`, where
`seReduce q = cTD₂ q − (degreeY₀ q)·q` is the single-exp reduce with the canonical multiplier
`c = degreeY₀ q`. This is the `hsnd` obligation of `chain2Reduce_nestedLT_canon_of_snd` (once the outer
cancellation `chain2Reduce_lcY1_eval` + eval-invariance move it to the `y₁`-leading coefficient
`q = lcY₁ p`, a genuine single-exp object).

The KEY simplification (why the full `y₀`-coefficient list is NOT needed): the canonical measure only
ever reads the **top** `y₀`-coefficient, and the two identities from `ChainExp2LcY0CTD`
(`degreeY0_cTD_eq_of_y1free` + `leadingCoeffY0_cTD_eval_IterExp2`) pin that top exactly. With
`c = degreeY₀ q` the `d·lcY₀` injection cancels the `c·lcY₀` term, leaving
`lcY₀(seReduce q) ≡ (lcY₀ q)'` (the x-derivative). Then:

* **leading coeff non-constant** → `(lcY₀ q)'` has strictly smaller `trueDeg`, first component (`cdegY0`)
  preserved → descend on the second (`polyTrueDegreeStrict_polyDerivativeCoeffs_lt`);
* **leading coeff constant** → `(lcY₀ q)' ≡ 0` canonically → the top vanishes → `cdegY0` drops.

Path B: single-exp framework + `ChainExp2SDR` untouched.
-/

namespace MachLib.ChainExp2SingleExpDescent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR
open MachLib.PolynomialCanonical
open MachLib.PolynomialRootCount
open MachLib.ChainExp2LcY0CTD
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv

/-- The **single-exp reduce** of a `y₁`-free `q`: `cTD₂ q − (degreeY₀ q)·q`. The scalar multiplier is
`natCast (degreeY₀ q)` — exactly the value that cancels the `y₀`-identity's `d·lcY₀` injection. -/
noncomputable def seReduce (q : MultiPoly 2) : MultiPoly 2 :=
  MultiPoly.sub (chainTotalDeriv (IterExpChain 2) q)
    (MultiPoly.mul
      (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) q)

/-- **Sub-brick 1 — the leading `y₀`-coefficient of the reduce is the derivative of the leading
coefficient.** For `y₁`-free `q`, `eval(lcY₀(seReduce q)) = eval(cTD₂(lcY₀ q))`. The `d·lcY₀` injection
of the `y₀`-identity cancels the reduce's `c·lcY₀` term exactly when `c = degreeY₀ q`. -/
theorem seReduce_lcY0_eval (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (seReduce q)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env := by
  unfold seReduce
  have hdd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
               (chainTotalDeriv (IterExpChain 2) q)
           = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
               (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) q) := by
    rw [MultiPoly.degreeY_mul_const, degreeY0_cTD_eq_of_y1free q hy1]
  rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2) _ _ hdd,
      MultiPoly.leadingCoeffY_mul_const,
      MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_const,
      leadingCoeffY0_cTD_eval_IterExp2 q x env hy1]
  generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
      (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env = A
  generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) = N
  generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) x env = L
  mach_ring

/-! ### List facts: how the canonical `y₀`-degree reads the top coefficient -/

/-- `dropWhile` never lengthens a list (re-declared; `ChainExp2CanonMeasure`'s is `private`). -/
private theorem length_dropWhile_le {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: t => by
    rw [List.dropWhile_cons]
    cases p a with
    | false => exact Nat.le_refl _
    | true => exact Nat.le_trans (length_dropWhile_le p t) (Nat.le_succ _)

/-- The head of `L.reverse` is `L.getLast` (packaged for the `rcases` below). -/
private theorem reverse_head_eq_getLast {α : Type} (L : List α) (hne : L ≠ [])
    {a : α} {t : List α} (hrev : L.reverse = a :: t) : a = L.getLast hne := by
  have hh : L.reverse.head? = L.getLast? := List.head?_reverse L
  rw [hrev, List.head?_cons, List.getLast?_eq_getLast L hne] at hh
  exact Option.some.inj hh

/-- If a nonempty list's last entry fails the drop predicate, `reverse.dropWhile` drops nothing. -/
private theorem rdw_full_of_getLast_neg {α : Type} (p : α → Bool) (L : List α) (hne : L ≠ [])
    (hlast : p (L.getLast hne) = false) :
    L.reverse.dropWhile p = L.reverse := by
  rcases hrev : L.reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
  · rw [List.dropWhile_cons, reverse_head_eq_getLast L hne hrev, hlast,
        if_neg (by decide)]

/-- If a nonempty list's last entry passes the drop predicate, `reverse.dropWhile` strictly shortens. -/
private theorem rdw_lt_of_getLast_pos {α : Type} (p : α → Bool) (L : List α) (hne : L ≠ [])
    (hlast : p (L.getLast hne) = true) :
    (L.reverse.dropWhile p).length < L.length := by
  rcases hrev : L.reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
  · have hpos : 0 < L.length :=
      Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero.mp h))
    have htlen : t.length = L.length - 1 := by
      have hc := congrArg List.length hrev
      rw [List.length_reverse, List.length_cons] at hc
      omega
    rw [List.dropWhile_cons, reverse_head_eq_getLast L hne hrev, hlast, if_pos rfl]
    calc (t.dropWhile p).length ≤ t.length := length_dropWhile_le p t
      _ < L.length := by omega

/-- `degreeY₀` of the single-exp reduce equals `degreeY₀ q` (both summands of the `sub` have degree
`degreeY₀ q`: `cTD₂` preserves it for `y₁`-free `q`, and `const·q` keeps it). -/
theorem degreeY0_seReduce (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (seReduce q)
      = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  unfold seReduce
  rw [MultiPoly.degreeY_sub_of_eq (⟨0, by omega⟩ : Fin 2) _ _
        (by rw [MultiPoly.degreeY_mul_const, degreeY0_cTD_eq_of_y1free q hy1]),
      degreeY0_cTD_eq_of_y1free q hy1]

/-! ### Bridge: `cdegY0` / `canonLcY0` read off the top `y₀`-coefficient -/

/-- Abbreviation: the top (highest-power) `y₀`-coefficient of `q`. -/
private noncomputable def y0top (q : MultiPoly 2) : MultiPoly 2 :=
  (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).getLast (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q)

/-- When the top `y₀`-coefficient is **not** canonically zero, the canonical `y₀`-degree equals the
syntactic one (`dropWhile` removes nothing). -/
theorem cdegY0_eq_degreeY0_of_top (q : MultiPoly 2)
    (hlast : coeffCanonZeroB (y0top q) = false) :
    cdegY0 q = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  unfold cdegY0
  rw [rdw_full_of_getLast_neg coeffCanonZeroB _
        (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlast,
      List.length_reverse, yCoeffsAt_length_eq]
  omega

/-- When the top `y₀`-coefficient is not canonically zero, the canonical leading coefficient IS that
top coefficient. -/
theorem canonLcY0_eq_top (q : MultiPoly 2)
    (hlast : coeffCanonZeroB (y0top q) = false) :
    canonLcY0 q = y0top q := by
  unfold canonLcY0
  rw [rdw_full_of_getLast_neg coeffCanonZeroB _
        (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlast]
  rcases hrev : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q)
  · show a = y0top q
    exact reverse_head_eq_getLast _ (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hrev

/-- When the top `y₀`-coefficient **is** canonically zero and the syntactic degree is positive, the
canonical `y₀`-degree strictly drops. -/
theorem cdegY0_lt_degreeY0_of_top (q : MultiPoly 2)
    (hlast : coeffCanonZeroB (y0top q) = true)
    (hpos : 0 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) :
    cdegY0 q < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  unfold cdegY0
  have hlt := rdw_lt_of_getLast_pos coeffCanonZeroB _
                (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlast
  rw [yCoeffsAt_length_eq] at hlt
  omega

/-- When the top `y₀`-coefficient is canonically zero and the syntactic `y₀`-degree is `0`, the
canonical leading coefficient collapses to `const 0` (`dropWhile` empties the one-element list). -/
theorem canonLcY0_eq_const0_of_top_deg0 (q : MultiPoly 2)
    (hlast : coeffCanonZeroB (y0top q) = true)
    (hdeg : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0) :
    canonLcY0 q = MultiPoly.const 0 := by
  unfold canonLcY0
  have hlt := rdw_lt_of_getLast_pos coeffCanonZeroB _
                (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlast
  rw [yCoeffsAt_length_eq, hdeg] at hlt
  have hnil : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB = [] :=
    List.length_eq_zero.mp (by omega)
  rw [hnil]; rfl

/-! ### Connecting glue: `mP2PFL`-coefficients evaluate at the zero environment -/

/-- `evalCoeffs (polyCoeffs (mP2PFL A)) x = eval A x 0`: the scalar Horner value of the `y`-projected
coefficients is `A`'s value at the all-zero environment. -/
theorem evalCoeffs_polyCoeffs_mP2PFL (A : MultiPoly 2) (x : Real) :
    evalCoeffs (polyCoeffs (multiPolyToPolyForLex A)) x
      = MultiPoly.eval A x (fun _ => 0) := by
  rw [polyCoeffs_eval, eval_multiPolyToPolyForLex_eq_eval_zero]

/-! ### The core canonical single-exp descent -/

/-- **The single-exp canonical descent.** For `y₁`-free `q` whose top `y₀`-coefficient is not
canonically zero (`htop` — the reduce-arm precondition, equivalent to `lcY₁ p` not canonically zero at
the call site), the single-exp reduce strictly descends the canonical measure. Three leaves:

* reduce-top not canonically zero → `cdegY0` preserved, second component drops (leading coeff's
  derivative has strictly smaller `trueDeg`);
* reduce-top canonically zero, `degreeY₀ q > 0` → `cdegY0` strictly drops;
* reduce-top canonically zero, `degreeY₀ q = 0` → `cdegY0` ties at `0`, second component drops to `0`
  (`htop` gives the original second component `≥ 1`). -/
theorem singleExpMeasureCanon_seReduce_lt (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0)
    (htop : coeffCanonZeroB (y0top q) = false) :
    LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
      (singleExpMeasureCanon (seReduce q)) (singleExpMeasureCanon q) := by
  -- (Lq0 below abbreviates `polyCoeffs (mP2PFL (lcY₀ q))`, the flat coefficient list.)
  have hcd_q : cdegY0 q = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q :=
    cdegY0_eq_degreeY0_of_top q htop
  have hcl_q : canonLcY0 q = y0top q := canonLcY0_eq_top q htop
  -- the getLast eval-bridge (lcY₀ ~ y0top), specialised to env 0
  have hgl : ∀ (Z : MultiPoly 2) (x : Real),
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) Z) x (fun _ => 0)
        = MultiPoly.eval (y0top Z) x (fun _ => 0) := fun Z x =>
    eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨0, by omega⟩ : Fin 2) Z
      (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) Z) x (fun _ => 0)
  -- q's second component equals polyTrueDegreeStrict Lq0 (canonLcY0 ~ lcY₀ at eval).
  have htd_q : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
             = polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
                 (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
    apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
    intro x
    rw [evalCoeffs_polyCoeffs_mP2PFL, evalCoeffs_polyCoeffs_mP2PFL, hcl_q, ← hgl q x]
  -- q's second component is positive (its leading coeff is canonically nonzero).
  have htd_pos : 0 < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
                       (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
    have hnz : ¬ CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (y0top q))) := by
      have := htop; unfold coeffCanonZeroB at this; exact of_decide_eq_false this
    have hstep : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top q)))
               = polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
                   (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
      rw [← hcl_q]; exact htd_q
    rw [← hstep, polyTrueDegreeStrict_of_not_canonicallyZero _ hnz]; omega
  -- The reduce's top y₀-coefficient (when non-canonically-zero) has second component = deriv drop.
  have htdR : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top (seReduce q))))
            = polyTrueDegreeStrict (polyDerivativeCoeffs (polyCoeffs (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)))) := by
    have h1 : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top (seReduce q))))
            = polyTrueDegreeStrict (polyCoeffs (polyDerivative (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)))) := by
      apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
      intro x
      rw [evalCoeffs_polyCoeffs_mP2PFL, ← hgl (seReduce q) x,
          seReduce_lcY0_eval q x (fun _ => 0) hy1,
          ← eval_multiPolyToPolyForLex_eq_eval_zero,
          multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp, polyCoeffs_eval]
    rw [h1, polyTrueDegreeStrict_polyDerivative_eq_polyDerivativeCoeffs]
  -- Case split on the reduce's top y₀-coefficient.
  by_cases htopR : coeffCanonZeroB (y0top (seReduce q)) = true
  · -- reduce-top canonically zero: cdegY0 drops, or (deg 0) second drops to 0.
    by_cases hdpos : 0 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
    · -- degreeY₀ q > 0: first component strictly drops.
      refine Or.inl ?_
      show cdegY0 (seReduce q) < cdegY0 q
      rw [hcd_q]
      have := cdegY0_lt_degreeY0_of_top (seReduce q) htopR
                (by rw [degreeY0_seReduce q hy1]; exact hdpos)
      rwa [degreeY0_seReduce q hy1] at this
    · -- degreeY₀ q = 0: first ties at 0, second drops to 0.
      have hdeg0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0 := by omega
      refine Or.inr ⟨?_, ?_⟩
      · show cdegY0 (seReduce q) = cdegY0 q
        have h1 : cdegY0 (seReduce q) ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (seReduce q) :=
          cdegY0_le_degreeY0 _
        rw [degreeY0_seReduce q hy1, hdeg0] at h1
        rw [hcd_q, hdeg0]; omega
      · show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 (seReduce q))))
            < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
        rw [canonLcY0_eq_const0_of_top_deg0 (seReduce q) htopR
              (by rw [degreeY0_seReduce q hy1]; exact hdeg0),
            htd_q]
        have hz0 : polyTrueDegreeStrict
              (polyCoeffs (multiPolyToPolyForLex (MultiPoly.const 0 : MultiPoly 2))) = 0 := by
          apply polyTrueDegreeStrict_of_canonicallyZero
          have := coeffCanonZeroB_const0
          unfold coeffCanonZeroB at this
          exact of_decide_eq_true this
        rw [hz0]; exact htd_pos
  · -- reduce-top not canonically zero: first ties, second drops via derivative.
    have htopR' : coeffCanonZeroB (y0top (seReduce q)) = false := by
      cases h : coeffCanonZeroB (y0top (seReduce q))
      · rfl
      · exact absurd h htopR
    refine Or.inr ⟨?_, ?_⟩
    · show cdegY0 (seReduce q) = cdegY0 q
      rw [cdegY0_eq_degreeY0_of_top (seReduce q) htopR', degreeY0_seReduce q hy1, hcd_q]
    · show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 (seReduce q))))
          < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
      rw [canonLcY0_eq_top (seReduce q) htopR', htdR, htd_q]
      exact polyTrueDegreeStrict_polyDerivativeCoeffs_lt
        (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)))
        htd_pos

end MachLib.ChainExp2SingleExpDescent
