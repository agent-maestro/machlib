import MachLib.ChainExp2Trim

/-!
# Depth-3 inner-trim — dropping a phantom leading `y₁`-term of the leading `y₂`-coefficient

The depth-3 WF assembly's one remaining shrinking move. When the inner `q := dropLastY(lcY₂ p)` is
*phantom* (its syntactic leading `y₁`-coefficient vanishes on the chain) with `degreeY₁ q > 0`, the
reduce cannot make progress (it targets the dead coefficient). The fix: drop that phantom `y₁`-term
from `lcY₂ p` — reflected into `p` by rebuilding its `y₂`-coefficient list with the last (leading)
entry replaced by its `dropLeadingYAt ⟨1⟩`.

This file builds the operation `innerTrim3` and its **eval-preservation** (`eval_innerTrim3`): when the
leading `y₁`-term of the leading `y₂`-coefficient vanishes on every environment, `innerTrim3 p` agrees
with `p` everywhere. The measure/degree facts and the WF assembly follow in later phases.

Foundation: `eval_reconstructY_last_swap` — swapping the last coefficient of a `reconstructY` list for
an eval-equal one preserves the evaluation (`reconstructY` is `Σ cₖ·yᵏ`, linear in each `cₖ`). Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3InnerTrim

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct

/-- **Last-coefficient swap preserves eval.** Replacing the final entry of a `reconstructY` coefficient
list by an eval-equal polynomial does not change the evaluation — `reconstructY` is a sum `Σ cₖ·yᵢᵏ`
linear in each coefficient, and only the last coefficient changes. -/
theorem eval_reconstructY_last_swap {n : Nat} (i : Fin n) (a b : MultiPoly n)
    (x : Real) (env : Fin n → Real) (hab : MultiPoly.eval a x env = MultiPoly.eval b x env) :
    ∀ (pre : List (MultiPoly n)) (k : Nat),
      MultiPoly.eval (reconstructY i (pre ++ [a]) k) x env
        = MultiPoly.eval (reconstructY i (pre ++ [b]) k) x env := by
  intro pre
  induction pre with
  | nil =>
    intro k
    simp only [List.nil_append]
    rw [reconstructY_cons, reconstructY_cons, MultiPoly.eval_add, MultiPoly.eval_add,
        MultiPoly.eval_mul, MultiPoly.eval_mul, hab]
  | cons c cs ih =>
    intro k
    show MultiPoly.eval (reconstructY i (c :: (cs ++ [a])) k) x env
       = MultiPoly.eval (reconstructY i (c :: (cs ++ [b])) k) x env
    rw [reconstructY_cons, reconstructY_cons, MultiPoly.eval_add, MultiPoly.eval_add, ih (k + 1)]

/-- **The inner-trim operation.** Rebuild `p`'s `y₂`-coefficient list with the leading (last) entry —
the leading `y₂`-coefficient `lcY₂ p` — replaced by its `dropLeadingYAt ⟨1⟩` (its own leading `y₁`-term
dropped). All other `y₂`-coefficients are untouched. -/
noncomputable def innerTrim3 (p : MultiPoly 3) : MultiPoly 3 :=
  reconstructY (⟨2, by omega⟩ : Fin 3)
    ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]) 0

/-- **Eval-preservation.** When the leading `y₁`-term of the leading `y₂`-coefficient of `p` vanishes on
every environment (the phantom condition), `innerTrim3 p` evaluates identically to `p` at every point:
the swapped-in `dropLeadingYAt ⟨1⟩ (lcY₂ p)` is eval-equal to `lcY₂ p`, so the reconstructed polynomial
is eval-equal to the `yCoeffsAt`-round-trip, i.e. `p` itself. -/
theorem eval_innerTrim3 (p : MultiPoly 3)
    (h_phantom : ∀ (x : Real) (env : Fin 3 → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
          ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))) x env = 0)
    (x : Real) (env : Fin 3 → Real) :
    MultiPoly.eval (innerTrim3 p) x env = MultiPoly.eval p x env := by
  have hswap_eval : MultiPoly.eval (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))) x env
      = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)) x env :=
    MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 3)
      ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))
      (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))
      h_phantom x env
  unfold innerTrim3
  rw [eval_reconstructY_last_swap (⟨2, by omega⟩ : Fin 3)
        (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
          ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))
        x env hswap_eval (MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast 0,
      List.dropLast_concat_getLast (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)]
  exact eval_reconstructY_yCoeffsAt (⟨2, by omega⟩ : Fin 3) p x env

/-! ### Cross-index degree-freeness (generic) — needed for the `degreeY₂` non-increase -/

/-- **Cross-index `yCoeffsAt` freeness.** Extracting the `y_i`-coefficients of a `y_j`-free polynomial
gives `y_j`-free coefficients. Generic port of `yCoeffsAt0_entries_degreeY1_zero` — the `mul` case reuses
the index-generic `listMulN_entries_degreeY_zero`. -/
theorem yCoeffsAt_entries_other_degreeY_zero {n : Nat} (i j : Fin n) :
    ∀ (X : MultiPoly n), MultiPoly.degreeY j X = 0 →
      ∀ c ∈ MultiPoly.yCoeffsAt i X, MultiPoly.degreeY j c = 0 := by
  intro X
  induction X with
  | const c =>
    intro _ c' hc'
    rw [List.mem_singleton.mp hc']; rfl
  | varX =>
    intro _ c' hc'
    rw [List.mem_singleton.mp hc']; rfl
  | varY k =>
    intro hj c' hc'
    by_cases hki : k = i
    · change c' ∈ (if k = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                    else [MultiPoly.varY k]) at hc'
      rw [if_pos hki] at hc'
      rcases List.mem_cons.mp hc' with h | h
      · rw [h]; rfl
      · rcases List.mem_cons.mp h with h2 | h2
        · rw [h2]; rfl
        · exact absurd h2 (List.not_mem_nil _)
    · change c' ∈ (if k = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                    else [MultiPoly.varY k]) at hc'
      rw [if_neg hki, List.mem_singleton] at hc'
      rw [hc']; exact hj
  | add p q ihp ihq =>
    intro hj c hc
    have hmax : Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) = 0 := hj
    have hp : MultiPoly.degreeY j p = 0 := by
      have hle : MultiPoly.degreeY j p ≤ Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) :=
        Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY j q = 0 := by
      have hle : MultiPoly.degreeY j q ≤ Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) :=
        Nat.le_max_right _ _
      omega
    exact listAddN_entries_degreeY_zero j (MultiPoly.yCoeffsAt i p) (MultiPoly.yCoeffsAt i q)
      (ihp hp) (ihq hq) c hc
  | sub p q ihp ihq =>
    intro hj c hc
    have hmax : Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) = 0 := hj
    have hp : MultiPoly.degreeY j p = 0 := by
      have hle : MultiPoly.degreeY j p ≤ Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) :=
        Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY j q = 0 := by
      have hle : MultiPoly.degreeY j q ≤ Nat.max (MultiPoly.degreeY j p) (MultiPoly.degreeY j q) :=
        Nat.le_max_right _ _
      omega
    exact listSubN_entries_degreeY_zero j (MultiPoly.yCoeffsAt i p) (MultiPoly.yCoeffsAt i q)
      (ihp hp) (ihq hq) c hc
  | mul p q ihp ihq =>
    intro hj c hc
    have hadd : MultiPoly.degreeY j p + MultiPoly.degreeY j q = 0 := hj
    have hp : MultiPoly.degreeY j p = 0 := by omega
    have hq : MultiPoly.degreeY j q = 0 := by omega
    exact listMulN_entries_degreeY_zero j (MultiPoly.yCoeffsAt i p) (MultiPoly.yCoeffsAt i q)
      (ihp hp) (ihq hq) c hc

/-- `degreeY j (pow (varY i) k) = 0` when `j ≠ i` — powers of one chain variable are free of the others. -/
theorem degreeY_pow_varY_other {n : Nat} (i j : Fin n) (hij : j ≠ i) (k : Nat) :
    MultiPoly.degreeY j (MultiPoly.pow (MultiPoly.varY i) k) = 0 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show MultiPoly.degreeY j (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.pow (MultiPoly.varY i) k')) = 0
    show MultiPoly.degreeY j (MultiPoly.varY i) + MultiPoly.degreeY j (MultiPoly.pow (MultiPoly.varY i) k') = 0
    rw [ih]
    show (if j = i then (1 : Nat) else 0) + 0 = 0
    rw [if_neg hij]

/-- **Cross-index `reconstructY` freeness.** Reconstructing along `y_i` from `y_j`-free coefficients gives a
`y_j`-free polynomial (`j ≠ i`). Generic port of `degreeY1_reconstructY0_zero`. -/
theorem degreeY_reconstructY_other_zero {n : Nat} (i j : Fin n) (hij : j ≠ i) :
    ∀ (L : List (MultiPoly n)), (∀ c ∈ L, MultiPoly.degreeY j c = 0) → ∀ (k : Nat),
      MultiPoly.degreeY j (reconstructY i L k) = 0 := by
  intro L
  induction L with
  | nil => intro _ k; rw [reconstructY_nil]; rfl
  | cons c cs ih =>
    intro hL k
    rw [reconstructY_cons]
    show Nat.max (MultiPoly.degreeY j (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)))
                 (MultiPoly.degreeY j (reconstructY i cs (k + 1))) = 0
    have hhead : MultiPoly.degreeY j (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)) = 0 := by
      show MultiPoly.degreeY j c + MultiPoly.degreeY j (MultiPoly.pow (MultiPoly.varY i) k) = 0
      rw [hL c (List.mem_cons_self _ _), degreeY_pow_varY_other i j hij]
    have htail : MultiPoly.degreeY j (reconstructY i cs (k + 1)) = 0 :=
      ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')) (k + 1)
    rw [hhead, htail]; exact Nat.max_self 0

/-- `dropLeadingYAt ⟨1⟩` preserves `y₂`-freeness (`Fin 3`). -/
theorem degreeY2_dropLeadingYAt1_zero (X : MultiPoly 3)
    (hy2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) X = 0) :
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3) X) = 0 := by
  show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
        (reconstructY (⟨1, by omega⟩ : Fin 3)
          (MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 3) X).dropLast 0) = 0
  apply degreeY_reconstructY_other_zero (⟨1, by omega⟩ : Fin 3) (⟨2, by omega⟩ : Fin 3)
    (by intro h; have h2 := congrArg Fin.val h; simp at h2)
  intro c hc
  exact yCoeffsAt_entries_other_degreeY_zero (⟨1, by omega⟩ : Fin 3) (⟨2, by omega⟩ : Fin 3) X hy2 c
    (List.dropLast_subset _ hc)

/-- **`degreeY₂` non-increase.** `innerTrim3` never raises `degreeY₂` — the rebuilt `y₂`-coefficient list
has the same length and all-`y₂`-free entries, so `degreeY_reconstructY_lt` bounds it below the length. -/
theorem degreeY2_innerTrim3_le (p : MultiPoly 3) :
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p)
      ≤ MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := by
  have hfree : ∀ c ∈ ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]),
      MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) c = 0 := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact MultiPoly.yCoeffsAt_entries_degreeY_zero (⟨2, by omega⟩ : Fin 3) p c
        (List.dropLast_subset _ h)
    · rw [List.mem_singleton.mp h]
      exact degreeY2_dropLeadingYAt1_zero _
        (MultiPoly.yCoeffsAt_entries_degreeY_zero (⟨2, by omega⟩ : Fin 3) p _
          (List.getLast_mem _))
  have hne : ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]) ≠ [] := by
    simp
  have hlt := degreeY_reconstructY_lt (⟨2, by omega⟩ : Fin 3)
    ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]) hne hfree 0
  have hlen : ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]).length
      = (MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).length := by
    rw [List.length_append, List.length_dropLast, List.length_singleton]
    have hlen_pos : 0 < (MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).length :=
      List.length_pos.mpr (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)
    omega
  have hlen_eq : (MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).length
      = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p + 1 :=
    yCoeffsAt_length_eq (⟨2, by omega⟩ : Fin 3) p
  show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (reconstructY (⟨2, by omega⟩ : Fin 3) _ 0)
    ≤ MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
  rw [Nat.zero_add] at hlt
  rw [hlen, hlen_eq] at hlt
  omega

end MachLib.IterExpDepth3InnerTrim
