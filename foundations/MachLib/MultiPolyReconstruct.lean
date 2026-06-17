import MachLib.MultiPoly
import MachLib.MultiPolyCanonYN
import MachLib.PolynomialCanonical

/-!
# MachLib.MultiPolyReconstruct — y-coefficient reconstruction

Inverse to `MachLib.MultiPolyCanonYN.yCoeffsAt`: given a list of
y-free MultiPolys representing the y-coefficients, reconstruct a
MultiPoly. The headline `eval_reconstructY_yCoeffsAt` shows the
round-trip preserves eval.

Used by `dropLeadingY`: when the leading y-coefficient is canonically
zero, extract the y-coefficients, drop the last (canonically-zero)
entry, and reconstruct — producing a polynomial with strictly lower
formal degreeY but the same eval.

Zero Mathlib dependency. -/

namespace MachLib
namespace MultiPolyReconstruct

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly

/-! ## `reconstructY` definition

`reconstructY i [a_0, a_1, …, a_d] k = a_0·y_i^k + a_1·y_i^(k+1) +
  … + a_d·y_i^(k+d)`. The `k` offset is for inductive bookkeeping;
the user-facing form uses `k = 0`. -/

noncomputable def reconstructY {n : Nat} (i : Fin n) :
    List (MultiPoly n) → Nat → MultiPoly n
  | [],       _ => MultiPoly.const 0
  | c :: cs,  k => MultiPoly.add
                     (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k))
                     (reconstructY i cs (k + 1))

theorem reconstructY_nil {n : Nat} (i : Fin n) (k : Nat) :
    reconstructY i [] k = MultiPoly.const 0 := rfl

theorem reconstructY_cons {n : Nat} (i : Fin n) (c : MultiPoly n)
    (cs : List (MultiPoly n)) (k : Nat) :
    reconstructY i (c :: cs) k =
    MultiPoly.add (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k))
                  (reconstructY i cs (k + 1)) := rfl

/-! ## Eval correctness — matches `listEvalAuxN` -/

theorem eval_reconstructY {n : Nat} (i : Fin n) (coeffs : List (MultiPoly n))
    (k : Nat) (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (reconstructY i coeffs k) x env =
    listEvalAuxN i coeffs k x env := by
  induction coeffs generalizing k with
  | nil =>
    rw [reconstructY_nil, listEvalAuxN_nil]
    rfl
  | cons c cs ih =>
    rw [reconstructY_cons, listEvalAuxN_cons]
    show MultiPoly.eval c x env *
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env +
         MultiPoly.eval (reconstructY i cs (k + 1)) x env =
         MultiPoly.eval c x env *
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env +
         listEvalAuxN i cs (k + 1) x env
    rw [ih (k + 1)]

/-- The round-trip: reconstruct from yCoeffsAt gives the same eval. -/
theorem eval_reconstructY_yCoeffsAt {n : Nat} (i : Fin n) (p : MultiPoly n)
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (reconstructY i (yCoeffsAt i p) 0) x env =
    MultiPoly.eval p x env := by
  rw [eval_reconstructY]
  exact eval_yCoeffsAt i p x env

/-! ## Formal degreeY bound

For a coefficient list of length `L.length`, the reconstructed
polynomial has formal `degreeY i ≤ k + L.length - 1` (or 0 if the
list is empty). When all coefficients are y-free, this is tight. -/

theorem degreeY_pow_varY_self {n : Nat} (i : Fin n) (k : Nat) :
    MultiPoly.degreeY i (MultiPoly.pow (MultiPoly.varY i) k) = k := by
  induction k with
  | zero =>
    show MultiPoly.degreeY i MultiPoly.one = 0
    rfl
  | succ k' ih =>
    show MultiPoly.degreeY i
          (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.pow (MultiPoly.varY i) k')) =
         k' + 1
    show MultiPoly.degreeY i (MultiPoly.varY i) +
         MultiPoly.degreeY i (MultiPoly.pow (MultiPoly.varY i) k') = k' + 1
    rw [ih]
    show (if i = i then (1 : Nat) else 0) + k' = k' + 1
    rw [if_pos rfl]
    omega

/-- For y-free coefficients, `reconstructY` has formal degreeY at
most `k + coeffs.length - 1` (or 0 for empty list). We state the
upper bound as `k + coeffs.length` to avoid the empty-list edge case
in the statement; the tighter bound holds for nonempty lists. -/
theorem degreeY_reconstructY_le {n : Nat} (i : Fin n)
    (coeffs : List (MultiPoly n))
    (h_free : ∀ c ∈ coeffs, MultiPoly.degreeY i c = 0) (k : Nat) :
    MultiPoly.degreeY i (reconstructY i coeffs k) ≤ k + coeffs.length := by
  induction coeffs generalizing k with
  | nil =>
    rw [reconstructY_nil]
    show MultiPoly.degreeY i (MultiPoly.const 0 : MultiPoly n) ≤ k + 0
    show (0 : Nat) ≤ k + 0
    omega
  | cons c cs ih =>
    rw [reconstructY_cons]
    show Nat.max
      (MultiPoly.degreeY i
        (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)))
      (MultiPoly.degreeY i (reconstructY i cs (k + 1))) ≤
      k + (cs.length + 1)
    have h_c : MultiPoly.degreeY i c = 0 := h_free c (List.mem_cons_self _ _)
    have h_cs : ∀ c' ∈ cs, MultiPoly.degreeY i c' = 0 := fun c' hc' =>
      h_free c' (List.mem_cons_of_mem _ hc')
    have h_left : MultiPoly.degreeY i
                    (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)) = k := by
      change MultiPoly.degreeY i c +
             MultiPoly.degreeY i (MultiPoly.pow (MultiPoly.varY i) k) = k
      rw [h_c, degreeY_pow_varY_self, Nat.zero_add]
    have h_right : MultiPoly.degreeY i (reconstructY i cs (k + 1)) ≤ k + 1 + cs.length :=
      ih h_cs (k + 1)
    rw [h_left]
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · omega
    · omega

/-- Strict bound: for a nonempty y-free coefficient list, the
reconstructed polynomial's degreeY is *strictly less* than
`k + coeffs.length`. This is what `dropLeadingY` needs to drop the
first lex component. -/
theorem degreeY_reconstructY_lt {n : Nat} (i : Fin n)
    (coeffs : List (MultiPoly n))
    (h_nonempty : coeffs ≠ [])
    (h_free : ∀ c ∈ coeffs, MultiPoly.degreeY i c = 0) (k : Nat) :
    MultiPoly.degreeY i (reconstructY i coeffs k) < k + coeffs.length := by
  induction coeffs generalizing k with
  | nil => exact (h_nonempty rfl).elim
  | cons c cs ih =>
    rw [reconstructY_cons]
    show Nat.max
      (MultiPoly.degreeY i (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)))
      (MultiPoly.degreeY i (reconstructY i cs (k + 1))) <
      k + (c :: cs).length
    have h_c : MultiPoly.degreeY i c = 0 := h_free c (List.mem_cons_self _ _)
    have h_left : MultiPoly.degreeY i
                    (MultiPoly.mul c (MultiPoly.pow (MultiPoly.varY i) k)) = k := by
      change MultiPoly.degreeY i c +
             MultiPoly.degreeY i (MultiPoly.pow (MultiPoly.varY i) k) = k
      rw [h_c, degreeY_pow_varY_self, Nat.zero_add]
    rw [h_left]
    by_cases h_cs_empty : cs = []
    · subst h_cs_empty
      rw [reconstructY_nil]
      show Nat.max k (MultiPoly.degreeY i (MultiPoly.const 0 : MultiPoly n)) <
           k + [c].length
      show Nat.max k 0 < k + 1
      have h : Nat.max k 0 ≤ k :=
        Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
      omega
    · have h_cs_free : ∀ c' ∈ cs, MultiPoly.degreeY i c' = 0 := fun c' hc' =>
        h_free c' (List.mem_cons_of_mem _ hc')
      have h_ih := ih h_cs_empty h_cs_free (k + 1)
      -- h_ih : degreeY (reconstructY i cs (k+1)) < (k+1) + cs.length.
      -- (c :: cs).length = cs.length + 1.
      have h_len : (c :: cs).length = cs.length + 1 := rfl
      rw [h_len]
      -- max(k, h_ih) < k + cs.length + 1, since k < k+cs.length+1 and h_ih < (k+1)+cs.length = k+cs.length+1.
      apply Nat.max_lt.mpr
      refine ⟨?_, ?_⟩
      · -- k < k + cs.length + 1
        have : cs.length ≥ 1 := List.length_pos.mpr h_cs_empty
        omega
      · -- degreeY (reconstructY cs (k+1)) < k + cs.length + 1
        omega

/-! ## `dropLeadingY` — trim a canonically-zero leading y-coefficient

Specifically for MultiPoly 1: when the leading y-coefficient is
canonically zero (dead AST term), drop it via the round-trip through
yCoeffsAt + dropLast + reconstructY. -/

/-- The trim operation. -/
noncomputable def dropLeadingY (p : MultiPoly 1) : MultiPoly 1 :=
  reconstructY ⟨0, by omega⟩ (yCoeffsAt ⟨0, by omega⟩ p).dropLast 0

/-! ### Formal degreeY of dropLeadingY drops

For `degreeY 0 p > 0`, `yCoeffsAt 0 p` has length ≥ 2 so dropLast is
nonempty, and the reconstructY strict-bound gives `degreeY 0
(dropLeadingY p) < degreeY 0 p`. -/

/-! ### `yCoeffsAt` length bound

`(yCoeffsAt i p).length ≤ degreeY i p + 1` — the y-coefficient list
has at most `degree + 1` entries. Together with `yCoeffsAt_nonempty`,
this lets `dropLast` drop the formal degreeY at least by 1.

We need bounds on `listAddN`, `listSubN`, `listMulN` lengths
(actually only ≤ suffices for our purposes). -/

theorem listAddN_length_le {n : Nat} (l1 l2 : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listAddN l1 l2).length ≤
    Nat.max l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil =>
    rw [MachLib.MultiPolyMod.MultiPoly.listAddN_nil_left]
    show l2.length ≤ Nat.max 0 l2.length
    exact Nat.le_max_right _ _
  | cons p ps ih =>
    cases l2 with
    | nil =>
      rw [MachLib.MultiPolyMod.MultiPoly.listAddN_cons_nil]
      show (p :: ps).length ≤ Nat.max (p :: ps).length 0
      exact Nat.le_max_left _ _
    | cons q qs =>
      rw [MachLib.MultiPolyMod.MultiPoly.listAddN_cons_cons]
      show (MachLib.MultiPolyMod.MultiPoly.listAddN ps qs).length + 1 ≤
           Nat.max (ps.length + 1) (qs.length + 1)
      have ih_bound := ih qs
      have h : Nat.max ps.length qs.length + 1 ≤
               Nat.max (ps.length + 1) (qs.length + 1) := by
        rcases Nat.le_total ps.length qs.length with hpq | hpq
        · rw [show Nat.max ps.length qs.length = qs.length from
              Nat.max_eq_right hpq]
          exact Nat.le_max_right _ _
        · rw [show Nat.max ps.length qs.length = ps.length from
              Nat.max_eq_left hpq]
          exact Nat.le_max_left _ _
      exact Nat.le_trans (Nat.add_le_add_right ih_bound 1) h

/-- Helper: listSubN [] l has length = l.length. -/
theorem listSubN_nil_length {n : Nat} (l : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listSubN [] l).length = l.length := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    show (MachLib.MultiPolyMod.MultiPoly.listSubN [] (q :: qs)).length =
         (q :: qs).length
    change ((MultiPoly.sub (MultiPoly.const 0) q) ::
            MachLib.MultiPolyMod.MultiPoly.listSubN [] qs).length =
           qs.length + 1
    rw [List.length_cons, ih]

theorem listSubN_length_le {n : Nat} (l1 l2 : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listSubN l1 l2).length ≤
    Nat.max l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil =>
    rw [listSubN_nil_length]
    exact Nat.le_max_right _ _
  | cons p ps ih =>
    cases l2 with
    | nil =>
      show (MachLib.MultiPolyMod.MultiPoly.listSubN (p :: ps) []).length ≤
           Nat.max (p :: ps).length 0
      change (p :: ps).length ≤ Nat.max (p :: ps).length 0
      exact Nat.le_max_left _ _
    | cons q qs =>
      show (MachLib.MultiPolyMod.MultiPoly.listSubN (p :: ps) (q :: qs)).length ≤
           Nat.max (p :: ps).length (q :: qs).length
      change ((MultiPoly.sub p q) ::
              MachLib.MultiPolyMod.MultiPoly.listSubN ps qs).length ≤
             Nat.max ps.length.succ qs.length.succ
      have ih_bound := ih qs
      -- (listSubN ps qs).length + 1 ≤ max(ps+1, qs+1) = max(ps, qs) + 1.
      show (MachLib.MultiPolyMod.MultiPoly.listSubN ps qs).length + 1 ≤
           Nat.max (ps.length + 1) (qs.length + 1)
      have h : Nat.max ps.length qs.length + 1 ≤
               Nat.max (ps.length + 1) (qs.length + 1) := by
        rcases Nat.le_total ps.length qs.length with hpq | hpq
        · rw [show Nat.max ps.length qs.length = qs.length from
              Nat.max_eq_right hpq]
          exact Nat.le_max_right _ _
        · rw [show Nat.max ps.length qs.length = ps.length from
              Nat.max_eq_left hpq]
          exact Nat.le_max_left _ _
      exact Nat.le_trans (Nat.add_le_add_right ih_bound 1) h

/-- Length bound for `listScaleN`: scaling preserves length. -/
theorem listScaleN_length {n : Nat} (p : MultiPoly n) (qs : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listScaleN p qs).length = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs' ih =>
    rw [MachLib.MultiPolyMod.MultiPoly.listScaleN_cons]
    rw [List.length_cons, List.length_cons, ih]

/-- Strict `listMulN` length bound for both nonempty inputs:
length is strictly less than `A.length + B.length`. The strict form
is what `yCoeffsAt_length_le` needs at the `mul` case. -/
theorem listMulN_length_lt {n : Nat} (l1 l2 : List (MultiPoly n))
    (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    (MachLib.MultiPolyMod.MultiPoly.listMulN l1 l2).length <
    l1.length + l2.length := by
  induction l1 with
  | nil => exact (h1 rfl).elim
  | cons p ps ih =>
    rw [MachLib.MultiPolyMod.MultiPoly.listMulN_cons]
    have h_add := listAddN_length_le
      (MachLib.MultiPolyMod.MultiPoly.listScaleN p l2)
      (MultiPoly.const 0 :: MachLib.MultiPolyMod.MultiPoly.listMulN ps l2)
    rw [listScaleN_length] at h_add
    have h_l2_pos : l2.length > 0 := List.length_pos.mpr h2
    apply Nat.lt_of_le_of_lt h_add
    refine Nat.max_lt.mpr ⟨?_, ?_⟩
    · -- l2.length < (p :: ps).length + l2.length
      show l2.length < ps.length + 1 + l2.length
      omega
    · -- (const 0 :: listMulN ps l2).length < (p :: ps).length + l2.length
      show (MachLib.MultiPolyMod.MultiPoly.listMulN ps l2).length + 1 <
           ps.length + 1 + l2.length
      by_cases h_ps_empty : ps = []
      · subst h_ps_empty
        rw [MachLib.MultiPolyMod.MultiPoly.listMulN_nil]
        show 0 + 1 < 0 + 1 + l2.length
        omega
      · have h_ih := ih h_ps_empty
        omega

/-- Bound on `yCoeffsAt i p` length. -/
theorem yCoeffsAt_length_le {n : Nat} (i : Fin n) (p : MultiPoly n) :
    (yCoeffsAt i p).length ≤ MultiPoly.degreeY i p + 1 := by
  induction p with
  | const c =>
    -- yCoeffsAt i (const c) = [const c]; degreeY i (const c) = 0. 1 ≤ 1.
    exact Nat.le_refl 1
  | varX =>
    -- yCoeffsAt i varX = [varX]; degreeY i varX = 0. 1 ≤ 1.
    exact Nat.le_refl 1
  | varY j =>
    -- Different equality conventions: yCoeffsAt uses `j = i`, degreeY uses `i = j`.
    by_cases h : j = i
    · have h' : i = j := h.symm
      have h_yc : yCoeffsAt i (MultiPoly.varY j : MultiPoly n) =
                  [MultiPoly.const 0, MultiPoly.const 1] := by
        show (if j = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                       else ([MultiPoly.varY j] : List (MultiPoly n))) = _
        rw [if_pos h]
      have h_dy : MultiPoly.degreeY i (MultiPoly.varY j : MultiPoly n) = 1 := by
        show (if i = j then (1 : Nat) else 0) = 1
        rw [if_pos h']
      rw [h_yc, h_dy]
      exact Nat.le_refl 2
    · have h' : ¬ (i = j) := fun he => h he.symm
      have h_yc : yCoeffsAt i (MultiPoly.varY j : MultiPoly n) = [MultiPoly.varY j] := by
        show (if j = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                       else ([MultiPoly.varY j] : List (MultiPoly n))) = _
        rw [if_neg h]
      have h_dy : MultiPoly.degreeY i (MultiPoly.varY j : MultiPoly n) = 0 := by
        show (if i = j then (1 : Nat) else 0) = 0
        rw [if_neg h']
      rw [h_yc, h_dy]
      exact Nat.le_refl 1
  | add p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listAddN (yCoeffsAt i p) (yCoeffsAt i q)).length ≤
           Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
    have h_add := listAddN_length_le (yCoeffsAt i p) (yCoeffsAt i q)
    refine Nat.le_trans h_add ?_
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · apply Nat.le_trans ihp
      have h1 : MultiPoly.degreeY i p ≤
                Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_left _ _
      omega
    · apply Nat.le_trans ihq
      have h2 : MultiPoly.degreeY i q ≤
                Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      omega
  | sub p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listSubN (yCoeffsAt i p) (yCoeffsAt i q)).length ≤
           Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
    have h_sub := listSubN_length_le (yCoeffsAt i p) (yCoeffsAt i q)
    refine Nat.le_trans h_sub ?_
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · apply Nat.le_trans ihp
      have h1 : MultiPoly.degreeY i p ≤
                Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_left _ _
      omega
    · apply Nat.le_trans ihq
      have h2 : MultiPoly.degreeY i q ≤
                Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      omega
  | mul p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listMulN (yCoeffsAt i p) (yCoeffsAt i q)).length ≤
           (MultiPoly.degreeY i p + MultiPoly.degreeY i q) + 1
    have h_p_ne : yCoeffsAt i p ≠ [] := yCoeffsAt_nonempty i p
    have h_q_ne : yCoeffsAt i q ≠ [] := yCoeffsAt_nonempty i q
    have h_mul := listMulN_length_lt (yCoeffsAt i p) (yCoeffsAt i q) h_p_ne h_q_ne
    omega

/-! ### `degreeY_dropLeadingY_lt`: formal degreeY strict-decrease -/

theorem degreeY_dropLeadingY_lt (p : MultiPoly 1)
    (h_pos : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p > 0) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) (dropLeadingY p) <
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p := by
  -- Case analysis on whether `(yCoeffsAt 0 p).dropLast` is empty.
  -- Empty case: dropLeadingY = const 0, degreeY = 0 < degreeY p.
  -- Nonempty case: use the strict reconstructY bound.
  by_cases h_drop_empty :
      (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).dropLast = []
  · -- dropLeadingY = reconstructY 0 [] 0 = const 0. degreeY = 0.
    show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) (dropLeadingY p) <
         MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    unfold dropLeadingY
    rw [h_drop_empty, reconstructY_nil]
    show (0 : Nat) < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    exact h_pos
  · -- dropLast nonempty: degreeY (reconstructY 0 dropLast 0) < dropLast.length ≤ degreeY p.
    have h_yCoeffsAt_free :
        ∀ c ∈ yCoeffsAt (⟨0, by omega⟩ : Fin 1) p,
          MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) c = 0 :=
      yCoeffsAt_entries_degreeY_zero _ p
    have h_dropLast_free :
        ∀ c ∈ (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).dropLast,
          MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) c = 0 := fun c hc =>
      h_yCoeffsAt_free c (List.dropLast_subset _ hc)
    have h_lt := degreeY_reconstructY_lt
      (⟨0, by omega⟩ : Fin 1)
      (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).dropLast
      h_drop_empty h_dropLast_free 0
    -- h_lt: degreeY (reconstructY 0 dropLast 0) < 0 + dropLast.length.
    rw [Nat.zero_add] at h_lt
    -- dropLast.length ≤ degreeY p (since yCoeffsAt length ≤ degreeY + 1).
    have h_drop_le :
        (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).dropLast.length ≤
        MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p := by
      rw [List.length_dropLast]
      have h_le := yCoeffsAt_length_le (⟨0, by omega⟩ : Fin 1) p
      omega
    exact Nat.lt_of_lt_of_le h_lt h_drop_le

/-! ### `eval_dropLeadingY` — when the last yCoeffsAt entry is canonically zero -/

/-- Key technical lemma: `listEvalAuxN` of a list and of its `dropLast`
agree at every point when the last entry of the list is canonically
zero at that point. -/
theorem listEvalAuxN_dropLast_eq_of_last_eval_zero {n : Nat} (i : Fin n)
    (L : List (MultiPoly n)) (h_ne : L ≠ [])
    (x : Real) (env : Fin n → Real)
    (h_last_zero : MultiPoly.eval (L.getLast h_ne) x env = 0)
    (k : Nat) :
    listEvalAuxN i L.dropLast k x env = listEvalAuxN i L k x env := by
  induction L generalizing k with
  | nil => exact (h_ne rfl).elim
  | cons c rest ih =>
    cases rest with
    | nil =>
      -- L = [c]. dropLast = []. getLast = c. h_last_zero: c.eval = 0.
      -- listEvalAuxN [] k = 0. listEvalAuxN [c] k = c.eval * y^k + 0.
      show listEvalAuxN i ([] : List (MultiPoly n)) k x env =
           listEvalAuxN i [c] k x env
      rw [listEvalAuxN_nil, listEvalAuxN_cons, listEvalAuxN_nil]
      -- 0 = c.eval * y^k + 0. Need c.eval = 0.
      -- getLast [c] _ = c (definitionally).
      have h_c_zero : MultiPoly.eval c x env = 0 := h_last_zero
      rw [h_c_zero]
      show (0 : Real) = 0 * MultiPoly.eval
                            (MultiPoly.pow (MultiPoly.varY i) k) x env + 0
      rw [zero_mul, add_zero]
    | cons c' rest' =>
      -- L = c :: c' :: rest'. dropLast = c :: (c' :: rest').dropLast.
      -- getLast L = getLast (c' :: rest').
      change listEvalAuxN i (c :: (c' :: rest').dropLast) k x env =
             listEvalAuxN i (c :: c' :: rest') k x env
      rw [listEvalAuxN_cons, listEvalAuxN_cons]
      -- Apply IH on (c' :: rest') at offset k + 1.
      have h_rest_ne : (c' :: rest') ≠ [] := List.cons_ne_nil _ _
      have h_rest_last_zero :
          MultiPoly.eval ((c' :: rest').getLast h_rest_ne) x env = 0 := by
        -- getLast (c :: c' :: rest') = getLast (c' :: rest').
        have h_eq : ((c :: c' :: rest').getLast h_ne) =
                    ((c' :: rest').getLast h_rest_ne) :=
          List.getLast_cons h_rest_ne
        rw [← h_eq]
        exact h_last_zero
      have h_ih := ih h_rest_ne h_rest_last_zero (k + 1)
      rw [h_ih]

open MachLib.PolynomialCanonical in
/-- **Eval preservation for `dropLeadingY`.** When the leading
y-coefficient (last entry of `yCoeffsAt 0 p`) is canonically zero
at every point, `dropLeadingY p` evaluates to the same value as `p`. -/
theorem eval_dropLeadingY_of_last_canonically_zero (p : MultiPoly 1)
    (h_ne : yCoeffsAt (⟨0, by omega⟩ : Fin 1) p ≠ [])
    (h_canonical_zero : ∀ x env,
      MultiPoly.eval
        ((yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).getLast h_ne) x env = 0)
    (x : Real) (env : Fin 1 → Real) :
    MultiPoly.eval (dropLeadingY p) x env = MultiPoly.eval p x env := by
  unfold dropLeadingY
  rw [eval_reconstructY]
  rw [← eval_yCoeffsAt (⟨0, by omega⟩ : Fin 1) p x env]
  rw [show listEvalN (⟨0, by omega⟩ : Fin 1)
            (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p) x env =
          listEvalAuxN (⟨0, by omega⟩ : Fin 1)
            (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p) 0 x env from rfl]
  exact listEvalAuxN_dropLast_eq_of_last_eval_zero
    (⟨0, by omega⟩ : Fin 1) (yCoeffsAt (⟨0, by omega⟩ : Fin 1) p) h_ne x env
    (h_canonical_zero x env) 0

/-! ### Bridge: `lcY p` ↔ `(yCoeffsAt p).getLast` at the eval level

For `MultiPoly 1`, both `leadingCoeffY 0 p` and the list-based
`(yCoeffsAt 0 p).getLast` extract the same leading y-coefficient,
so they're eval-equivalent. Proven by structural induction on p
via supporting lemmas on list arithmetic length-equalities and
`getLast` distributivity through `listAddN`/`listSubN`/`listMulN`. -/

/-! #### Length equalities for list arithmetic -/

theorem listAddN_length_eq {n : Nat} (A B : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listAddN A B).length =
    Nat.max A.length B.length := by
  induction A generalizing B with
  | nil =>
    rw [MachLib.MultiPolyMod.MultiPoly.listAddN_nil_left]
    show B.length = Nat.max 0 B.length
    exact (Nat.max_eq_right (Nat.zero_le _)).symm
  | cons a as ih =>
    cases B with
    | nil =>
      rw [MachLib.MultiPolyMod.MultiPoly.listAddN_cons_nil]
      show (a :: as).length = Nat.max (a :: as).length 0
      exact (Nat.max_eq_left (Nat.zero_le _)).symm
    | cons b bs =>
      rw [MachLib.MultiPolyMod.MultiPoly.listAddN_cons_cons]
      show (MultiPoly.add a b ::
            MachLib.MultiPolyMod.MultiPoly.listAddN as bs).length =
           Nat.max (a :: as).length (b :: bs).length
      rw [List.length_cons, List.length_cons, List.length_cons, ih bs]
      rcases Nat.le_total as.length bs.length with h | h
      · have h1 : Nat.max as.length bs.length = bs.length :=
          Nat.max_eq_right h
        have h2 : Nat.max (as.length + 1) (bs.length + 1) = bs.length + 1 :=
          Nat.max_eq_right (Nat.succ_le_succ h)
        omega
      · have h1 : Nat.max as.length bs.length = as.length :=
          Nat.max_eq_left h
        have h2 : Nat.max (as.length + 1) (bs.length + 1) = as.length + 1 :=
          Nat.max_eq_left (Nat.succ_le_succ h)
        omega

theorem listSubN_length_eq {n : Nat} (A B : List (MultiPoly n)) :
    (MachLib.MultiPolyMod.MultiPoly.listSubN A B).length =
    Nat.max A.length B.length := by
  induction A generalizing B with
  | nil =>
    rw [listSubN_nil_length]
    exact (Nat.max_eq_right (Nat.zero_le _)).symm
  | cons a as ih =>
    cases B with
    | nil =>
      change (a :: as).length = Nat.max (a :: as).length 0
      exact (Nat.max_eq_left (Nat.zero_le _)).symm
    | cons b bs =>
      change ((MultiPoly.sub a b) ::
              MachLib.MultiPolyMod.MultiPoly.listSubN as bs).length =
             Nat.max (a :: as).length (b :: bs).length
      rw [List.length_cons, List.length_cons, List.length_cons, ih bs]
      rcases Nat.le_total as.length bs.length with h | h
      · have h1 : Nat.max as.length bs.length = bs.length :=
          Nat.max_eq_right h
        have h2 : Nat.max (as.length + 1) (bs.length + 1) = bs.length + 1 :=
          Nat.max_eq_right (Nat.succ_le_succ h)
        omega
      · have h1 : Nat.max as.length bs.length = as.length :=
          Nat.max_eq_left h
        have h2 : Nat.max (as.length + 1) (bs.length + 1) = as.length + 1 :=
          Nat.max_eq_left (Nat.succ_le_succ h)
        omega

theorem listMulN_length_eq {n : Nat} (A B : List (MultiPoly n))
    (hA : A ≠ []) (hB : B ≠ []) :
    (MachLib.MultiPolyMod.MultiPoly.listMulN A B).length =
    A.length + B.length - 1 := by
  induction A with
  | nil => exact (hA rfl).elim
  | cons a as ih =>
    rw [MachLib.MultiPolyMod.MultiPoly.listMulN_cons]
    rw [listAddN_length_eq, listScaleN_length]
    -- Goal: max(B.length, (const 0 :: listMulN as B).length) = (a :: as).length + B.length - 1.
    show Nat.max B.length
            (MultiPoly.const 0 ::
              MachLib.MultiPolyMod.MultiPoly.listMulN as B).length =
         (as.length + 1) + B.length - 1
    rw [List.length_cons]
    by_cases h_as_empty : as = []
    · subst h_as_empty
      rw [MachLib.MultiPolyMod.MultiPoly.listMulN_nil]
      show Nat.max B.length (([] : List (MultiPoly n)).length + 1) =
           (([] : List (MultiPoly n)).length + 1) + B.length - 1
      show Nat.max B.length 1 = 0 + 1 + B.length - 1
      have h_B_pos : B.length ≥ 1 := List.length_pos.mpr hB
      have h_max : Nat.max B.length 1 = B.length := Nat.max_eq_left h_B_pos
      omega
    · have h_ih := ih h_as_empty
      rw [h_ih]
      have h_as_pos : as.length ≥ 1 := List.length_pos.mpr h_as_empty
      have h_B_pos : B.length ≥ 1 := List.length_pos.mpr hB
      show Nat.max B.length (as.length + B.length - 1 + 1) =
           as.length + 1 + B.length - 1
      have h_eq : as.length + B.length - 1 + 1 = as.length + B.length := by omega
      rw [h_eq]
      have h_max : Nat.max B.length (as.length + B.length) = as.length + B.length :=
        Nat.max_eq_right (by omega)
      omega

/-! #### `yCoeffsAt` length is exactly `degreeY + 1` -/

theorem yCoeffsAt_length_eq {n : Nat} (i : Fin n) (p : MultiPoly n) :
    (yCoeffsAt i p).length = MultiPoly.degreeY i p + 1 := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    by_cases h : j = i
    · have h' : i = j := h.symm
      have h_yc : yCoeffsAt i (MultiPoly.varY j : MultiPoly n) =
                  [MultiPoly.const 0, MultiPoly.const 1] := by
        show (if j = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                       else ([MultiPoly.varY j] : List (MultiPoly n))) = _
        rw [if_pos h]
      have h_dy : MultiPoly.degreeY i (MultiPoly.varY j : MultiPoly n) = 1 := by
        show (if i = j then (1 : Nat) else 0) = 1
        rw [if_pos h']
      rw [h_yc, h_dy]
      rfl
    · have h' : ¬ (i = j) := fun he => h he.symm
      have h_yc : yCoeffsAt i (MultiPoly.varY j : MultiPoly n) = [MultiPoly.varY j] := by
        show (if j = i then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly n))
                       else ([MultiPoly.varY j] : List (MultiPoly n))) = _
        rw [if_neg h]
      have h_dy : MultiPoly.degreeY i (MultiPoly.varY j : MultiPoly n) = 0 := by
        show (if i = j then (1 : Nat) else 0) = 0
        rw [if_neg h']
      rw [h_yc, h_dy]
      rfl
  | add p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listAddN (yCoeffsAt i p) (yCoeffsAt i q)).length =
           Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
    rw [listAddN_length_eq, ihp, ihq]
    rcases Nat.le_total (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with h | h
    · have h1 : Nat.max (MultiPoly.degreeY i p + 1) (MultiPoly.degreeY i q + 1) =
                MultiPoly.degreeY i q + 1 :=
        Nat.max_eq_right (Nat.succ_le_succ h)
      have h2 : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) =
                MultiPoly.degreeY i q :=
        Nat.max_eq_right h
      omega
    · have h1 : Nat.max (MultiPoly.degreeY i p + 1) (MultiPoly.degreeY i q + 1) =
                MultiPoly.degreeY i p + 1 :=
        Nat.max_eq_left (Nat.succ_le_succ h)
      have h2 : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) =
                MultiPoly.degreeY i p :=
        Nat.max_eq_left h
      omega
  | sub p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listSubN (yCoeffsAt i p) (yCoeffsAt i q)).length =
           Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
    rw [listSubN_length_eq, ihp, ihq]
    rcases Nat.le_total (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with h | h
    · have h1 : Nat.max (MultiPoly.degreeY i p + 1) (MultiPoly.degreeY i q + 1) =
                MultiPoly.degreeY i q + 1 :=
        Nat.max_eq_right (Nat.succ_le_succ h)
      have h2 : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) =
                MultiPoly.degreeY i q :=
        Nat.max_eq_right h
      omega
    · have h1 : Nat.max (MultiPoly.degreeY i p + 1) (MultiPoly.degreeY i q + 1) =
                MultiPoly.degreeY i p + 1 :=
        Nat.max_eq_left (Nat.succ_le_succ h)
      have h2 : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) =
                MultiPoly.degreeY i p :=
        Nat.max_eq_left h
      omega
  | mul p q ihp ihq =>
    change (MachLib.MultiPolyMod.MultiPoly.listMulN (yCoeffsAt i p) (yCoeffsAt i q)).length =
           MultiPoly.degreeY i p + MultiPoly.degreeY i q + 1
    have h_p_ne : yCoeffsAt i p ≠ [] := yCoeffsAt_nonempty i p
    have h_q_ne : yCoeffsAt i q ≠ [] := yCoeffsAt_nonempty i q
    rw [listMulN_length_eq _ _ h_p_ne h_q_ne, ihp, ihq]
    omega

/-! ### `getLast` distributivity through list arithmetic -/

/-- Helper: nonemptiness of `listAddN A B` follows from either argument
being nonempty (via the length equality, since `max a b > 0` iff `a > 0
or b > 0`). -/
theorem listAddN_ne_of_left_ne {n : Nat} (A B : List (MultiPoly n))
    (hA : A ≠ []) : MachLib.MultiPolyMod.MultiPoly.listAddN A B ≠ [] := by
  intro h
  have h_zero : (MachLib.MultiPolyMod.MultiPoly.listAddN A B).length = 0 :=
    List.length_eq_zero.mpr h
  rw [listAddN_length_eq] at h_zero
  have h_pos : A.length > 0 := List.length_pos.mpr hA
  have h_le : A.length ≤ Nat.max A.length B.length := Nat.le_max_left _ _
  omega

/-- Helper: `(a :: l).getLast` equals `l.getLast` when `l ≠ []`. Wraps
`List.getLast_cons`. -/
theorem getLast_cons_of_ne {α : Type _} (a : α) (l : List α) (h_l : l ≠ [])
    (h_al : (a :: l) ≠ []) :
    (a :: l).getLast h_al = l.getLast h_l :=
  List.getLast_cons h_l

/-- getLast of listAddN A B (eval-level). 3-way ITE matches length
comparison: A longer → eval A.getLast; B longer → eval B.getLast;
equal → sum. -/
theorem listAddN_getLast_eval {n : Nat} :
    ∀ (A B : List (MultiPoly n)) (hA : A ≠ []) (hB : B ≠ [])
      (x : Real) (env : Fin n → Real),
    MultiPoly.eval
      ((MachLib.MultiPolyMod.MultiPoly.listAddN A B).getLast
        (listAddN_ne_of_left_ne A B hA)) x env =
    (if A.length > B.length then MultiPoly.eval (A.getLast hA) x env
     else if B.length > A.length then MultiPoly.eval (B.getLast hB) x env
     else MultiPoly.eval (A.getLast hA) x env +
          MultiPoly.eval (B.getLast hB) x env) := by
  intro A
  induction A with
  | nil => intro B hA; exact (hA rfl).elim
  | cons a as ih =>
    intro B hA hB x env
    match B with
    | [] => exact (hB rfl).elim
    | b :: bs =>
      match as, bs with
      | [], [] =>
        -- A = [a], B = [b]. listAddN = [add a b]. Lengths 1, 1. ITE → equal case.
        show MultiPoly.eval ([MultiPoly.add a b].getLast _) x env =
             (if 1 > 1 then _ else if 1 > 1 then _ else
              MultiPoly.eval a x env + MultiPoly.eval b x env)
        rw [if_neg (by omega), if_neg (by omega)]
        rfl
      | [], b' :: bs' =>
        show MultiPoly.eval _ x env =
             (if [a].length > (b :: b' :: bs').length then _
              else if (b :: b' :: bs').length > [a].length then
                MultiPoly.eval ((b :: b' :: bs').getLast _) x env
              else _)
        have h_b_len : (b :: b' :: bs').length = bs'.length + 2 := rfl
        rw [if_neg (by simp [h_b_len]), if_pos (by simp [h_b_len])]
        show MultiPoly.eval
              ((MultiPoly.add a b :: (b' :: bs')).getLast _) x env =
             MultiPoly.eval ((b :: b' :: bs').getLast _) x env
        have h_eq_lhs : (MultiPoly.add a b :: (b' :: bs') :
                         List (MultiPoly n)).getLast (by simp) =
                        (b' :: bs').getLast (by simp) :=
          List.getLast_cons (by simp)
        have h_eq_rhs : (b :: b' :: bs' : List (MultiPoly n)).getLast hB =
                        (b' :: bs').getLast (by simp) :=
          List.getLast_cons (by simp)
        rw [h_eq_lhs, h_eq_rhs]
      | a' :: as', [] =>
        show MultiPoly.eval _ x env =
             (if (a :: a' :: as').length > [b].length then
                MultiPoly.eval ((a :: a' :: as').getLast _) x env
              else if [b].length > (a :: a' :: as').length then _
              else _)
        have h_a_len : (a :: a' :: as').length = as'.length + 2 := rfl
        rw [if_pos (by simp [h_a_len])]
        show MultiPoly.eval
              ((MultiPoly.add a b :: (a' :: as')).getLast _) x env =
             MultiPoly.eval ((a :: a' :: as').getLast _) x env
        have h_eq_lhs : (MultiPoly.add a b :: (a' :: as') :
                         List (MultiPoly n)).getLast (by simp) =
                        (a' :: as').getLast (by simp) :=
          List.getLast_cons (by simp)
        have h_eq_rhs : (a :: a' :: as' : List (MultiPoly n)).getLast hA =
                        (a' :: as').getLast (by simp) :=
          List.getLast_cons (by simp)
        rw [h_eq_lhs, h_eq_rhs]
      | a' :: as', b' :: bs' =>
        -- Both lengths ≥ 2. Recurse via IH on (a' :: as', b' :: bs').
        have h_as' : (a' :: as' : List (MultiPoly n)) ≠ [] := by simp
        have h_bs' : (b' :: bs' : List (MultiPoly n)) ≠ [] := by simp
        have h_ih := ih (b' :: bs') h_as' h_bs' x env
        -- LHS: listAddN (a :: a' :: as') (b :: b' :: bs').getLast.
        -- = (add a b :: listAddN (a' :: as') (b' :: bs')).getLast.
        -- = (listAddN (a' :: as') (b' :: bs')).getLast (since RHS nonempty).
        show MultiPoly.eval
              ((MultiPoly.add a b ::
                MachLib.MultiPolyMod.MultiPoly.listAddN (a' :: as') (b' :: bs')).getLast _) x env =
             (if (a :: a' :: as').length > (b :: b' :: bs').length then
                MultiPoly.eval ((a :: a' :: as').getLast _) x env
              else if (b :: b' :: bs').length > (a :: a' :: as').length then
                MultiPoly.eval ((b :: b' :: bs').getLast _) x env
              else MultiPoly.eval ((a :: a' :: as').getLast _) x env +
                   MultiPoly.eval ((b :: b' :: bs').getLast _) x env)
        rw [List.getLast_cons (listAddN_ne_of_left_ne _ _ h_as')]
        rw [h_ih]
        rw [List.getLast_cons h_as', List.getLast_cons h_bs']
        -- Now match the ITE: (a :: a' :: as').length > (b :: b' :: bs').length iff (a' :: as').length > (b' :: bs').length.
        have h_a_len : (a :: a' :: as').length = (a' :: as').length + 1 := rfl
        have h_b_len : (b :: b' :: bs').length = (b' :: bs').length + 1 := rfl
        rcases Nat.lt_trichotomy (a' :: as').length (b' :: bs').length with h | h | h
        · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
        · rw [if_pos h, if_pos (by omega)]

/-! #### `listScaleN` and `listMulN` getLast helpers -/

/-- Nonemptiness: listScaleN preserves nonemptiness. -/
theorem listScaleN_nonempty_iff {n : Nat} (p : MultiPoly n)
    (qs : List (MultiPoly n)) (h : qs ≠ []) :
    MachLib.MultiPolyMod.MultiPoly.listScaleN p qs ≠ [] := by
  cases qs with
  | nil => exact (h rfl).elim
  | cons q qs' =>
    rw [MachLib.MultiPolyMod.MultiPoly.listScaleN_cons]
    exact List.cons_ne_nil _ _

/-- listScaleN's getLast (eval) = (scalar.eval) * (L.getLast.eval). -/
theorem listScaleN_getLast_eval {n : Nat} (p : MultiPoly n)
    (L : List (MultiPoly n)) (h_ne : L ≠ [])
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval
      ((MachLib.MultiPolyMod.MultiPoly.listScaleN p L).getLast
        (listScaleN_nonempty_iff p L h_ne)) x env =
    MultiPoly.eval p x env * MultiPoly.eval (L.getLast h_ne) x env := by
  induction L with
  | nil => exact (h_ne rfl).elim
  | cons q qs ih =>
    cases qs with
    | nil =>
      -- L = [q]. listScaleN p [q] = [mul p q]. getLast = mul p q. eval = eval p * eval q.
      show MultiPoly.eval
            ((MachLib.MultiPolyMod.MultiPoly.listScaleN p [q]).getLast _) x env =
           MultiPoly.eval p x env * MultiPoly.eval (([q] : List (MultiPoly n)).getLast _) x env
      rfl
    | cons q' qs' =>
      -- L = q :: q' :: qs'. listScaleN p L = mul p q :: listScaleN p (q' :: qs').
      -- getLast = (listScaleN p (q' :: qs')).getLast.
      -- By IH: eval = eval p * eval ((q' :: qs').getLast).
      -- L.getLast = (q :: q' :: qs').getLast = (q' :: qs').getLast.
      show MultiPoly.eval
            ((MultiPoly.mul p q ::
              MachLib.MultiPolyMod.MultiPoly.listScaleN p (q' :: qs')).getLast _) x env =
           MultiPoly.eval p x env *
           MultiPoly.eval ((q :: q' :: qs').getLast _) x env
      have h_inner : (q' :: qs' : List (MultiPoly n)) ≠ [] := by simp
      rw [List.getLast_cons (listScaleN_nonempty_iff p _ h_inner)]
      rw [List.getLast_cons h_inner]
      exact ih h_inner

/-- Nonemptiness of listMulN A B from both A, B nonempty. -/
theorem listMulN_ne_of_both_ne {n : Nat} (A B : List (MultiPoly n))
    (hA : A ≠ []) (hB : B ≠ []) :
    MachLib.MultiPolyMod.MultiPoly.listMulN A B ≠ [] := by
  intro h
  have h_zero : (MachLib.MultiPolyMod.MultiPoly.listMulN A B).length = 0 :=
    List.length_eq_zero.mpr h
  rw [listMulN_length_eq _ _ hA hB] at h_zero
  have h_A_pos : A.length ≥ 1 := List.length_pos.mpr hA
  have h_B_pos : B.length ≥ 1 := List.length_pos.mpr hB
  omega

/-- getLast of listMulN A B (eval) = (A.getLast.eval) * (B.getLast.eval)
for both A, B nonempty. -/
theorem listMulN_getLast_eval {n : Nat} :
    ∀ (A B : List (MultiPoly n)) (hA : A ≠ []) (hB : B ≠ [])
      (x : Real) (env : Fin n → Real),
    MultiPoly.eval
      ((MachLib.MultiPolyMod.MultiPoly.listMulN A B).getLast
        (listMulN_ne_of_both_ne A B hA hB)) x env =
    MultiPoly.eval (A.getLast hA) x env * MultiPoly.eval (B.getLast hB) x env := by
  intro A
  induction A with
  | nil => intro B hA; exact (hA rfl).elim
  | cons a as ih =>
    intro B hA hB x env
    cases as with
    | nil =>
      -- A = [a]. listMulN [a] B = listAddN (listScaleN a B) [const 0] (definitionally,
      -- via listMulN_cons + listMulN_nil + the (const 0 :: []) = [const 0] notation).
      -- We use `change` to expose this definitional form.
      change MultiPoly.eval
              ((MachLib.MultiPolyMod.MultiPoly.listAddN
                (MachLib.MultiPolyMod.MultiPoly.listScaleN a B)
                ([MultiPoly.const 0] : List (MultiPoly n))).getLast _) x env =
             MultiPoly.eval a x env * MultiPoly.eval (B.getLast hB) x env
      have h_scale_ne : MachLib.MultiPolyMod.MultiPoly.listScaleN a B ≠ [] :=
        listScaleN_nonempty_iff a B hB
      have h_const_ne : ([MultiPoly.const 0] : List (MultiPoly n)) ≠ [] :=
        List.cons_ne_nil _ _
      rw [listAddN_getLast_eval _ _ h_scale_ne h_const_ne x env]
      rw [listScaleN_length]
      -- Goal now: ITE on B.length vs [const 0].length. [const 0].length = 1 (definitional).
      have h_const_len : ([MultiPoly.const 0] : List (MultiPoly n)).length = 1 := rfl
      have h_B_pos : B.length ≥ 1 := List.length_pos.mpr hB
      by_cases h_B_eq : B.length = 1
      · -- Equal length case (B.length = 1).
        rw [if_neg (by show ¬ B.length > 1; omega),
            if_neg (by show ¬ 1 > B.length; omega)]
        -- Goal: eval listScaleN.getLast + eval ([const 0].getLast) = eval a * eval B.getLast.
        rw [listScaleN_getLast_eval a B hB x env]
        show MultiPoly.eval a x env * MultiPoly.eval (B.getLast hB) x env +
             MultiPoly.eval
               (([MultiPoly.const 0] : List (MultiPoly n)).getLast
                 (List.cons_ne_nil _ _)) x env =
             MultiPoly.eval a x env * MultiPoly.eval (B.getLast hB) x env
        show _ + (0 : Real) = _
        rw [add_zero]
      · -- B.length > 1.
        have h_B_gt : B.length > 1 := by omega
        rw [if_pos (by show B.length > 1; omega)]
        rw [listScaleN_getLast_eval a B hB x env]
    | cons a' as' =>
      -- A = a :: a' :: as'. listMulN unfolds to
      -- listAddN (listScaleN a B) (const 0 :: listMulN (a' :: as') B).
      -- listMulN (a' :: as') B is nonempty (recursion).
      -- (const 0 :: listMulN ...).length = (a' :: as').length + B.length > B.length.
      -- So the right side is longer; getLast = (const 0 :: ...).getLast = (listMulN ...).getLast.
      -- By IH: = (a' :: as').getLast * B.getLast.
      have h_as'_ne : (a' :: as' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
      have h_mul_ne : MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B ≠ [] :=
        listMulN_ne_of_both_ne (a' :: as') B h_as'_ne hB
      -- Use change to expose the listAddN form.
      change MultiPoly.eval
              ((MachLib.MultiPolyMod.MultiPoly.listAddN
                (MachLib.MultiPolyMod.MultiPoly.listScaleN a B)
                (MultiPoly.const 0 ::
                  MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B)).getLast _) x env =
             MultiPoly.eval ((a :: a' :: as').getLast _) x env *
             MultiPoly.eval (B.getLast hB) x env
      have h_scale_ne : MachLib.MultiPolyMod.MultiPoly.listScaleN a B ≠ [] :=
        listScaleN_nonempty_iff a B hB
      have h_cons_ne : (MultiPoly.const 0 ::
                       MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B :
                       List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
      rw [listAddN_getLast_eval _ _ h_scale_ne h_cons_ne x env]
      rw [listScaleN_length]
      -- Inner length: (const 0 :: listMulN (a' :: as') B).length = (listMulN ...).length + 1
      --                                                          = ((a' :: as').length + B.length - 1) + 1
      --                                                          = (a' :: as').length + B.length.
      have h_as'_pos : (a' :: as').length ≥ 1 := List.length_pos.mpr h_as'_ne
      have h_B_pos : B.length ≥ 1 := List.length_pos.mpr hB
      have h_inner_len : (MultiPoly.const 0 ::
                          MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B :
                          List (MultiPoly n)).length =
                         (a' :: as').length + B.length := by
        show (MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B).length + 1 =
             (a' :: as').length + B.length
        rw [listMulN_length_eq _ _ h_as'_ne hB]
        omega
      -- For (a' :: as').length ≥ 1: (a' :: as').length + B.length > B.length.
      rw [if_neg
        (by show ¬ B.length > (MultiPoly.const 0 ::
                MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B :
                List (MultiPoly n)).length
            rw [h_inner_len]; omega)]
      rw [if_pos
        (by show (MultiPoly.const 0 ::
              MachLib.MultiPolyMod.MultiPoly.listMulN (a' :: as') B :
              List (MultiPoly n)).length > B.length
            rw [h_inner_len]; omega)]
      -- Goal: eval ((const 0 :: listMulN ...).getLast _) = eval ((a :: a' :: as').getLast _) * eval B.getLast.
      rw [List.getLast_cons h_mul_ne]
      rw [ih B h_as'_ne hB x env]
      rw [List.getLast_cons h_as'_ne]

/-! #### `listSubN` getLast (with negation cascade for the nil-left case) -/

/-- Nonemptiness of listSubN A B from A nonempty. -/
theorem listSubN_ne_of_left_ne {n : Nat} (A B : List (MultiPoly n))
    (hA : A ≠ []) : MachLib.MultiPolyMod.MultiPoly.listSubN A B ≠ [] := by
  intro h
  have h_zero : (MachLib.MultiPolyMod.MultiPoly.listSubN A B).length = 0 :=
    List.length_eq_zero.mpr h
  rw [listSubN_length_eq] at h_zero
  have h_pos : A.length > 0 := List.length_pos.mpr hA
  have h_le : A.length ≤ Nat.max A.length B.length := Nat.le_max_left _ _
  omega

/-- Nonemptiness of listSubN [] L from L nonempty. -/
theorem listSubN_nil_ne_of_ne {n : Nat} (L : List (MultiPoly n)) (h : L ≠ []) :
    MachLib.MultiPolyMod.MultiPoly.listSubN ([] : List (MultiPoly n)) L ≠ [] := by
  cases L with
  | nil => exact (h rfl).elim
  | cons q qs =>
    rw [MachLib.MultiPolyMod.MultiPoly.listSubN_nil_cons]
    exact List.cons_ne_nil _ _

/-- Auxiliary: `listSubN [] L`'s getLast (eval) = `0 - L.getLast.eval`. -/
theorem listSubN_nil_getLast_eval {n : Nat} (L : List (MultiPoly n))
    (h_ne : L ≠ []) (x : Real) (env : Fin n → Real) :
    MultiPoly.eval
      ((MachLib.MultiPolyMod.MultiPoly.listSubN ([] : List (MultiPoly n)) L).getLast
        (listSubN_nil_ne_of_ne L h_ne)) x env =
    0 - MultiPoly.eval (L.getLast h_ne) x env := by
  induction L with
  | nil => exact (h_ne rfl).elim
  | cons q qs ih =>
    cases qs with
    | nil =>
      -- L = [q]. listSubN [] [q] = [sub (const 0) q]. getLast = sub (const 0) q.
      -- eval = 0 - q.eval.
      rfl
    | cons q' qs' =>
      -- L = q :: q' :: qs'. listSubN [] L = sub (const 0) q :: listSubN [] (q' :: qs').
      -- getLast = (listSubN [] (q' :: qs')).getLast.
      -- By IH: = 0 - (q' :: qs').getLast.eval.
      -- L.getLast = (q' :: qs').getLast (via List.getLast_cons).
      have h_inner : (q' :: qs' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
      have h_inner_sub_ne := listSubN_nil_ne_of_ne (q' :: qs') h_inner
      change MultiPoly.eval
              ((MultiPoly.sub (MultiPoly.const 0) q ::
                MachLib.MultiPolyMod.MultiPoly.listSubN [] (q' :: qs')).getLast _) x env =
             0 - MultiPoly.eval ((q :: q' :: qs').getLast _) x env
      rw [List.getLast_cons h_inner_sub_ne]
      rw [List.getLast_cons h_inner]
      exact ih h_inner

/-- getLast of listSubN A B (eval). 3-way ITE: A longer → eval A.getLast;
B longer → 0 - eval B.getLast (negated due to the listSubN [] cascade);
equal → eval A.getLast - eval B.getLast. -/
theorem listSubN_getLast_eval {n : Nat} :
    ∀ (A B : List (MultiPoly n)) (hA : A ≠ []) (hB : B ≠ [])
      (x : Real) (env : Fin n → Real),
    MultiPoly.eval
      ((MachLib.MultiPolyMod.MultiPoly.listSubN A B).getLast
        (listSubN_ne_of_left_ne A B hA)) x env =
    (if A.length > B.length then MultiPoly.eval (A.getLast hA) x env
     else if B.length > A.length then 0 - MultiPoly.eval (B.getLast hB) x env
     else MultiPoly.eval (A.getLast hA) x env -
          MultiPoly.eval (B.getLast hB) x env) := by
  intro A
  induction A with
  | nil => intro B hA; exact (hA rfl).elim
  | cons a as ih =>
    intro B hA hB x env
    match B with
    | [] => exact (hB rfl).elim
    | b :: bs =>
      match as, bs with
      | [], [] =>
        -- A = [a], B = [b]. listSubN [a] [b] = [sub a b]. equal length 1.
        show MultiPoly.eval _ x env =
             (if 1 > 1 then _ else if 1 > 1 then _ else
              MultiPoly.eval a x env - MultiPoly.eval b x env)
        rw [if_neg (by omega), if_neg (by omega)]
        rfl
      | [], b' :: bs' =>
        -- A = [a], B = b :: b' :: bs'. listSubN [a] (b :: b' :: bs') =
        --   sub a b :: listSubN [] (b' :: bs').
        -- getLast = (listSubN [] (b' :: bs')).getLast = sub (const 0) (last)
        --         = 0 - (b' :: bs').getLast (via listSubN_nil_getLast_eval).
        -- (b :: b' :: bs').getLast = (b' :: bs').getLast.
        -- A.length = 1, B.length = bs'.length + 2 > 1. ITE → B longer, eval = 0 - eval B.getLast.
        show MultiPoly.eval _ x env =
             (if [a].length > (b :: b' :: bs').length then _
              else if (b :: b' :: bs').length > [a].length then
                0 - MultiPoly.eval ((b :: b' :: bs').getLast hB) x env
              else _)
        rw [if_neg (by show ¬ 1 > bs'.length + 2; omega),
            if_pos (by show bs'.length + 2 > 1; omega)]
        change MultiPoly.eval
                ((MultiPoly.sub a b ::
                  MachLib.MultiPolyMod.MultiPoly.listSubN [] (b' :: bs')).getLast _) x env =
               0 - MultiPoly.eval ((b :: b' :: bs').getLast hB) x env
        have h_inner_ne : (b' :: bs' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
        have h_inner_sub_ne := listSubN_nil_ne_of_ne (b' :: bs') h_inner_ne
        rw [List.getLast_cons h_inner_sub_ne]
        rw [listSubN_nil_getLast_eval (b' :: bs') h_inner_ne x env]
        rw [List.getLast_cons h_inner_ne]
      | a' :: as', [] =>
        -- A = a :: a' :: as', B = [b]. listSubN = sub a b :: listSubN (a' :: as') [].
        -- listSubN (a' :: as') [] = (a' :: as') (the unmatched-A case is identity).
        -- getLast = (a' :: as').getLast = (a :: a' :: as').getLast.
        show MultiPoly.eval _ x env =
             (if (a :: a' :: as').length > [b].length then
                MultiPoly.eval ((a :: a' :: as').getLast _) x env
              else if [b].length > (a :: a' :: as').length then _
              else _)
        rw [if_pos (by show as'.length + 2 > 1; omega)]
        change MultiPoly.eval
                ((MultiPoly.sub a b :: (a' :: as')).getLast _) x env =
               MultiPoly.eval ((a :: a' :: as').getLast _) x env
        have h_inner : (a' :: as' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
        rw [List.getLast_cons h_inner]
        rw [List.getLast_cons h_inner]
      | a' :: as', b' :: bs' =>
        -- Both lengths ≥ 2. Recurse via IH on (a' :: as', b' :: bs').
        have h_as'_ne : (a' :: as' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
        have h_bs'_ne : (b' :: bs' : List (MultiPoly n)) ≠ [] := List.cons_ne_nil _ _
        have h_ih := ih (b' :: bs') h_as'_ne h_bs'_ne x env
        change MultiPoly.eval
                ((MultiPoly.sub a b ::
                  MachLib.MultiPolyMod.MultiPoly.listSubN (a' :: as') (b' :: bs')).getLast _) x env =
               (if (a :: a' :: as').length > (b :: b' :: bs').length then
                  MultiPoly.eval ((a :: a' :: as').getLast _) x env
                else if (b :: b' :: bs').length > (a :: a' :: as').length then
                  0 - MultiPoly.eval ((b :: b' :: bs').getLast _) x env
                else MultiPoly.eval ((a :: a' :: as').getLast _) x env -
                     MultiPoly.eval ((b :: b' :: bs').getLast _) x env)
        rw [List.getLast_cons (listSubN_ne_of_left_ne _ _ h_as'_ne)]
        rw [h_ih]
        rw [List.getLast_cons h_as'_ne, List.getLast_cons h_bs'_ne]
        have h_a_len : (a :: a' :: as').length = (a' :: as').length + 1 := rfl
        have h_b_len : (b :: b' :: bs').length = (b' :: bs').length + 1 := rfl
        rcases Nat.lt_trichotomy (a' :: as').length (b' :: bs').length with h | h | h
        · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
        · rw [if_pos h, if_pos (by omega)]

/-! ### Bridge theorem: `lcY p` and `(yCoeffsAt p).getLast` are eval-equivalent

Generic over chain length n. Proven by structural induction on p,
using the three `getLast` distributivity lemmas plus
`yCoeffsAt_length_eq` to align `lcY`'s `degreeY` case analysis with
`getLast`'s length case analysis. -/

theorem eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general {n : Nat}
    (i : Fin n) (p : MultiPoly n) (h_ne : yCoeffsAt i p ≠ [])
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env =
    MultiPoly.eval ((yCoeffsAt i p).getLast h_ne) x env := by
  induction p with
  | const c =>
    -- lcY (const c) = const c. yCoeffsAt (const c) = [const c]. getLast = const c. rfl.
    rfl
  | varX =>
    rfl
  | varY j =>
    by_cases h : j = i
    · show MultiPoly.eval
            (MultiPoly.leadingCoeffY i (MultiPoly.varY j : MultiPoly n)) x env =
           MultiPoly.eval
            ((yCoeffsAt i (MultiPoly.varY j : MultiPoly n)).getLast h_ne) x env
      simp only [MultiPoly.leadingCoeffY, yCoeffsAt, if_pos h]
      rfl
    · show MultiPoly.eval
            (MultiPoly.leadingCoeffY i (MultiPoly.varY j : MultiPoly n)) x env =
           MultiPoly.eval
            ((yCoeffsAt i (MultiPoly.varY j : MultiPoly n)).getLast h_ne) x env
      simp only [MultiPoly.leadingCoeffY, yCoeffsAt, if_neg h]
      rfl
  | add p q ihp ihq =>
    -- yCoeffsAt (add p q) = listAddN A B where A = yCoeffsAt p, B = yCoeffsAt q.
    -- lcY (add p q) = if dp > dq then lcY p else if dq > dp then lcY q else add (lcY p) (lcY q).
    -- length(A) = dp + 1, length(B) = dq + 1 (by yCoeffsAt_length_eq).
    -- listAddN_getLast_eval: 3-way ITE on lengths matches our case analysis.
    have h_p_ne : yCoeffsAt i p ≠ [] := yCoeffsAt_nonempty i p
    have h_q_ne : yCoeffsAt i q ≠ [] := yCoeffsAt_nonempty i q
    change MultiPoly.eval
            (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then
              MultiPoly.leadingCoeffY i p
             else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then
              MultiPoly.leadingCoeffY i q
             else MultiPoly.add (MultiPoly.leadingCoeffY i p)
                                (MultiPoly.leadingCoeffY i q)) x env =
           MultiPoly.eval
            ((MachLib.MultiPolyMod.MultiPoly.listAddN
              (yCoeffsAt i p) (yCoeffsAt i q)).getLast _) x env
    rw [listAddN_getLast_eval _ _ h_p_ne h_q_ne x env]
    rw [yCoeffsAt_length_eq, yCoeffsAt_length_eq]
    -- Now case-split on degreeY comparison.
    rcases Nat.lt_trichotomy (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with h | h | h
    · -- dp < dq → lcY = lcY q; ITE → eval (yCoeffsAt q).getLast = eval (lcY q) by ihq.
      rw [if_neg (by omega), if_pos h]
      rw [if_neg (by omega), if_pos (by omega)]
      exact ihq h_q_ne
    · -- dp = dq → lcY = add (lcY p) (lcY q); ITE equal case → eval A.getLast + eval B.getLast.
      rw [if_neg (by omega), if_neg (by omega)]
      rw [if_neg (by omega), if_neg (by omega)]
      show MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env +
           MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env =
           MultiPoly.eval ((yCoeffsAt i p).getLast h_p_ne) x env +
           MultiPoly.eval ((yCoeffsAt i q).getLast h_q_ne) x env
      rw [ihp h_p_ne, ihq h_q_ne]
    · -- dp > dq → lcY = lcY p; ITE → eval A.getLast = eval (lcY p) by ihp.
      rw [if_pos h]
      rw [if_pos (by omega)]
      exact ihp h_p_ne
  | sub p q ihp ihq =>
    -- yCoeffsAt (sub p q) = listSubN A B. lcY's sub branch has the same case structure but with sub/negation.
    have h_p_ne : yCoeffsAt i p ≠ [] := yCoeffsAt_nonempty i p
    have h_q_ne : yCoeffsAt i q ≠ [] := yCoeffsAt_nonempty i q
    change MultiPoly.eval
            (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then
              MultiPoly.leadingCoeffY i p
             else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then
              MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
             else MultiPoly.sub (MultiPoly.leadingCoeffY i p)
                                (MultiPoly.leadingCoeffY i q)) x env =
           MultiPoly.eval
            ((MachLib.MultiPolyMod.MultiPoly.listSubN
              (yCoeffsAt i p) (yCoeffsAt i q)).getLast _) x env
    rw [listSubN_getLast_eval _ _ h_p_ne h_q_ne x env]
    rw [yCoeffsAt_length_eq, yCoeffsAt_length_eq]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with h | h | h
    · -- dp < dq → lcY = sub (const 0) (lcY q); ITE → 0 - eval (yCoeffsAt q).getLast.
      rw [if_neg (by omega), if_pos h]
      rw [if_neg (by omega), if_pos (by omega)]
      show MultiPoly.eval (MultiPoly.const 0 : MultiPoly n) x env -
           MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env =
           0 - MultiPoly.eval ((yCoeffsAt i q).getLast h_q_ne) x env
      rw [ihq h_q_ne]
      rfl
    · -- dp = dq → lcY = sub (lcY p) (lcY q); ITE equal case → eval A.getLast - eval B.getLast.
      rw [if_neg (by omega), if_neg (by omega)]
      rw [if_neg (by omega), if_neg (by omega)]
      show MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env -
           MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env =
           MultiPoly.eval ((yCoeffsAt i p).getLast h_p_ne) x env -
           MultiPoly.eval ((yCoeffsAt i q).getLast h_q_ne) x env
      rw [ihp h_p_ne, ihq h_q_ne]
    · -- dp > dq → lcY = lcY p.
      rw [if_pos h]
      rw [if_pos (by omega)]
      exact ihp h_p_ne
  | mul p q ihp ihq =>
    -- yCoeffsAt (mul p q) = listMulN A B. lcY (mul p q) = mul (lcY p) (lcY q).
    -- listMulN_getLast_eval: eval = eval A.getLast * eval B.getLast.
    have h_p_ne : yCoeffsAt i p ≠ [] := yCoeffsAt_nonempty i p
    have h_q_ne : yCoeffsAt i q ≠ [] := yCoeffsAt_nonempty i q
    change MultiPoly.eval
            (MultiPoly.mul (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)) x env =
           MultiPoly.eval
            ((MachLib.MultiPolyMod.MultiPoly.listMulN
              (yCoeffsAt i p) (yCoeffsAt i q)).getLast _) x env
    rw [listMulN_getLast_eval _ _ h_p_ne h_q_ne x env]
    show MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env *
         MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env =
         MultiPoly.eval ((yCoeffsAt i p).getLast h_p_ne) x env *
         MultiPoly.eval ((yCoeffsAt i q).getLast h_q_ne) x env
    rw [ihp h_p_ne, ihq h_q_ne]

/-- Specialization to `MultiPoly 1` matching the dispatch reducer's
expectation. -/
theorem eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast
    (p : MultiPoly 1)
    (h_ne : yCoeffsAt (⟨0, by omega⟩ : Fin 1) p ≠ [])
    (x : Real) (env : Fin 1 → Real) :
    MultiPoly.eval
      (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 1) p) x env =
    MultiPoly.eval
      ((yCoeffsAt (⟨0, by omega⟩ : Fin 1) p).getLast h_ne) x env :=
  eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general _ p h_ne x env

end MultiPolyReconstruct
end MachLib
