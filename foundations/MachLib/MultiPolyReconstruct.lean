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

end MultiPolyReconstruct
end MachLib
