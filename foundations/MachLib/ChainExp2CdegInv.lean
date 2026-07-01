import MachLib.ChainExp2CanonMeasure
import MachLib.ChainExp2YPIT
import MachLib.ChainExp2SDR

/-!
# Route A, brick 3 — `cdegY0` eval-invariance

The canonical `y₀`-degree `cdegY0` (from `ChainExp2CanonMeasure`) is an eval-invariant: eval-equal
`MultiPoly 2`s have equal `cdegY0`. This is what lets the cancellation (`lcY₁(chain2Reduce c p)` is
eval-equal to the single-exp reduce of `lcY₁ p`) transfer the descent to the single-exp side.

Foundation: `coeffCanonZeroB` (the "this `y₀`-coefficient is canonically zero" test) is eval-invariant,
because `CanonicallyZero (polyCoeffs (mP2PFL c))` unfolds — via `polyCoeffs_eval` and
`eval_multiPolyToPolyForLex_eq_eval_zero` — to the eval condition `∀ x, eval c x (0-env) = 0`. Combined
with the `y`-PIT (`ChainExp2YPIT`) applied to `q1 − q2` and the definitional
`yCoeffsAt(sub) = listSubN(yCoeffsAt)(yCoeffsAt)`, eval-equal polys have entry-wise canonically-equal
`yCoeffsAt`, so the `reverse.dropWhile` trimming — hence `cdegY0` — agrees.

`ChainExp2SDR` + single-exp untouched (Path B).
-/

namespace MachLib.ChainExp2CdegInv

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.ChainExp2SDR
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2YPIT

/-- `CanonicallyZero (polyCoeffs (mP2PFL c))` is exactly "the `y→0` projection of `c` evaluates to `0` at
every `x`" — an eval condition. (Chains `polyCoeffs_eval` with `eval_multiPolyToPolyForLex_eq_eval_zero`.) -/
theorem canonZero_iff_eval_zero_at_0 (c : MultiPoly 2) :
    CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c))
      ↔ ∀ x : Real, MultiPoly.eval c x (fun _ => 0) = 0 := by
  unfold CanonicallyZero
  constructor
  · intro h x
    rw [← eval_multiPolyToPolyForLex_eq_eval_zero c x, ← polyCoeffs_eval]
    exact h x
  · intro h x
    rw [polyCoeffs_eval, eval_multiPolyToPolyForLex_eq_eval_zero c x]
    exact h x

/-- **`coeffCanonZeroB` is eval-invariant.** If `c1`, `c2` evaluate identically everywhere, the canonical-
zero test agrees on them. -/
theorem coeffCanonZeroB_eq_of_eval_eq (c1 c2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    coeffCanonZeroB c1 = coeffCanonZeroB c2 := by
  unfold coeffCanonZeroB
  have hiff : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c1))
            ↔ CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c2)) := by
    rw [canonZero_iff_eval_zero_at_0, canonZero_iff_eval_zero_at_0]
    constructor
    · intro hc x; rw [← h x (fun _ => 0)]; exact hc x
    · intro hc x; rw [h x (fun _ => 0)]; exact hc x
  exact decide_eq_decide.mpr hiff

/-- `coeffCanonZeroB` depends only on the `0`-env evaluation (weaker hypothesis than full eval-equality). -/
theorem coeffCanonZeroB_eq_of_eval0_eq (p q : MultiPoly 2)
    (h : ∀ x : Real, MultiPoly.eval p x (fun _ => 0) = MultiPoly.eval q x (fun _ => 0)) :
    coeffCanonZeroB p = coeffCanonZeroB q := by
  unfold coeffCanonZeroB
  apply decide_eq_decide.mpr
  rw [canonZero_iff_eval_zero_at_0, canonZero_iff_eval_zero_at_0]
  constructor
  · intro hc x; rw [← h x]; exact hc x
  · intro hc x; rw [h x]; exact hc x

/-- A poly vanishing everywhere has `coeffCanonZeroB = true`. -/
theorem coeffCanonZeroB_true_of_eval_zero (c : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c x env = 0) :
    coeffCanonZeroB c = true := by
  unfold coeffCanonZeroB
  rw [decide_eq_true_iff, canonZero_iff_eval_zero_at_0]
  intro x; exact h x (fun _ => 0)

/-- If `sub p q` is canonically zero, `p` and `q` have equal `coeffCanonZeroB`. -/
theorem coeffCanonZeroB_eq_of_sub_canonZero (p q : MultiPoly 2)
    (h : coeffCanonZeroB (MultiPoly.sub p q) = true) :
    coeffCanonZeroB p = coeffCanonZeroB q := by
  apply coeffCanonZeroB_eq_of_eval0_eq
  intro x
  have hz : MultiPoly.eval (MultiPoly.sub p q) x (fun _ => 0) = 0 :=
    (canonZero_iff_eval_zero_at_0 (MultiPoly.sub p q)).mp (decide_eq_true_iff.mp h) x
  rw [MultiPoly.eval_sub] at hz
  have hcalc : MultiPoly.eval p x (fun _ => 0)
      = (MultiPoly.eval p x (fun _ => 0) - MultiPoly.eval q x (fun _ => 0))
        + MultiPoly.eval q x (fun _ => 0) := by mach_ring
  rw [hcalc, hz]; mach_ring

/-! ### Pure-list machinery for `reverse.dropWhile` length -/

/-- If every element satisfies `p`, `dropWhile p` empties the list. -/
theorem dropWhile_all {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = true) → l.dropWhile p = []
  | [], _ => rfl
  | a :: as, h => by
    rw [List.dropWhile_cons]
    have hpa : p a = true := h a (List.mem_cons_self _ _)
    rw [if_pos hpa]
    exact dropWhile_all p as (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- `dropWhile` distributes over an append with a single trailing element. (`isEmpty` — a `Bool` — avoids
needing `DecidableEq (List α)`, which `MultiPoly 2` lacks.) -/
theorem dropWhile_append_single {α : Type} (p : α → Bool) (a : α) (l : List α) :
    (l ++ [a]).dropWhile p
    = if (l.dropWhile p).isEmpty then [a].dropWhile p else l.dropWhile p ++ [a] := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    by_cases hpb : p b = true
    · simp only [List.cons_append, List.dropWhile_cons, if_pos hpb, ih]
    · simp [List.cons_append, List.dropWhile_cons, hpb]

/-- The recursion for `(·.reverse.dropWhile p).length` on a cons. -/
theorem rdw_cons {α : Type} (p : α → Bool) (a : α) (rest : List α) :
    ((a :: rest).reverse.dropWhile p).length
    = if 0 < (rest.reverse.dropWhile p).length
      then (rest.reverse.dropWhile p).length + 1
      else (if p a = true then 0 else 1) := by
  rw [List.reverse_cons, dropWhile_append_single p a rest.reverse]
  rcases hd : rest.reverse.dropWhile p with _ | ⟨d, ds⟩
  · by_cases hpa : p a = true
    · simp [List.dropWhile, hpa]
    · simp [List.dropWhile, hpa]
  · simp [List.length_append]

/-- `(·.reverse.dropWhile p).length = 0` when every element satisfies `p`. -/
theorem rdw_zero_of_all {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ a ∈ l, p a = true) : (l.reverse.dropWhile p).length = 0 := by
  rw [dropWhile_all p l.reverse (fun a ha => h a (List.mem_reverse.mp ha))]
  rfl

/-! ### The `listSubN`-canonically-zero ⇒ equal `cdegY0` induction -/

theorem coeffCanonZeroB_const0 : coeffCanonZeroB (MultiPoly.const (0 : Real)) = true := by
  apply coeffCanonZeroB_true_of_eval_zero; intro x env; rfl

/-- From `listSubN [] L` all canonically zero, `L` is all canonically zero. -/
theorem all_canonZero_of_listSubN_nil :
    ∀ L : List (MultiPoly 2),
      (∀ c ∈ listSubN [] L, coeffCanonZeroB c = true) →
      ∀ c ∈ L, coeffCanonZeroB c = true
  | [], _ => by intro c hc; cases hc
  | q :: qs, h => by
    rw [listSubN_nil_cons] at h
    intro c hc
    rcases List.mem_cons.mp hc with hcq | hcqs
    · subst hcq
      have := coeffCanonZeroB_eq_of_sub_canonZero (MultiPoly.const 0) c
                (h _ (List.mem_cons_self _ _))
      rw [coeffCanonZeroB_const0] at this
      exact this.symm
    · exact all_canonZero_of_listSubN_nil qs
        (fun d hd => h d (List.mem_cons_of_mem _ hd)) c hcqs

/-- **Main list induction.** If `listSubN L1 L2` is entrywise canonically zero, the trimmed lengths
(`reverse.dropWhile coeffCanonZeroB`) of `L1` and `L2` agree. -/
theorem rdw_eq_of_listSubN :
    ∀ (L1 L2 : List (MultiPoly 2)),
      (∀ c ∈ listSubN L1 L2, coeffCanonZeroB c = true) →
      (L1.reverse.dropWhile coeffCanonZeroB).length
        = (L2.reverse.dropWhile coeffCanonZeroB).length
  | [], L2, hsub => by
    rw [rdw_zero_of_all coeffCanonZeroB L2 (all_canonZero_of_listSubN_nil L2 hsub)]
    rfl
  | p :: ps, [], hsub => by
    rw [listSubN_cons_nil] at hsub
    rw [rdw_zero_of_all coeffCanonZeroB (p :: ps) hsub]
    rfl
  | p :: ps, q :: qs, hsub => by
    rw [listSubN_cons_cons] at hsub
    have hpq : coeffCanonZeroB (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : coeffCanonZeroB p = coeffCanonZeroB q :=
      coeffCanonZeroB_eq_of_sub_canonZero p q hpq
    have hih := rdw_eq_of_listSubN ps qs
      (fun c hc => hsub c (List.mem_cons_of_mem _ hc))
    rw [rdw_cons coeffCanonZeroB p ps, rdw_cons coeffCanonZeroB q qs, hcpq, hih]

/-- **`cdegY0` eval-invariance.** Eval-equal `MultiPoly 2`s have equal canonical `y₀`-degree. Proof:
`q1 − q2 ≡ 0`, so (`y`-PIT) `yCoeffsAt(sub q1 q2) = listSubN(yCoeffsAt q1)(yCoeffsAt q2)` is entrywise
canonically zero, and `rdw_eq_of_listSubN` gives equal trimmed lengths. -/
theorem cdegY0_eq_of_eval_eq (q1 q2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env) :
    cdegY0 q1 = cdegY0 q2 := by
  have hzero : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, h x env]; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q1)
                             (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q2),
      coeffCanonZeroB c = true := by
    intro c hc
    apply coeffCanonZeroB_true_of_eval_zero
    intro x env
    exact yCoeffsAt_entry_eval_zero_of_eval_zero (⟨0, by omega⟩ : Fin 2)
      (MultiPoly.sub q1 q2) hzero x env c hc
  show ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q1).reverse.dropWhile coeffCanonZeroB).length - 1
     = ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q2).reverse.dropWhile coeffCanonZeroB).length - 1
  rw [rdw_eq_of_listSubN _ _ hsub]

/-! ### Second component — `canonLcY0` eval-invariance (0-env) → `singleExpMeasureCanon` eval-invariance -/

/-- From `sub p q` canonically zero, `p` and `q` agree at the `0`-env. -/
theorem eval0_eq_of_sub_canonZero (p q : MultiPoly 2)
    (h : coeffCanonZeroB (MultiPoly.sub p q) = true) :
    ∀ x : Real, MultiPoly.eval p x (fun _ => 0) = MultiPoly.eval q x (fun _ => 0) := by
  intro x
  have hz : MultiPoly.eval (MultiPoly.sub p q) x (fun _ => 0) = 0 :=
    (canonZero_iff_eval_zero_at_0 (MultiPoly.sub p q)).mp (decide_eq_true_iff.mp h) x
  rw [MultiPoly.eval_sub] at hz
  have hcalc : MultiPoly.eval p x (fun _ => 0)
      = (MultiPoly.eval p x (fun _ => 0) - MultiPoly.eval q x (fun _ => 0))
        + MultiPoly.eval q x (fun _ => 0) := by mach_ring
  rw [hcalc, hz]; mach_ring

/-- The `headD`-recursion of `·.reverse.dropWhile p` on a cons (parallel to `rdw_cons`). -/
theorem rdwHead_cons {α : Type} (p : α → Bool) (a : α) (rest : List α) (d : α) :
    ((a :: rest).reverse.dropWhile p).headD d
    = if 0 < (rest.reverse.dropWhile p).length
      then (rest.reverse.dropWhile p).headD d
      else (if p a = true then d else a) := by
  rw [List.reverse_cons, dropWhile_append_single p a rest.reverse]
  rcases hd : rest.reverse.dropWhile p with _ | ⟨e, es⟩
  · by_cases hpa : p a = true
    · simp [List.dropWhile, hpa]
    · simp [List.dropWhile, hpa]
  · simp

/-- **`canonLcY0` eval-invariance at `0`-env** (main induction, parallel to `rdw_eq_of_listSubN`). If
`listSubN L1 L2` is entrywise canonically zero, the `headD`s of the two trimmed reversed lists agree at
the `0`-env. -/
theorem rdwHead_eval0_eq_of_listSubN :
    ∀ (L1 L2 : List (MultiPoly 2)),
      (∀ c ∈ listSubN L1 L2, coeffCanonZeroB c = true) →
      ∀ x : Real,
        MultiPoly.eval ((L1.reverse.dropWhile coeffCanonZeroB).headD (MultiPoly.const 0)) x (fun _ => 0)
        = MultiPoly.eval ((L2.reverse.dropWhile coeffCanonZeroB).headD (MultiPoly.const 0)) x (fun _ => 0)
  | [], L2, hsub => by
    intro x
    rw [dropWhile_all coeffCanonZeroB L2.reverse
      (fun c hc => all_canonZero_of_listSubN_nil L2 hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, [], hsub => by
    intro x
    rw [listSubN_cons_nil] at hsub
    rw [dropWhile_all coeffCanonZeroB (p :: ps).reverse
      (fun c hc => hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, q :: qs, hsub => by
    intro x
    rw [listSubN_cons_cons] at hsub
    have hpq : coeffCanonZeroB (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : coeffCanonZeroB p = coeffCanonZeroB q :=
      coeffCanonZeroB_eq_of_sub_canonZero p q hpq
    have htail : ∀ c ∈ listSubN ps qs, coeffCanonZeroB c = true :=
      fun c hc => hsub c (List.mem_cons_of_mem _ hc)
    have hlen := rdw_eq_of_listSubN ps qs htail
    have hheadIH := rdwHead_eval0_eq_of_listSubN ps qs htail x
    have hpq0 := eval0_eq_of_sub_canonZero p q hpq x
    rw [rdwHead_cons coeffCanonZeroB p ps, rdwHead_cons coeffCanonZeroB q qs, hcpq, hlen]
    by_cases hc : 0 < (qs.reverse.dropWhile coeffCanonZeroB).length
    · rw [if_pos hc, if_pos hc]; exact hheadIH
    · rw [if_neg hc, if_neg hc]
      by_cases hcz : coeffCanonZeroB q = true
      · rw [if_pos hcz, if_pos hcz]
      · rw [if_neg hcz, if_neg hcz]; exact hpq0

/-- **`singleExpMeasureCanon` is eval-invariant.** Eval-equal `MultiPoly 2`s have equal canonical single-exp
measure — the first component by `cdegY0_eq_of_eval_eq`, the second (`polyTrueDegreeStrict` of `canonLcY0`)
by `rdwHead_eval0_eq_of_listSubN` fed through `polyTrueDegreeStrict_eq_of_evalCoeffs_eq`. -/
theorem singleExpMeasureCanon_eq_of_eval_eq (q1 q2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env) :
    singleExpMeasureCanon q1 = singleExpMeasureCanon q2 := by
  have hzero : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, h x env]; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q1)
                             (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q2),
      coeffCanonZeroB c = true := by
    intro c hc
    apply coeffCanonZeroB_true_of_eval_zero
    intro x env
    exact yCoeffsAt_entry_eval_zero_of_eval_zero (⟨0, by omega⟩ : Fin 2)
      (MultiPoly.sub q1 q2) hzero x env c hc
  unfold singleExpMeasureCanon
  rw [cdegY0_eq_of_eval_eq q1 q2 h]
  congr 1
  apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
  intro x
  rw [polyCoeffs_eval, polyCoeffs_eval,
      eval_multiPolyToPolyForLex_eq_eval_zero, eval_multiPolyToPolyForLex_eq_eval_zero]
  exact rdwHead_eval0_eq_of_listSubN _ _ hsub x

end MachLib.ChainExp2CdegInv
