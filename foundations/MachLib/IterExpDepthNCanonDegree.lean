import MachLib.ChainExp2CdegInv
import MachLib.ChainExp2YPIT

/-!
# Phase A — the index-generic canonical `y`-degree and its eval-invariance (∀N)

The depth-2/3 measure uses an *eval-invariant* canonical `y`-degree (`cdegY0`, `cdegY1`) — it forgets
phantom leading `y`-terms that only cancel semantically, so eval-equal polynomials get equal degrees.
Those are written per-index (`cdegY0` at `⟨0⟩`, `cdegY1` at `⟨1⟩` in `MultiPoly 2`). The ∀N tower needs
the same construction at the **top index of any depth**, uniformly.

This file supplies it. The one index-specific ingredient in the depth-2/3 version was the canon-zero
*test* on coefficients; we replace it with a single **classical** test — `canonZeroB c = decide (c
evaluates to 0 everywhere)` — which is index- and depth-generic and makes eval-invariance nearly free
(canon-zero is congruent under eval-equality by construction). Every list-level helper it needs
(`rdw_cons`, `dropWhile_all`, `rdw_zero_of_all`, `listSubN`, `yCoeffsAt_entry_eval_zero_of_eval_zero`,
`eval_eq_of_env_agree_off`) is already index-generic.

* `MPEvalZero` / `canonZeroB` — the semantic "vanishes everywhere" predicate and its classical `Bool`.
* `cdegYAt i q` — the canonical `y_i`-degree: drop trailing canon-zero coefficients, `length − 1`.
* `canonLcYAt i q` — the canonical leading `y_i`-coefficient.
* `cdegYAt_eq_of_eval_eq`, `canonLcYAt_eval_eq_of_eval_eq` — **eval-invariance**, the payoff.

Footprint gains only `Classical.choice` over the depth-2/3 canonical degree (same as the depth-3
capstone already uses); no `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2YPIT

open scoped Classical

/-! ## The generic canon-zero test -/

/-- A coefficient/polynomial "vanishes everywhere" — the semantic notion the canonical degree forgets. -/
def MPEvalZero {n : Nat} (c : MultiPoly n) : Prop :=
  ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval c x env = 0

/-- The index-generic canon-zero test: classically decide whether `c` vanishes everywhere. Noncomputable
(uses `Classical.propDecidable`); that is fine — the whole measure is noncomputable. -/
noncomputable def canonZeroB {n : Nat} (c : MultiPoly n) : Bool := decide (MPEvalZero c)

theorem canonZeroB_true_iff {n : Nat} (c : MultiPoly n) :
    canonZeroB c = true ↔ MPEvalZero c := by
  unfold canonZeroB; exact decide_eq_true_iff

theorem canonZeroB_true_of_eval_zero {n : Nat} (c : MultiPoly n) (h : MPEvalZero c) :
    canonZeroB c = true := (canonZeroB_true_iff c).mpr h

theorem canonZeroB_const0 {n : Nat} : canonZeroB (MultiPoly.const (0 : Real) : MultiPoly n) = true :=
  canonZeroB_true_of_eval_zero _ (fun _ _ => rfl)

/-- **Canon-zero is congruent under eval-equality** — the property the classical test buys for free. -/
theorem canonZeroB_eq_of_eval_eq {n : Nat} (c1 c2 : MultiPoly n)
    (h : ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    canonZeroB c1 = canonZeroB c2 := by
  have hiff : MPEvalZero c1 ↔ MPEvalZero c2 :=
    ⟨fun hz x env => by rw [← h x env]; exact hz x env,
     fun hz x env => by rw [h x env]; exact hz x env⟩
  unfold canonZeroB
  cases hb1 : (decide (MPEvalZero c1)) <;> cases hb2 : (decide (MPEvalZero c2)) <;>
    simp_all [decide_eq_true_iff, decide_eq_false_iff_not]

/-- From `sub p q` canon-zero, `p` and `q` have equal canon-zero test. -/
theorem canonZeroB_eq_of_sub_canonZero {n : Nat} (p q : MultiPoly n)
    (h : canonZeroB (MultiPoly.sub p q) = true) : canonZeroB p = canonZeroB q := by
  have hsub : MPEvalZero (MultiPoly.sub p q) := (canonZeroB_true_iff _).mp h
  have hpq : ∀ (x : Real) (env : Fin n → Real),
      MultiPoly.eval p x env = MultiPoly.eval q x env := by
    intro x env
    have hz := hsub x env
    rw [MultiPoly.eval_sub] at hz
    have hcalc : MultiPoly.eval p x env
        = (MultiPoly.eval p x env - MultiPoly.eval q x env) + MultiPoly.eval q x env := by mach_ring
    rw [hcalc, hz]; mach_ring
  exact canonZeroB_eq_of_eval_eq p q hpq

/-! ## The list core (generic-predicate reuse of the depth-2 induction) -/

theorem all_canonZero_of_listSubN_nil {n : Nat} :
    ∀ L : List (MultiPoly n),
      (∀ c ∈ listSubN [] L, canonZeroB c = true) → ∀ c ∈ L, canonZeroB c = true
  | [], _ => by intro c hc; cases hc
  | q :: qs, h => by
    rw [listSubN_nil_cons] at h
    intro c hc
    rcases List.mem_cons.mp hc with hcq | hcqs
    · subst hcq
      have hh := canonZeroB_eq_of_sub_canonZero (MultiPoly.const 0) c (h _ (List.mem_cons_self _ _))
      rw [canonZeroB_const0] at hh
      exact hh.symm
    · exact all_canonZero_of_listSubN_nil qs (fun d hd => h d (List.mem_cons_of_mem _ hd)) c hcqs

/-- **Main list induction.** If `listSubN L1 L2` is entrywise canon-zero, the two canon-trimmed reversed
lists have equal length. -/
theorem rdw_eq_of_listSubN {n : Nat} :
    ∀ (L1 L2 : List (MultiPoly n)),
      (∀ c ∈ listSubN L1 L2, canonZeroB c = true) →
      (L1.reverse.dropWhile canonZeroB).length = (L2.reverse.dropWhile canonZeroB).length
  | [], L2, hsub => by
    rw [rdw_zero_of_all canonZeroB L2 (all_canonZero_of_listSubN_nil L2 hsub)]; rfl
  | p :: ps, [], hsub => by
    rw [listSubN_cons_nil] at hsub
    rw [rdw_zero_of_all canonZeroB (p :: ps) hsub]; rfl
  | p :: ps, q :: qs, hsub => by
    rw [listSubN_cons_cons] at hsub
    have hpq : canonZeroB (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : canonZeroB p = canonZeroB q := canonZeroB_eq_of_sub_canonZero p q hpq
    have hih := rdw_eq_of_listSubN ps qs (fun c hc => hsub c (List.mem_cons_of_mem _ hc))
    rw [rdw_cons canonZeroB p ps, rdw_cons canonZeroB q qs, hcpq, hih]

/-! ## The canonical `y_i`-degree and its eval-invariance -/

/-- **Canonical `y_i`-degree** (index-generic): drop the trailing canon-zero `y_i`-coefficients, then
`length − 1`. The eval-invariant refinement of the syntactic `degreeY i`. -/
noncomputable def cdegYAt {n : Nat} (i : Fin n) (q : MultiPoly n) : Nat :=
  ((yCoeffsAt i q).reverse.dropWhile canonZeroB).length - 1

/-- **`cdegYAt` is eval-invariant** — eval-equal polynomials have equal canonical `y_i`-degree. The
generic analog of `cdegY1_eq_of_eval_eq`; the depth-3-style descent transfers the eval-equality of the
dropped leading coefficient through it. -/
theorem cdegYAt_eq_of_eval_eq {n : Nat} (i : Fin n) (q1 q2 : MultiPoly n)
    (h : ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env) :
    cdegYAt i q1 = cdegYAt i q2 := by
  have hzero : ∀ (x : Real) (env : Fin n → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, h x env]; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt i q1) (yCoeffsAt i q2), canonZeroB c = true := by
    intro c hc
    apply canonZeroB_true_of_eval_zero
    intro x env
    exact yCoeffsAt_entry_eval_zero_of_eval_zero i (MultiPoly.sub q1 q2) hzero x env c hc
  show ((yCoeffsAt i q1).reverse.dropWhile canonZeroB).length - 1
     = ((yCoeffsAt i q2).reverse.dropWhile canonZeroB).length - 1
  rw [rdw_eq_of_listSubN _ _ hsub]

/-! ## The canonical leading `y_i`-coefficient and its eval-invariance -/

/-- From `sub p q` canon-zero, `p` and `q` are eval-equal at EVERY point (the classical test gives
everywhere-agreement directly — no `env0` restriction, unlike the structural depth-2 version). -/
theorem evalEq_of_sub_canonZero {n : Nat} (p q : MultiPoly n)
    (h : canonZeroB (MultiPoly.sub p q) = true) :
    ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval p x env = MultiPoly.eval q x env := by
  have hsub : MPEvalZero (MultiPoly.sub p q) := (canonZeroB_true_iff _).mp h
  intro x env
  have hz := hsub x env
  rw [MultiPoly.eval_sub] at hz
  have hcalc : MultiPoly.eval p x env
      = (MultiPoly.eval p x env - MultiPoly.eval q x env) + MultiPoly.eval q x env := by mach_ring
  rw [hcalc, hz]; mach_ring

private theorem mem_of_mem_dropWhile' {α : Type} (p : α → Bool) :
    ∀ (M : List α) (a : α), a ∈ M.dropWhile p → a ∈ M
  | [], a, h => h
  | b :: bs, a, h => by
    by_cases hb : p b = true
    · have hd : (b :: bs).dropWhile p = bs.dropWhile p := by simp [List.dropWhile, hb]
      rw [hd] at h
      exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile' p bs a h)
    · have hd : (b :: bs).dropWhile p = b :: bs := by simp [List.dropWhile, hb]
      rw [hd] at h
      exact h

/-- **Full-env headD induction.** If `listSubN L1 L2` is entrywise canon-zero, the `headD`s of the two
canon-trimmed reversed lists are eval-equal at EVERY point. Generic-index, full-env analog of
`rdwHead_eval0_eq_of_listSubN`. -/
theorem rdwHead_eval_eq_of_listSubN {n : Nat} :
    ∀ (L1 L2 : List (MultiPoly n)),
      (∀ c ∈ listSubN L1 L2, canonZeroB c = true) →
      ∀ (x : Real) (env : Fin n → Real),
        MultiPoly.eval ((L1.reverse.dropWhile canonZeroB).headD (MultiPoly.const 0)) x env
        = MultiPoly.eval ((L2.reverse.dropWhile canonZeroB).headD (MultiPoly.const 0)) x env
  | [], L2, hsub => by
    intro x env
    rw [dropWhile_all canonZeroB L2.reverse
      (fun c hc => all_canonZero_of_listSubN_nil L2 hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, [], hsub => by
    intro x env
    rw [listSubN_cons_nil] at hsub
    rw [dropWhile_all canonZeroB (p :: ps).reverse
      (fun c hc => hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, q :: qs, hsub => by
    intro x env
    rw [listSubN_cons_cons] at hsub
    have hpq : canonZeroB (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : canonZeroB p = canonZeroB q := canonZeroB_eq_of_sub_canonZero p q hpq
    have htail : ∀ c ∈ listSubN ps qs, canonZeroB c = true :=
      fun c hc => hsub c (List.mem_cons_of_mem _ hc)
    have hlen := rdw_eq_of_listSubN ps qs htail
    have hheadIH := rdwHead_eval_eq_of_listSubN ps qs htail x env
    have hpqe := evalEq_of_sub_canonZero p q hpq x env
    rw [rdwHead_cons canonZeroB p ps, rdwHead_cons canonZeroB q qs, hcpq, hlen]
    by_cases hc : 0 < (qs.reverse.dropWhile canonZeroB).length
    · rw [if_pos hc, if_pos hc]; exact hheadIH
    · rw [if_neg hc, if_neg hc]
      by_cases hcz : canonZeroB q = true
      · rw [if_pos hcz, if_pos hcz]
      · rw [if_neg hcz, if_neg hcz]; exact hpqe

/-- **Canonical leading `y_i`-coefficient** (index-generic): the last non-canon-zero `y_i`-coefficient. -/
noncomputable def canonLcYAt {n : Nat} (i : Fin n) (q : MultiPoly n) : MultiPoly n :=
  ((yCoeffsAt i q).reverse.dropWhile canonZeroB).headD (MultiPoly.const 0)

/-- `canonLcYAt i q` is `y_i`-free (it is a `y_i`-coefficient, or `const 0`). -/
theorem canonLcYAt_degreeY_zero {n : Nat} (i : Fin n) (q : MultiPoly n) :
    MultiPoly.degreeY i (canonLcYAt i q) = 0 := by
  unfold canonLcYAt
  rcases hL : (yCoeffsAt i q).reverse.dropWhile canonZeroB with _ | ⟨e, es⟩
  · show MultiPoly.degreeY i (MultiPoly.const 0) = 0; rfl
  · show MultiPoly.degreeY i e = 0
    have he : e ∈ yCoeffsAt i q := by
      have hmem : e ∈ (yCoeffsAt i q).reverse := by
        have hd : e ∈ (yCoeffsAt i q).reverse.dropWhile canonZeroB := by
          rw [hL]; exact List.mem_cons_self _ _
        exact mem_of_mem_dropWhile' _ _ e hd
      exact List.mem_reverse.mp hmem
    exact yCoeffsAt_entries_degreeY_zero i q e he

/-- **`canonLcYAt` is (fully) eval-invariant** — eval-equal polynomials have eval-equal canonical leading
`y_i`-coefficients. The generic analog of `canonLcY1_eval_eq_of_eval_eq`; feeds the measure's inner
component. -/
theorem canonLcYAt_eval_eq_of_eval_eq {n : Nat} (i : Fin n) (q1 q2 : MultiPoly n)
    (h : ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env)
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (canonLcYAt i q1) x env = MultiPoly.eval (canonLcYAt i q2) x env := by
  have hzero : ∀ (x' : Real) (env' : Fin n → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x' env' = 0 := by
    intro x' env'; rw [MultiPoly.eval_sub, h x' env']; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt i q1) (yCoeffsAt i q2), canonZeroB c = true := by
    intro c hc
    apply canonZeroB_true_of_eval_zero
    intro x' env'
    exact yCoeffsAt_entry_eval_zero_of_eval_zero i (MultiPoly.sub q1 q2) hzero x' env' c hc
  exact rdwHead_eval_eq_of_listSubN _ _ hsub x env

end MachLib.IterExpDepthN
