import MachLib.FiniteZeroPacket
import MachLib.Differentiation
import MachLib.Rolle

/-!
MachLib.PolynomialRootCount — first tiny root-count scaffold.

This module defines the primitives needed for a future polynomial
degree/root-count theorem and proves one checked foothold: a linear factor
has no pair of distinct roots. It does not prove the general degree/root-count
theorem.
-/

namespace MachLib
namespace PolynomialRootCount

open MachLib.Real
open MachLib.PolynomialEvidence

/-- A point is a root of a polynomial when evaluation returns zero. -/
def Root (p : Poly) (x : Real) : Prop :=
  Poly.eval p x = 0

/-- A polynomial is witnessed nonzero by one point where evaluation is nonzero. -/
def NonzeroWitness (p : Poly) : Prop :=
  ∃ x : Real, Poly.eval p x ≠ 0

/-- A pair of distinct roots. This is the first root-count obstruction shape. -/
def DistinctRootPair (p : Poly) : Prop :=
  ∃ x : Real, ∃ y : Real, Root p x ∧ Root p y ∧ x ≠ y

/-- A syntactic degree upper bound for the tiny polynomial AST. -/
def degreeUpper : Poly → Nat
  | Poly.const _ => 0
  | Poly.var => 1
  | Poly.add p q => Nat.max (degreeUpper p) (degreeUpper q)
  | Poly.sub p q => Nat.max (degreeUpper p) (degreeUpper q)
  | Poly.mul p q => degreeUpper p + degreeUpper q

/-- A linear factor has syntactic degree upper bound one. -/
theorem degreeUpper_linearFactor (r : Real) :
    degreeUpper (Poly.linearFactor r) = 1 := rfl

/-- Multiplying by a linear factor increases the syntactic degree upper bound
by one. This is only a syntactic upper-bound fact, not a normalized polynomial
degree theorem. -/
theorem degreeUpper_factorMul (r : Real) (q : Poly) :
    degreeUpper (Poly.factorMul r q) = 1 + degreeUpper q := rfl

/-- If `(x - r)` evaluates to zero at `x`, then `x = r`. -/
theorem linearFactor_root_unique (r x : Real)
    (h : Root (Poly.linearFactor r) x) : x = r := by
  unfold Root Poly.linearFactor Poly.eval at h
  change x - r = 0 at h
  rw [sub_def] at h
  calc x
      = x + 0 := (add_zero x).symm
    _ = x + (-r + r) := by rw [neg_add_self]
    _ = (x + -r) + r := by rw [← add_assoc]
    _ = 0 + r := by rw [h]
    _ = r := zero_add r

/-- A linear factor cannot have two distinct roots. -/
theorem linearFactor_no_distinct_root_pair (r : Real) :
    ¬ DistinctRootPair (Poly.linearFactor r) := by
  intro h
  rcases h with ⟨x, y, hxroot, hyroot, hne⟩
  have hx_eq : x = r := linearFactor_root_unique r x hxroot
  have hy_eq : y = r := linearFactor_root_unique r y hyroot
  apply hne
  rw [hx_eq, hy_eq]

/-- A finite root list is sound when every actual root is present in the list.
This is intentionally finite/list-shaped; it does not claim a complete set of
roots for arbitrary polynomial syntax. -/
def RootListSound (p : Poly) (roots : List Real) : Prop :=
  ∀ x : Real, Root p x → x ∈ roots

/-- Root-list distinctness without importing a larger finite-set library. -/
def RootListDistinct : List Real → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ RootListDistinct xs

/-- A finite root list respects the syntactic degree upper bound. -/
def RootListDegreeBound (p : Poly) (roots : List Real) : Prop :=
  roots.length ≤ degreeUpper p

/-- A checked finite root packet for a tiny polynomial. -/
structure FiniteRootPacket where
  poly : Poly
  roots : List Real
  sound : RootListSound poly roots
  distinct : RootListDistinct roots
  degree_bound : RootListDegreeBound poly roots

/-- The singleton `[r]` is a sound root list for the linear factor `(x - r)`. -/
theorem linearFactor_rootListSound (r : Real) :
    RootListSound (Poly.linearFactor r) [r] := by
  intro x hx
  have hx_eq : x = r := linearFactor_root_unique r x hx
  rw [hx_eq]
  simp

/-- The singleton `[r]` has no duplicate roots. -/
theorem singleton_rootListDistinct (r : Real) :
    RootListDistinct [r] := by
  simp [RootListDistinct]

/-- The singleton root list for a linear factor is bounded by degree one. -/
theorem linearFactor_rootListDegreeBound (r : Real) :
    RootListDegreeBound (Poly.linearFactor r) [r] := by
  simp [RootListDegreeBound, degreeUpper_linearFactor]

/-- A complete checked finite-root packet for the first degree-one case. -/
noncomputable def linearFactorFiniteRootPacket (r : Real) : FiniteRootPacket where
  poly := Poly.linearFactor r
  roots := [r]
  sound := linearFactor_rootListSound r
  distinct := singleton_rootListDistinct r
  degree_bound := linearFactor_rootListDegreeBound r

/-! ## Polynomial derivative — symbolic, with HasDerivAt agreement -/

/-- Symbolic derivative of a polynomial. Follows the standard rules:
constant → 0, var → 1, sum/difference componentwise, product via the
product rule. Lives in the PolynomialRootCount namespace; reference
as `MachLib.PolynomialRootCount.polyDerivative`. -/
noncomputable def polyDerivative : Poly → Poly
  | Poly.const _ => Poly.const 0
  | Poly.var => Poly.const 1
  | Poly.add p q => Poly.add (polyDerivative p) (polyDerivative q)
  | Poly.sub p q => Poly.sub (polyDerivative p) (polyDerivative q)
  | Poly.mul p q => Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q))

/-- `Poly.eval p` is differentiable everywhere, and its derivative is
`Poly.eval polyDerivative p`. Proven by induction on the polynomial
structure using Differentiation.lean's `HasDerivAt_*` rules. -/
theorem polyHasDerivAt_eval (p : Poly) (x : Real) :
    HasDerivAt (Poly.eval p) (Poly.eval (polyDerivative p) x) x := by
  induction p with
  | const c =>
    exact HasDerivAt_const c x
  | var =>
    exact HasDerivAt_id x
  | add p q ihp ihq =>
    exact HasDerivAt_add (Poly.eval p) (Poly.eval q)
            (Poly.eval (polyDerivative p) x) (Poly.eval (polyDerivative q) x) x ihp ihq
  | sub p q ihp ihq =>
    exact HasDerivAt_sub (Poly.eval p) (Poly.eval q)
            (Poly.eval (polyDerivative p) x) (Poly.eval (polyDerivative q) x) x ihp ihq
  | mul p q ihp ihq =>
    exact HasDerivAt_mul (Poly.eval p) (Poly.eval q)
            (Poly.eval (polyDerivative p) x) (Poly.eval (polyDerivative q) x) x ihp ihq

/-! ## Polynomial normalization — polySimplify -/

open Classical in
/-- `true` if the polynomial is the literal `const 0`. Uses classical
decidability of Real equality. -/
noncomputable def polyIsZeroConst : Poly → Bool
  | Poly.const c => if c = 0 then true else false
  | _ => false

open Classical in
/-- `true` if the polynomial is the literal `const 1`. -/
noncomputable def polyIsOneConst : Poly → Bool
  | Poly.const c => if c = 1 then true else false
  | _ => false

open Classical in
/-- Polynomial normalization. Collapses identity factors / additive
zeros:
- `add p (const 0) → p`, `add (const 0) p → p`.
- `sub p (const 0) → p`.
- `mul p (const 0) → const 0`, `mul (const 0) p → const 0`.
- `mul p (const 1) → p`, `mul (const 1) p → p`.

Other expressions are left structurally intact. The normalization
preserves evaluation (theorem `polySimplify_eval`). -/
noncomputable def polySimplify : Poly → Poly
  | Poly.const c => Poly.const c
  | Poly.var => Poly.var
  | Poly.add p q =>
    let p' := polySimplify p
    let q' := polySimplify q
    if polyIsZeroConst p' then q'
    else if polyIsZeroConst q' then p'
    else Poly.add p' q'
  | Poly.sub p q =>
    let p' := polySimplify p
    let q' := polySimplify q
    if polyIsZeroConst q' then p'
    else Poly.sub p' q'
  | Poly.mul p q =>
    let p' := polySimplify p
    let q' := polySimplify q
    if polyIsZeroConst p' then Poly.const 0
    else if polyIsZeroConst q' then Poly.const 0
    else if polyIsOneConst p' then q'
    else if polyIsOneConst q' then p'
    else Poly.mul p' q'

/-- If `polyIsZeroConst p = true`, then `Poly.eval p x = 0` everywhere. -/
theorem polyIsZeroConst_eval (p : Poly) (h : polyIsZeroConst p = true) (x : Real) :
    Poly.eval p x = 0 := by
  cases p with
  | const c =>
    unfold polyIsZeroConst at h
    by_cases hc : c = 0
    · rw [hc]; rfl
    · simp [hc] at h
  | var => unfold polyIsZeroConst at h; simp at h
  | add _ _ => unfold polyIsZeroConst at h; simp at h
  | sub _ _ => unfold polyIsZeroConst at h; simp at h
  | mul _ _ => unfold polyIsZeroConst at h; simp at h

/-- If `polyIsOneConst p = true`, then `Poly.eval p x = 1` everywhere. -/
theorem polyIsOneConst_eval (p : Poly) (h : polyIsOneConst p = true) (x : Real) :
    Poly.eval p x = 1 := by
  cases p with
  | const c =>
    unfold polyIsOneConst at h
    by_cases hc : c = 1
    · rw [hc]; rfl
    · simp [hc] at h
  | var => unfold polyIsOneConst at h; simp at h
  | add _ _ => unfold polyIsOneConst at h; simp at h
  | sub _ _ => unfold polyIsOneConst at h; simp at h
  | mul _ _ => unfold polyIsOneConst at h; simp at h

/-- **`polySimplify` preserves evaluation.** -/
theorem polySimplify_eval (p : Poly) (x : Real) :
    Poly.eval (polySimplify p) x = Poly.eval p x := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    unfold polySimplify
    by_cases hp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hp]
      have hp_eval : Poly.eval (polySimplify p) x = 0 :=
        polyIsZeroConst_eval (polySimplify p) hp x
      show Poly.eval (polySimplify q) x = Poly.eval p x + Poly.eval q x
      rw [ihq, ← ihp, hp_eval, zero_add]
    · rw [if_neg hp]
      by_cases hq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hq]
        have hq_eval : Poly.eval (polySimplify q) x = 0 :=
          polyIsZeroConst_eval (polySimplify q) hq x
        show Poly.eval (polySimplify p) x = Poly.eval p x + Poly.eval q x
        rw [ihp, ← ihq, hq_eval, add_zero]
      · rw [if_neg hq]
        show Poly.eval (polySimplify p) x + Poly.eval (polySimplify q) x =
             Poly.eval p x + Poly.eval q x
        rw [ihp, ihq]
  | sub p q ihp ihq =>
    unfold polySimplify
    by_cases hq : polyIsZeroConst (polySimplify q) = true
    · rw [if_pos hq]
      have hq_eval : Poly.eval (polySimplify q) x = 0 :=
        polyIsZeroConst_eval (polySimplify q) hq x
      show Poly.eval (polySimplify p) x = Poly.eval p x - Poly.eval q x
      rw [ihp, ← ihq, hq_eval, sub_zero]
    · rw [if_neg hq]
      show Poly.eval (polySimplify p) x - Poly.eval (polySimplify q) x =
           Poly.eval p x - Poly.eval q x
      rw [ihp, ihq]
  | mul p q ihp ihq =>
    unfold polySimplify
    by_cases hp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hp]
      have hp_eval : Poly.eval (polySimplify p) x = 0 :=
        polyIsZeroConst_eval (polySimplify p) hp x
      show (0 : Real) = Poly.eval p x * Poly.eval q x
      rw [← ihp, hp_eval, zero_mul]
    · rw [if_neg hp]
      by_cases hq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hq]
        have hq_eval : Poly.eval (polySimplify q) x = 0 :=
          polyIsZeroConst_eval (polySimplify q) hq x
        show (0 : Real) = Poly.eval p x * Poly.eval q x
        rw [← ihq, hq_eval, mul_zero]
      · rw [if_neg hq]
        by_cases hp1 : polyIsOneConst (polySimplify p) = true
        · rw [if_pos hp1]
          have hp1_eval : Poly.eval (polySimplify p) x = 1 :=
            polyIsOneConst_eval (polySimplify p) hp1 x
          show Poly.eval (polySimplify q) x = Poly.eval p x * Poly.eval q x
          rw [ihq, ← ihp, hp1_eval, one_mul_thm]
        · rw [if_neg hp1]
          by_cases hq1 : polyIsOneConst (polySimplify q) = true
          · rw [if_pos hq1]
            have hq1_eval : Poly.eval (polySimplify q) x = 1 :=
              polyIsOneConst_eval (polySimplify q) hq1 x
            show Poly.eval (polySimplify p) x = Poly.eval p x * Poly.eval q x
            rw [ihp, ← ihq, hq1_eval, mul_one_ax]
          · rw [if_neg hq1]
            show Poly.eval (polySimplify p) x * Poly.eval (polySimplify q) x =
                 Poly.eval p x * Poly.eval q x
            rw [ihp, ihq]

/-! ## polyDerivative degreeUpper bound (non-strict) -/

/-- The symbolic derivative has `degreeUpper` no greater than the
original. Non-strict; the strict decrease `degreeUpper (polyDerivative
p) < degreeUpper p` (needed for the FTA induction via Rolle) requires
polynomial NORMALIZATION (collapse `0 * x` → `0`, etc.) which isn't
yet in MachLib. Without normalization, expressions like `mul (const c)
var` have polyDerivative `add (mul (const 0) var) (mul (const c)
(const 1))` whose syntactic degreeUpper = original's.

This non-strict bound is proven directly by structural induction. -/
theorem polyDerivative_degreeUpper_le (p : Poly) :
    degreeUpper (polyDerivative p) ≤ degreeUpper p := by
  induction p with
  | const _ => exact Nat.le_refl 0
  | var => exact Nat.zero_le 1
  | add p q ihp ihq =>
    -- degreeUpper (add (polyDerivative p) (polyDerivative q))
    --   = max (degreeUpper (polyDerivative p)) (degreeUpper (polyDerivative q))
    --   ≤ max (degreeUpper p) (degreeUpper q) = degreeUpper (add p q).
    show Nat.max (degreeUpper (polyDerivative p)) (degreeUpper (polyDerivative q)) ≤
           Nat.max (degreeUpper p) (degreeUpper q)
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
           Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | sub p q ihp ihq =>
    show Nat.max (degreeUpper (polyDerivative p)) (degreeUpper (polyDerivative q)) ≤
           Nat.max (degreeUpper p) (degreeUpper q)
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
           Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | mul p q ihp ihq =>
    -- degreeUpper (add (mul (polyDerivative p) q) (mul p (polyDerivative q)))
    --   = max (degreeUpper (polyDerivative p) + degreeUpper q)
    --         (degreeUpper p + degreeUpper (polyDerivative q))
    --   ≤ max (degreeUpper p + degreeUpper q)
    --         (degreeUpper p + degreeUpper q) = degreeUpper (mul p q).
    show Nat.max (degreeUpper (polyDerivative p) + degreeUpper q)
                  (degreeUpper p + degreeUpper (polyDerivative q)) ≤
           degreeUpper p + degreeUpper q
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.add_le_add_right ihp _
    · exact Nat.add_le_add_left ihq _

/-! ## polyDerivative degreeUpper bound after polySimplify (strict)

Khovanskii sprint week 1 chunk 2 (2026-06-11). The strict decrease
`degreeUpper (polyDerivative p) < degreeUpper p` fails syntactically
because polyDerivative inflates the AST: e.g. `mul (const c) var`
(degreeUpper 1) becomes `add (mul (const 0) var) (mul (const c)
(const 1))` whose `Poly.add` branch still has syntactic degreeUpper 1
from the `mul (const 0) var` subterm.

`polySimplify` collapses `mul (const 0) p` to `const 0` (and similar
identity reductions), which IS sufficient to recover the strict
decrease. The bound below uses the effective degree
`effDeg p := degreeUpper (polySimplify p)` and proves the strict
version needed for the FTA induction in chunk 3. -/

/-- If `polyIsZeroConst p = true`, then `p` is structurally `const 0` and
its `degreeUpper` is `0`. Helper for the polySimplify case splits below. -/
theorem polyIsZeroConst_degreeUpper (p : Poly) (h : polyIsZeroConst p = true) :
    degreeUpper p = 0 := by
  cases p with
  | const c => rfl
  | var => unfold polyIsZeroConst at h; simp at h
  | add _ _ => unfold polyIsZeroConst at h; simp at h
  | sub _ _ => unfold polyIsZeroConst at h; simp at h
  | mul _ _ => unfold polyIsZeroConst at h; simp at h

/-- Same as above for the one-constant test. -/
theorem polyIsOneConst_degreeUpper (p : Poly) (h : polyIsOneConst p = true) :
    degreeUpper p = 0 := by
  cases p with
  | const c => rfl
  | var => unfold polyIsOneConst at h; simp at h
  | add _ _ => unfold polyIsOneConst at h; simp at h
  | sub _ _ => unfold polyIsOneConst at h; simp at h
  | mul _ _ => unfold polyIsOneConst at h; simp at h

/-- `polyIsZeroConst (Poly.const 0) = true` evaluates through the
classical `if 0 = 0 then true else false`. Used as the unconditional
"yes" leaf throughout the polySimplify case analyses below. -/
theorem polyIsZeroConst_const_zero : polyIsZeroConst (Poly.const 0) = true := by
  simp [polyIsZeroConst]

/-- The polyIsZeroConst test is structural: only `Poly.const 0` passes.
This lets us rewrite a hypothesis `polyIsZeroConst p = true` into the
literal equation `p = Poly.const 0` for use as a `rw` rewriter. -/
theorem polyIsZeroConst_iff_const_zero (p : Poly) :
    polyIsZeroConst p = true → p = Poly.const 0 := by
  cases p with
  | const c =>
    intro h
    unfold polyIsZeroConst at h
    by_cases hc : c = 0
    · rw [hc]
    · simp [hc] at h
  | var => intro h; unfold polyIsZeroConst at h; simp at h
  | add _ _ => intro h; unfold polyIsZeroConst at h; simp at h
  | sub _ _ => intro h; unfold polyIsZeroConst at h; simp at h
  | mul _ _ => intro h; unfold polyIsZeroConst at h; simp at h


/-- **Load-bearing helper for the mul case.** If `p` simplifies to the
literal `const 0`, then so does its derivative. Without this fact, the
non-strict bound's `mul` case can't close: polySimplify of `Poly.mul p q`
collapses to `const 0` when `polyIsZeroConst (polySimplify p) = true`,
but polySimplify of `polyDerivative (Poly.mul p q)` (which contains
`Poly.mul p (polyDerivative q)`) does NOT automatically collapse just
from knowing `p` simplifies to zero — the polySimplify rule for mul
checks `polyIsZeroConst` on the LEFT factor's simplification, which
for `Poly.mul p (polyDerivative q)` is `polySimplify p`. THAT does
collapse via the hypothesis; the symmetric `Poly.mul (polyDerivative p) q`
also collapses because (by this lemma) `polySimplify (polyDerivative p)`
is also `const 0`. -/
theorem polyIsZeroConst_polyDerivative_after_simplify (p : Poly) :
    polyIsZeroConst (polySimplify p) = true →
    polyIsZeroConst (polySimplify (polyDerivative p)) = true := by
  induction p with
  | const c =>
    -- polyDerivative (const c) = const 0; polySimplify (const 0) = const 0;
    -- polyIsZeroConst (const 0) = true. So the conclusion is unconditional;
    -- the premise is only true when c = 0 but that doesn't matter here.
    intro _
    show polyIsZeroConst (Poly.const 0) = true
    exact polyIsZeroConst_const_zero
  | var =>
    -- polySimplify var = var; polyIsZeroConst var = false. Premise vacuous.
    intro h; unfold polySimplify polyIsZeroConst at h; simp at h
  | add p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hsp] at h
      -- h : polyIsZeroConst (polySimplify q) = true
      -- polyDerivative (add p q) = add (polyDerivative p) (polyDerivative q)
      -- Both polyDerivatives' simplifications are const 0 by ihp/ihq.
      show polyIsZeroConst (polySimplify
              (Poly.add (polyDerivative p) (polyDerivative q))) = true
      unfold polySimplify
      rw [if_pos (ihp hsp)]
      exact ihq h
    · rw [if_neg hsp] at h
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq] at h
        -- h : polyIsZeroConst (polySimplify p) = true; contradiction with hsp.
        exact absurd h hsp
      · rw [if_neg hsq] at h
        -- h : polyIsZeroConst of an `add` form, which is false.
        unfold polyIsZeroConst at h; simp at h
  | sub p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsq : polyIsZeroConst (polySimplify q) = true
    · rw [if_pos hsq] at h
      -- h : polyIsZeroConst (polySimplify p) = true
      show polyIsZeroConst (polySimplify
              (Poly.sub (polyDerivative p) (polyDerivative q))) = true
      unfold polySimplify
      rw [if_pos (ihq hsq)]
      exact ihp h
    · rw [if_neg hsq] at h
      -- h : polyIsZeroConst of a `sub` form, which is false.
      unfold polyIsZeroConst at h; simp at h
  | mul p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · -- polySimplify (mul p q) = const 0 via the zero-left rule;
      -- polyIsZeroConst (const 0) = true (h is trivially satisfied).
      -- polyDerivative (mul p q) = add (mul (polyDerivative p) q) (mul p (polyDerivative q)).
      -- Both inner muls simplify to const 0 (ihp hsp gives the first; hsp itself the second).
      show polyIsZeroConst (polySimplify
              (Poly.add (Poly.mul (polyDerivative p) q)
                        (Poly.mul p (polyDerivative q)))) = true
      have h_left : polyIsZeroConst (polySimplify
                        (Poly.mul (polyDerivative p) q)) = true := by
        unfold polySimplify
        rw [if_pos (ihp hsp)]; exact polyIsZeroConst_const_zero
      have h_right : polyIsZeroConst (polySimplify
                         (Poly.mul p (polyDerivative q))) = true := by
        unfold polySimplify
        rw [if_pos hsp]; exact polyIsZeroConst_const_zero
      unfold polySimplify
      rw [if_pos h_left]
      exact h_right
    · rw [if_neg hsp] at h
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · -- polySimplify (mul p q) = const 0 via the zero-right rule (after
        -- the left was rejected). Symmetric to the zero-left case.
        show polyIsZeroConst (polySimplify
                (Poly.add (Poly.mul (polyDerivative p) q)
                          (Poly.mul p (polyDerivative q)))) = true
        have h_left : polyIsZeroConst (polySimplify
                          (Poly.mul (polyDerivative p) q)) = true := by
          unfold polySimplify
          by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
          · rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
          · rw [if_neg hsdp, if_pos hsq]; exact polyIsZeroConst_const_zero
        have h_right : polyIsZeroConst (polySimplify
                           (Poly.mul p (polyDerivative q))) = true := by
          unfold polySimplify
          by_cases h2 : polyIsZeroConst (polySimplify p) = true
          · rw [if_pos h2]; exact polyIsZeroConst_const_zero
          · rw [if_neg h2, if_pos (ihq hsq)]; exact polyIsZeroConst_const_zero
        unfold polySimplify
        rw [if_pos h_left]
        exact h_right
      · rw [if_neg hsq] at h
        by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · rw [if_pos h1sp] at h
          -- h : polyIsZeroConst (polySimplify q) = true; contradiction with hsq.
          exact absurd h hsq
        · rw [if_neg h1sp] at h
          by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · rw [if_pos h1sq] at h
            -- h : polyIsZeroConst (polySimplify p) = true; contradiction with hsp.
            exact absurd h hsp
          · rw [if_neg h1sq] at h
            -- h : polyIsZeroConst of a `mul` form, which is false.
            unfold polyIsZeroConst at h; simp at h

/-- Parallel to polyIsZeroConst_polyDerivative_after_simplify but for one-const.
If `p` simplifies to the literal `const 1`, then its derivative simplifies to
the literal `const 0`. Needed for the strict mul case's polyIsOneConst sub-cases:
when sp = const 1, polySimplify (mul dp q) collapses via this lemma rather
than equalling sq (which would defeat the strict bound). -/
theorem polyIsOneConst_polyDerivative_zero_after_simplify (p : Poly) :
    polyIsOneConst (polySimplify p) = true →
    polyIsZeroConst (polySimplify (polyDerivative p)) = true := by
  induction p with
  | const c =>
    intro _
    show polyIsZeroConst (Poly.const 0) = true
    exact polyIsZeroConst_const_zero
  | var =>
    intro h; unfold polySimplify polyIsOneConst at h; simp at h
  | add p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hsp] at h
      have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
        polyIsZeroConst_polyDerivative_after_simplify p hsp
      show polyIsZeroConst (polySimplify
              (Poly.add (polyDerivative p) (polyDerivative q))) = true
      unfold polySimplify
      rw [if_pos hsdp]
      exact ihq h
    · rw [if_neg hsp] at h
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq] at h
        have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
          polyIsZeroConst_polyDerivative_after_simplify q hsq
        show polyIsZeroConst (polySimplify
                (Poly.add (polyDerivative p) (polyDerivative q))) = true
        unfold polySimplify
        by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
        · rw [if_pos hsdp]; exact hsdq
        · rw [if_neg hsdp]; rw [if_pos hsdq]; exact ihp h
      · rw [if_neg hsq] at h
        unfold polyIsOneConst at h; simp at h
  | sub p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsq : polyIsZeroConst (polySimplify q) = true
    · rw [if_pos hsq] at h
      have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
        polyIsZeroConst_polyDerivative_after_simplify q hsq
      show polyIsZeroConst (polySimplify
              (Poly.sub (polyDerivative p) (polyDerivative q))) = true
      unfold polySimplify
      rw [if_pos hsdq]
      exact ihp h
    · rw [if_neg hsq] at h
      unfold polyIsOneConst at h; simp at h
  | mul p q ihp ihq =>
    intro h
    unfold polySimplify at h
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hsp] at h
      -- h : polyIsOneConst (Poly.const 0) = true ⇒ 0 = 1; impossible.
      simp [polyIsOneConst] at h
      exact absurd h zero_ne_one_ax
    · rw [if_neg hsp] at h
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq] at h
        -- h : polyIsOneConst (Poly.const 0) = true ⇒ 0 = 1; impossible.
        simp [polyIsOneConst] at h
        exact absurd h zero_ne_one_ax
      · rw [if_neg hsq] at h
        by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · rw [if_pos h1sp] at h
          -- Both sp and sq simplify to const 1.
          have hsdp_zero : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
            ihp h1sp
          have hsdq_zero : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
            ihq h
          show polyIsZeroConst (polySimplify
                  (Poly.add (Poly.mul (polyDerivative p) q)
                            (Poly.mul p (polyDerivative q)))) = true
          have h_left : polyIsZeroConst (polySimplify
                            (Poly.mul (polyDerivative p) q)) = true := by
            unfold polySimplify
            rw [if_pos hsdp_zero]
            exact polyIsZeroConst_const_zero
          have h_right : polyIsZeroConst (polySimplify
                             (Poly.mul p (polyDerivative q))) = true := by
            unfold polySimplify
            rw [if_neg hsp, if_pos hsdq_zero]
            exact polyIsZeroConst_const_zero
          unfold polySimplify
          rw [if_pos h_left]
          exact h_right
        · rw [if_neg h1sp] at h
          by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · rw [if_pos h1sq] at h
            exact absurd h h1sp
          · rw [if_neg h1sq] at h
            unfold polyIsOneConst at h; simp at h

/-- If polySimplify q has degreeUpper 0 (q "represents a constant" in the
structural sense), then polyDerivative q simplifies to const 0. Needed
for the strict mul case's "neither" sub-case to handle the asymmetric
(sp > 0, sq = 0) situations where the outer polySimplify (add a' b')
collapse depends on polyIsZeroConst sdq.

Semantically: a polynomial that simplifies to a constant has derivative 0,
and polySimplify catches this. The proof is structural induction on q
that mirrors polyIsZeroConst_polyDerivative_after_simplify. -/
theorem polyDerivative_zero_when_simplified_degree_zero (q : Poly) :
    degreeUpper (polySimplify q) = 0 →
    polyIsZeroConst (polySimplify (polyDerivative q)) = true := by
  induction q with
  | const c =>
    intro _
    show polyIsZeroConst (Poly.const 0) = true
    exact polyIsZeroConst_const_zero
  | var =>
    -- polySimplify var = var; degreeUpper = 1; premise 1 = 0 vacuous.
    intro h
    show polyIsZeroConst (polySimplify (Poly.const 1)) = true
    -- Vacuous from h : (1 : Nat) = 0
    have : (1 : Nat) = 0 := h
    exact absurd this (by decide)
  | add p q ihp ihq =>
    intro h
    -- degreeUpper (polySimplify (add p q)) = 0 implies both polySimplify p, q
    -- have degreeUpper 0 (across all polySimplify cases).
    have hsp_zero : degreeUpper (polySimplify p) = 0 ∧
                    degreeUpper (polySimplify q) = 0 := by
      conv at h => lhs; unfold polySimplify
      by_cases hsp : polyIsZeroConst (polySimplify p) = true
      · rw [if_pos hsp] at h
        refine ⟨?_, h⟩
        exact polyIsZeroConst_degreeUpper _ hsp
      · rw [if_neg hsp] at h
        by_cases hsq : polyIsZeroConst (polySimplify q) = true
        · rw [if_pos hsq] at h
          refine ⟨h, ?_⟩
          exact polyIsZeroConst_degreeUpper _ hsq
        · rw [if_neg hsq] at h
          -- h : degreeUpper (Poly.add sp sq) = 0
          -- degreeUpper add = max → both 0.
          show degreeUpper (polySimplify p) = 0 ∧
               degreeUpper (polySimplify q) = 0
          have hmax : Nat.max (degreeUpper (polySimplify p))
                              (degreeUpper (polySimplify q)) = 0 := h
          refine ⟨Nat.le_zero.mp (hmax ▸ Nat.le_max_left _ _),
                  Nat.le_zero.mp (hmax ▸ Nat.le_max_right _ _)⟩
    have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
      ihp hsp_zero.1
    have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
      ihq hsp_zero.2
    have hsdq_eq : polySimplify (polyDerivative q) = Poly.const 0 :=
      polyIsZeroConst_iff_const_zero _ hsdq
    show polyIsZeroConst (polySimplify
            (Poly.add (polyDerivative p) (polyDerivative q))) = true
    conv => lhs; unfold polySimplify
    rw [if_pos hsdp, hsdq_eq]
    exact polyIsZeroConst_const_zero
  | sub p q ihp ihq =>
    intro h
    have hsp_zero : degreeUpper (polySimplify p) = 0 ∧
                    degreeUpper (polySimplify q) = 0 := by
      conv at h => lhs; unfold polySimplify
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq] at h
        refine ⟨h, ?_⟩
        exact polyIsZeroConst_degreeUpper _ hsq
      · rw [if_neg hsq] at h
        have hmax : Nat.max (degreeUpper (polySimplify p))
                            (degreeUpper (polySimplify q)) = 0 := h
        refine ⟨Nat.le_zero.mp (hmax ▸ Nat.le_max_left _ _),
                Nat.le_zero.mp (hmax ▸ Nat.le_max_right _ _)⟩
    have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
      ihp hsp_zero.1
    have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
      ihq hsp_zero.2
    have hsdp_eq : polySimplify (polyDerivative p) = Poly.const 0 :=
      polyIsZeroConst_iff_const_zero _ hsdp
    show polyIsZeroConst (polySimplify
            (Poly.sub (polyDerivative p) (polyDerivative q))) = true
    conv => lhs; unfold polySimplify
    rw [if_pos hsdq, hsdp_eq]
    exact polyIsZeroConst_const_zero
  | mul p q ihp ihq =>
    intro h
    -- 5 sub-cases on polySimplify (mul p q). In each, the inner muls'
    -- polyDerivative collapse via the helpers and the zero-left rule.
    conv at h => lhs; unfold polySimplify
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · -- sp is const 0; derivative side already collapses.
      have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
        polyIsZeroConst_polyDerivative_after_simplify p hsp
      show polyIsZeroConst (polySimplify
              (Poly.add (Poly.mul (polyDerivative p) q)
                        (Poly.mul p (polyDerivative q)))) = true
      have h_left : polyIsZeroConst (polySimplify
                        (Poly.mul (polyDerivative p) q)) = true := by
        conv => lhs; unfold polySimplify
        rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
      have h_right : polyIsZeroConst (polySimplify
                         (Poly.mul p (polyDerivative q))) = true := by
        conv => lhs; unfold polySimplify
        rw [if_pos hsp]; exact polyIsZeroConst_const_zero
      conv => lhs; unfold polySimplify
      rw [if_pos h_left]
      exact h_right
    · rw [if_neg hsp] at h
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
          polyIsZeroConst_polyDerivative_after_simplify q hsq
        show polyIsZeroConst (polySimplify
                (Poly.add (Poly.mul (polyDerivative p) q)
                          (Poly.mul p (polyDerivative q)))) = true
        have h_left : polyIsZeroConst (polySimplify
                          (Poly.mul (polyDerivative p) q)) = true := by
          conv => lhs; unfold polySimplify
          by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
          · rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
          · rw [if_neg hsdp, if_pos hsq]; exact polyIsZeroConst_const_zero
        have h_right : polyIsZeroConst (polySimplify
                           (Poly.mul p (polyDerivative q))) = true := by
          conv => lhs; unfold polySimplify
          rw [if_neg hsp, if_pos hsdq]; exact polyIsZeroConst_const_zero
        conv => lhs; unfold polySimplify
        rw [if_pos h_left]
        exact h_right
      · rw [if_neg hsq] at h
        by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · rw [if_pos h1sp] at h
          -- h : deg sq = 0.
          have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
            polyIsOneConst_polyDerivative_zero_after_simplify p h1sp
          have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
            ihq h
          show polyIsZeroConst (polySimplify
                  (Poly.add (Poly.mul (polyDerivative p) q)
                            (Poly.mul p (polyDerivative q)))) = true
          have h_left : polyIsZeroConst (polySimplify
                            (Poly.mul (polyDerivative p) q)) = true := by
            conv => lhs; unfold polySimplify
            rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
          have h_right : polyIsZeroConst (polySimplify
                             (Poly.mul p (polyDerivative q))) = true := by
            conv => lhs; unfold polySimplify
            rw [if_neg hsp, if_pos hsdq]; exact polyIsZeroConst_const_zero
          conv => lhs; unfold polySimplify
          rw [if_pos h_left]
          exact h_right
        · rw [if_neg h1sp] at h
          by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · rw [if_pos h1sq] at h
            have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
              ihp h
            have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
              polyIsOneConst_polyDerivative_zero_after_simplify q h1sq
            show polyIsZeroConst (polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q)))) = true
            have h_left : polyIsZeroConst (polySimplify
                              (Poly.mul (polyDerivative p) q)) = true := by
              conv => lhs; unfold polySimplify
              rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
            have h_right : polyIsZeroConst (polySimplify
                               (Poly.mul p (polyDerivative q))) = true := by
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_pos hsdq]; exact polyIsZeroConst_const_zero
            conv => lhs; unfold polySimplify
            rw [if_pos h_left]
            exact h_right
          · rw [if_neg h1sq] at h
            -- h : deg (mul sp sq) = sp + sq = 0 → both = 0.
            have hsp_zero : degreeUpper (polySimplify p) = 0 := by
              have hsum : degreeUpper (polySimplify p)
                        + degreeUpper (polySimplify q) = 0 := h
              omega
            have hsq_zero : degreeUpper (polySimplify q) = 0 := by
              have hsum : degreeUpper (polySimplify p)
                        + degreeUpper (polySimplify q) = 0 := h
              omega
            have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
              ihp hsp_zero
            have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
              ihq hsq_zero
            show polyIsZeroConst (polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q)))) = true
            have h_left : polyIsZeroConst (polySimplify
                              (Poly.mul (polyDerivative p) q)) = true := by
              conv => lhs; unfold polySimplify
              rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
            have h_right : polyIsZeroConst (polySimplify
                               (Poly.mul p (polyDerivative q))) = true := by
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_pos hsdq]; exact polyIsZeroConst_const_zero
            conv => lhs; unfold polySimplify
            rw [if_pos h_left]
            exact h_right

/-- The polySimplify of a Poly.mul has degreeUpper at most the sum of the
factors' simplified degreeUppers. Top-level version of the local
`inner_mul_bound` previously used inside the non-strict `mul` case; lifted
so the strict-bound `mul` case (below) can reuse it. -/
theorem degreeUpper_polySimplify_mul_le (a b : Poly) :
    degreeUpper (polySimplify (Poly.mul a b))
      ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b) := by
  show degreeUpper
        (if polyIsZeroConst (polySimplify a) = true then Poly.const 0
         else if polyIsZeroConst (polySimplify b) = true then Poly.const 0
         else if polyIsOneConst (polySimplify a) = true then polySimplify b
         else if polyIsOneConst (polySimplify b) = true then polySimplify a
         else (polySimplify a).mul (polySimplify b))
      ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b)
  by_cases hsa : polyIsZeroConst (polySimplify a) = true
  · rw [if_pos hsa]; exact Nat.zero_le _
  · rw [if_neg hsa]
    by_cases hsb : polyIsZeroConst (polySimplify b) = true
    · rw [if_pos hsb]; exact Nat.zero_le _
    · rw [if_neg hsb]
      by_cases h1a : polyIsOneConst (polySimplify a) = true
      · rw [if_pos h1a]
        exact Nat.le_add_left _ _
      · rw [if_neg h1a]
        by_cases h1b : polyIsOneConst (polySimplify b) = true
        · rw [if_pos h1b]
          exact Nat.le_add_right _ _
        · rw [if_neg h1b]
          show degreeUpper ((polySimplify a).mul (polySimplify b))
            ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b)
          exact Nat.le_refl _

/-- Helper: non-strict version of the polySimplify-aware degree bound.
The simplified derivative's degree is at most the simplified original's
degree. Together with the strict version below, this closes both branches
of the compound case analysis for `add` / `sub` / `mul`. -/
theorem polyDerivative_degreeUpper_le_after_simplify (p : Poly) :
    degreeUpper (polySimplify (polyDerivative p))
      ≤ degreeUpper (polySimplify p) := by
  induction p with
  | const _ =>
    -- polyDerivative (const c) = const 0; polySimplify (const 0) = const 0.
    -- polySimplify (const c) = const c. Both degreeUpper = 0.
    exact Nat.le_refl 0
  | var =>
    -- polyDerivative var = const 1; polySimplify (const 1) = const 1.
    -- polySimplify var = var. degreeUpper: 0 ≤ 1.
    exact Nat.zero_le 1
  | add p q ihp ihq =>
    -- Strategy: case on polySimplify (add p q) (3 cases via the zero-const
    -- tests on polySimplify p and polySimplify q), AND on polySimplify (add
    -- (polyDerivative p) (polyDerivative q)) (same 3 cases on polySimplify
    -- of each polyDerivative). In every leaf, ihp + ihq + a Nat.max
    -- inequality close the goal.
    show degreeUpper (polySimplify (Poly.add (polyDerivative p) (polyDerivative q)))
      ≤ degreeUpper (polySimplify (Poly.add p q))
    unfold polySimplify
    -- After unfold, both sides are `if-then-else` chains. We handle the
    -- 3×3 = 9 combinations by nested by_cases. Outer split is on the RHS;
    -- inner on the LHS.
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · -- RHS reduces to polySimplify q.
      rw [if_pos hsp]
      by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
      · rw [if_pos hsdp]; exact ihq
      · rw [if_neg hsdp]
        by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
        · rw [if_pos hsdq]
          -- LHS = polySimplify (polyDerivative p). degreeUpper ≤ degreeUpper (polySimplify p) = 0.
          -- RHS = polySimplify q with degreeUpper ≥ 0. Need bound 0 ≤ degreeUpper (polySimplify q).
          have hsp_zero : degreeUpper (polySimplify p) = 0 :=
            polyIsZeroConst_degreeUpper _ hsp
          calc degreeUpper (polySimplify (polyDerivative p))
              ≤ degreeUpper (polySimplify p) := ihp
            _ = 0 := hsp_zero
            _ ≤ degreeUpper (polySimplify q) := Nat.zero_le _
        · rw [if_neg hsdq]
          -- LHS = add (polySimplify dp) (polySimplify dq). degreeUpper = max.
          show Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                        (degreeUpper (polySimplify (polyDerivative q)))
            ≤ degreeUpper (polySimplify q)
          apply Nat.max_le.mpr
          refine ⟨?_, ihq⟩
          have hsp_zero : degreeUpper (polySimplify p) = 0 :=
            polyIsZeroConst_degreeUpper _ hsp
          calc degreeUpper (polySimplify (polyDerivative p))
              ≤ degreeUpper (polySimplify p) := ihp
            _ = 0 := hsp_zero
            _ ≤ degreeUpper (polySimplify q) := Nat.zero_le _
    · rw [if_neg hsp]
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq]
        -- RHS = polySimplify p. Symmetric to the case above.
        by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
        · rw [if_pos hsdp]
          have hsq_zero : degreeUpper (polySimplify q) = 0 :=
            polyIsZeroConst_degreeUpper _ hsq
          calc degreeUpper (polySimplify (polyDerivative q))
              ≤ degreeUpper (polySimplify q) := ihq
            _ = 0 := hsq_zero
            _ ≤ degreeUpper (polySimplify p) := Nat.zero_le _
        · rw [if_neg hsdp]
          by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
          · rw [if_pos hsdq]; exact ihp
          · rw [if_neg hsdq]
            show Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                          (degreeUpper (polySimplify (polyDerivative q)))
              ≤ degreeUpper (polySimplify p)
            apply Nat.max_le.mpr
            have hsq_zero : degreeUpper (polySimplify q) = 0 :=
              polyIsZeroConst_degreeUpper _ hsq
            refine ⟨ihp, ?_⟩
            calc degreeUpper (polySimplify (polyDerivative q))
                ≤ degreeUpper (polySimplify q) := ihq
              _ = 0 := hsq_zero
              _ ≤ degreeUpper (polySimplify p) := Nat.zero_le _
      · rw [if_neg hsq]
        -- RHS = add (polySimplify p) (polySimplify q). degreeUpper = max.
        by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
        · rw [if_pos hsdp]
          show degreeUpper (polySimplify (polyDerivative q))
            ≤ Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
          exact Nat.le_trans ihq (Nat.le_max_right _ _)
        · rw [if_neg hsdp]
          by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
          · rw [if_pos hsdq]
            show degreeUpper (polySimplify (polyDerivative p))
              ≤ Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
            exact Nat.le_trans ihp (Nat.le_max_left _ _)
          · rw [if_neg hsdq]
            show Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                          (degreeUpper (polySimplify (polyDerivative q)))
              ≤ Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
            apply Nat.max_le.mpr
            exact ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
                   Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | sub p q ihp ihq =>
    -- polySimplify only collapses sub on the right (no zero-left rule for sub).
    -- So this is a 2-way (instead of 3-way) case analysis on both sides.
    show degreeUpper (polySimplify (Poly.sub (polyDerivative p) (polyDerivative q)))
      ≤ degreeUpper (polySimplify (Poly.sub p q))
    unfold polySimplify
    by_cases hsq : polyIsZeroConst (polySimplify q) = true
    · rw [if_pos hsq]
      by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
      · rw [if_pos hsdq]; exact ihp
      · rw [if_neg hsdq]
        show Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                      (degreeUpper (polySimplify (polyDerivative q)))
          ≤ degreeUpper (polySimplify p)
        have hsq_zero : degreeUpper (polySimplify q) = 0 :=
          polyIsZeroConst_degreeUpper _ hsq
        apply Nat.max_le.mpr
        refine ⟨ihp, ?_⟩
        calc degreeUpper (polySimplify (polyDerivative q))
            ≤ degreeUpper (polySimplify q) := ihq
          _ = 0 := hsq_zero
          _ ≤ degreeUpper (polySimplify p) := Nat.zero_le _
    · rw [if_neg hsq]
      by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
      · rw [if_pos hsdq]
        show degreeUpper (polySimplify (polyDerivative p))
          ≤ Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
        exact Nat.le_trans ihp (Nat.le_max_left _ _)
      · rw [if_neg hsdq]
        show Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                      (degreeUpper (polySimplify (polyDerivative q)))
          ≤ Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
        apply Nat.max_le.mpr
        exact ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
               Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | mul p q ihp ihq =>
    -- polyDerivative (mul p q) = add (mul (polyDerivative p) q) (mul p (polyDerivative q)).
    -- 5-way case analysis on polySimplify (Poly.mul p q):
    --   polyIsZeroConst sp  → RHS = const 0; LHS also collapses (via the helper
    --                         polyIsZeroConst_polyDerivative_after_simplify).
    --   polyIsZeroConst sq  → symmetric.
    --   polyIsOneConst sp   → RHS = sq; LHS ≤ sq via ihp/ihq and inner mul bounds.
    --   polyIsOneConst sq   → symmetric.
    --   else                → RHS = sp + sq; LHS ≤ max of inner mul degrees,
    --                         each bounded by sp+sq.
    show degreeUpper (polySimplify (Poly.add (Poly.mul (polyDerivative p) q)
                                              (Poly.mul p (polyDerivative q))))
      ≤ degreeUpper (polySimplify (Poly.mul p q))
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · -- RHS collapses to const 0.
      have hRHS : degreeUpper (polySimplify (Poly.mul p q)) = 0 := by
        have : polyIsZeroConst (polySimplify (Poly.mul p q)) = true := by
          unfold polySimplify
          rw [if_pos hsp]
          exact polyIsZeroConst_const_zero
        exact polyIsZeroConst_degreeUpper _ this
      rw [hRHS]
      -- LHS: both inner muls' polySimplify = const 0, so the outer add's = const 0 too.
      have h_left : polyIsZeroConst (polySimplify
                        (Poly.mul (polyDerivative p) q)) = true := by
        unfold polySimplify
        rw [if_pos (polyIsZeroConst_polyDerivative_after_simplify p hsp)]
        exact polyIsZeroConst_const_zero
      have h_right : polyIsZeroConst (polySimplify
                         (Poly.mul p (polyDerivative q))) = true := by
        unfold polySimplify
        rw [if_pos hsp]
        exact polyIsZeroConst_const_zero
      have hLHS_zero : polyIsZeroConst (polySimplify
          (Poly.add (Poly.mul (polyDerivative p) q)
                    (Poly.mul p (polyDerivative q)))) = true := by
        unfold polySimplify
        rw [if_pos h_left]
        exact h_right
      exact Nat.le_of_eq (polyIsZeroConst_degreeUpper _ hLHS_zero)
    · by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · -- Symmetric to the zero-left case.
        have hRHS : degreeUpper (polySimplify (Poly.mul p q)) = 0 := by
          have : polyIsZeroConst (polySimplify (Poly.mul p q)) = true := by
            unfold polySimplify
            rw [if_neg hsp, if_pos hsq]
            exact polyIsZeroConst_const_zero
          exact polyIsZeroConst_degreeUpper _ this
        rw [hRHS]
        have h_left : polyIsZeroConst (polySimplify
                          (Poly.mul (polyDerivative p) q)) = true := by
          unfold polySimplify
          by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
          · rw [if_pos hsdp]; exact polyIsZeroConst_const_zero
          · rw [if_neg hsdp, if_pos hsq]; exact polyIsZeroConst_const_zero
        have h_right : polyIsZeroConst (polySimplify
                           (Poly.mul p (polyDerivative q))) = true := by
          unfold polySimplify
          rw [if_neg hsp, if_pos (polyIsZeroConst_polyDerivative_after_simplify q hsq)]
          exact polyIsZeroConst_const_zero
        have hLHS_zero : polyIsZeroConst (polySimplify
            (Poly.add (Poly.mul (polyDerivative p) q)
                      (Poly.mul p (polyDerivative q)))) = true := by
          unfold polySimplify
          rw [if_pos h_left]
          exact h_right
        exact Nat.le_of_eq (polyIsZeroConst_degreeUpper _ hLHS_zero)
      · -- Neither sp nor sq is zero const. RHS = sp+sq (or sq when sp=one,
        -- or sp when sq=one). LHS bounded by the inner mul degrees.
        -- Common bound: each inner mul's polySimplify has degreeUpper ≤ sp+sq,
        -- and max(...) is bounded by sp+sq. RHS ≥ sp+sq fails only at the
        -- polyIsOneConst sub-cases, which we handle separately.
        --
        -- Strategy: bound the LHS by sp+sq, then handle each RHS sub-case
        -- separately.
        --
        -- For each inner mul, its polySimplify ≤ (factor1_degree + factor2_degree).
        -- (polyIsZeroConst → 0; polyIsOneConst → the other factor; else → factor1 + factor2.
        --  All ≤ factor1 + factor2.)
        have inner_mul_bound : ∀ a b : Poly,
            degreeUpper (polySimplify (Poly.mul a b))
              ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b) := by
          intro a b
          -- Use show+rfl-after-conv to expose only the LHS's polySimplify expansion;
          -- a blanket `unfold polySimplify` would also unfold the RHS references,
          -- which would obscure `polySimplify a` / `polySimplify b` as `match`
          -- forms and break the show patterns below.
          show degreeUpper
                (if polyIsZeroConst (polySimplify a) = true then Poly.const 0
                 else if polyIsZeroConst (polySimplify b) = true then Poly.const 0
                 else if polyIsOneConst (polySimplify a) = true then polySimplify b
                 else if polyIsOneConst (polySimplify b) = true then polySimplify a
                 else (polySimplify a).mul (polySimplify b))
              ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b)
          by_cases hsa : polyIsZeroConst (polySimplify a) = true
          · rw [if_pos hsa]; exact Nat.zero_le _
          · rw [if_neg hsa]
            by_cases hsb : polyIsZeroConst (polySimplify b) = true
            · rw [if_pos hsb]; exact Nat.zero_le _
            · rw [if_neg hsb]
              by_cases h1a : polyIsOneConst (polySimplify a) = true
              · rw [if_pos h1a]
                exact Nat.le_add_left _ _
              · rw [if_neg h1a]
                by_cases h1b : polyIsOneConst (polySimplify b) = true
                · rw [if_pos h1b]
                  exact Nat.le_add_right _ _
                · rw [if_neg h1b]
                  show degreeUpper ((polySimplify a).mul (polySimplify b))
                    ≤ degreeUpper (polySimplify a) + degreeUpper (polySimplify b)
                  exact Nat.le_refl _
        -- Each inner mul: dispatch.
        have h_a_le : degreeUpper (polySimplify (Poly.mul (polyDerivative p) q))
            ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) :=
          Nat.le_trans (inner_mul_bound (polyDerivative p) q)
            (Nat.add_le_add_right ihp _)
        have h_b_le : degreeUpper (polySimplify (Poly.mul p (polyDerivative q)))
            ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) :=
          Nat.le_trans (inner_mul_bound p (polyDerivative q))
            (Nat.add_le_add_left ihq _)
        -- Outer add: result is one of {a', b', add a' b'}; degreeUpper bounded
        -- by max(degreeUpper a', degreeUpper b'). With both ≤ sp+sq, max ≤ sp+sq.
        have h_outer : degreeUpper (polySimplify
            (Poly.add (Poly.mul (polyDerivative p) q)
                      (Poly.mul p (polyDerivative q))))
              ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
          -- Scope the unfold to the LHS so the RHS's polySimplify references stay
          -- abstracted.
          conv => lhs; unfold polySimplify
          by_cases ha : polyIsZeroConst (polySimplify
              (Poly.mul (polyDerivative p) q)) = true
          · rw [if_pos ha]; exact h_b_le
          · rw [if_neg ha]
            by_cases hb : polyIsZeroConst (polySimplify
                (Poly.mul p (polyDerivative q))) = true
            · rw [if_pos hb]; exact h_a_le
            · rw [if_neg hb]
              exact Nat.max_le.mpr ⟨h_a_le, h_b_le⟩
        -- Now bound the RHS from below by sp + sq in the remaining cases
        -- (polyIsOneConst sp, polyIsOneConst sq, neither).
        by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · -- RHS = sq (polySimplify rule: after if_neg hsp, if_neg hsq, if_pos h1sp).
          -- sp's degreeUpper = 0 from polyIsOneConst_degreeUpper.
          have hsp_zero : degreeUpper (polySimplify p) = 0 :=
            polyIsOneConst_degreeUpper _ h1sp
          have hRHS : degreeUpper (polySimplify (Poly.mul p q))
              = degreeUpper (polySimplify q) := by
            conv => lhs; unfold polySimplify
            rw [if_neg hsp, if_neg hsq, if_pos h1sp]
          rw [hRHS]
          calc degreeUpper (polySimplify
                  (Poly.add (Poly.mul (polyDerivative p) q)
                            (Poly.mul p (polyDerivative q))))
              ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := h_outer
            _ = 0 + degreeUpper (polySimplify q) := by rw [hsp_zero]
            _ = degreeUpper (polySimplify q) := Nat.zero_add _
        · by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · -- RHS = sp.
            have hsq_zero : degreeUpper (polySimplify q) = 0 :=
              polyIsOneConst_degreeUpper _ h1sq
            have hRHS : degreeUpper (polySimplify (Poly.mul p q))
                = degreeUpper (polySimplify p) := by
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_neg hsq, if_neg h1sp, if_pos h1sq]
            rw [hRHS]
            calc degreeUpper (polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q))))
                ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := h_outer
              _ = degreeUpper (polySimplify p) + 0 := by rw [hsq_zero]
              _ = degreeUpper (polySimplify p) := Nat.add_zero _
          · -- RHS = sp + sq directly.
            have hRHS : degreeUpper (polySimplify (Poly.mul p q))
                = degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_neg hsq, if_neg h1sp, if_neg h1sq]
              rfl
            rw [hRHS]
            exact h_outer

/-- **Strict polySimplify-aware degreeUpper bound.** When the simplified
form of `p` has positive syntactic degree (i.e. `p` is not a "trivial"
polynomial that collapses to a constant), the simplified derivative
has strictly smaller syntactic degree.

This is exactly the rate-of-descent the FTA induction needs: Rolle's
theorem gives `# zeros of p ≤ 1 + # zeros of polyDerivative p`, and
this lemma lets the induction terminate. -/
theorem polyDerivative_degreeUpper_lt_after_simplify (p : Poly)
    (hp : degreeUpper (polySimplify p) > 0) :
    degreeUpper (polySimplify (polyDerivative p))
      < degreeUpper (polySimplify p) := by
  induction p with
  | const c =>
    -- polySimplify (const c) = const c; degreeUpper = 0.
    -- Hypothesis `0 > 0` is contradictory.
    show degreeUpper (polySimplify (polyDerivative (Poly.const c)))
      < degreeUpper (polySimplify (Poly.const c))
    -- polySimplify on const is identity; degreeUpper = 0.
    -- The hypothesis degreeUpper (polySimplify (const c)) > 0 is 0 > 0, vacuous.
    exact absurd hp (Nat.lt_irrefl 0)
  | var =>
    -- polySimplify var = var; degreeUpper = 1.
    -- polyDerivative var = const 1; polySimplify (const 1) = const 1; degreeUpper = 0.
    -- 0 < 1.
    show degreeUpper (polySimplify (polyDerivative Poly.var))
      < degreeUpper (polySimplify Poly.var)
    -- Both sides reduce by `rfl`-equivalent unfolding; the relation is 0 < 1.
    exact Nat.zero_lt_one
  | add p q ihp ihq =>
    -- Three sub-cases on polySimplify (add p q):
    --   polyIsZeroConst sp → RHS = degreeUpper sq; LHS collapses via the
    --     polyIsZeroConst_polyDerivative_after_simplify helper to
    --     degreeUpper sdq; strict ihq closes.
    --   polyIsZeroConst sq → symmetric.
    --   else → RHS = max(sp, sq) > 0, so at least one of sp, sq > 0; use the
    --     corresponding strict IH plus the non-strict helper on the other side.
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
        polyIsZeroConst_polyDerivative_after_simplify p hsp
      have hLHS_eq : degreeUpper (polySimplify (polyDerivative (Poly.add p q)))
                   = degreeUpper (polySimplify (polyDerivative q)) := by
        show degreeUpper (polySimplify
                (Poly.add (polyDerivative p) (polyDerivative q)))
             = degreeUpper (polySimplify (polyDerivative q))
        congr 1
        conv => lhs; unfold polySimplify
        rw [if_pos hsdp]
      have hRHS_eq : degreeUpper (polySimplify (Poly.add p q))
                   = degreeUpper (polySimplify q) := by
        congr 1
        conv => lhs; unfold polySimplify
        rw [if_pos hsp]
      rw [hLHS_eq, hRHS_eq]
      rw [hRHS_eq] at hp
      exact ihq hp
    · by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
          polyIsZeroConst_polyDerivative_after_simplify q hsq
        -- The LHS collapse here is symmetric: polyIsZeroConst sdq = true via
        -- helper. polySimplify (add dp dq) checks polyIsZeroConst sdp first;
        -- it MAY be true (then result = sdq = const 0), but otherwise it
        -- checks polyIsZeroConst sdq (true), so result = sdp. Either way
        -- the resulting degreeUpper ≤ degreeUpper sp via the non-strict
        -- helper, and the strict ihp closes against degreeUpper sp > 0.
        have hRHS_eq : degreeUpper (polySimplify (Poly.add p q))
                     = degreeUpper (polySimplify p) := by
          congr 1
          conv => lhs; unfold polySimplify
          rw [if_neg hsp, if_pos hsq]
        rw [hRHS_eq] at hp
        rw [hRHS_eq]
        show degreeUpper (polySimplify
                (Poly.add (polyDerivative p) (polyDerivative q)))
             < degreeUpper (polySimplify p)
        -- LHS bound: ≤ max(degreeUpper sdp, degreeUpper sdq) via the
        -- non-strict helper on each side, then degreeUpper sdq = 0 (helper
        -- + polyIsZeroConst_degreeUpper) and degreeUpper sdp < degreeUpper sp
        -- via strict ihp.
        have hsdq_zero : degreeUpper (polySimplify (polyDerivative q)) = 0 :=
          polyIsZeroConst_degreeUpper _ hsdq
        have hLHS_le_max : degreeUpper (polySimplify
                (Poly.add (polyDerivative p) (polyDerivative q)))
              ≤ Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                         (degreeUpper (polySimplify (polyDerivative q))) := by
          conv => lhs; unfold polySimplify
          by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
          · rw [if_pos hsdp]; exact Nat.le_max_right _ _
          · rw [if_neg hsdp]
            by_cases hsdq' : polyIsZeroConst (polySimplify (polyDerivative q)) = true
            · rw [if_pos hsdq']; exact Nat.le_max_left _ _
            · rw [if_neg hsdq']; exact Nat.le_refl _
        have hLHS_max : Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                                 (degreeUpper (polySimplify (polyDerivative q)))
                      < degreeUpper (polySimplify p) := by
          apply Nat.max_lt.mpr
          refine ⟨ihp hp, ?_⟩
          rw [hsdq_zero]; exact hp
        exact Nat.lt_of_le_of_lt hLHS_le_max hLHS_max
      · -- Neither zero-const. RHS = max(sp, sq).
        have hRHS_eq : degreeUpper (polySimplify (Poly.add p q))
                     = Nat.max (degreeUpper (polySimplify p))
                                (degreeUpper (polySimplify q)) := by
          have : polySimplify (Poly.add p q)
               = Poly.add (polySimplify p) (polySimplify q) := by
            conv => lhs; unfold polySimplify
            rw [if_neg hsp, if_neg hsq]
          rw [this]; rfl
        rw [hRHS_eq] at hp
        rw [hRHS_eq]
        -- LHS ≤ max(sdp, sdq); each side < sp or < sq.
        have hLHS_le_max : degreeUpper (polySimplify
                (Poly.add (polyDerivative p) (polyDerivative q)))
              ≤ Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                         (degreeUpper (polySimplify (polyDerivative q))) := by
          conv => lhs; unfold polySimplify
          by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
          · rw [if_pos hsdp]; exact Nat.le_max_right _ _
          · rw [if_neg hsdp]
            by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
            · rw [if_pos hsdq]; exact Nat.le_max_left _ _
            · rw [if_neg hsdq]; exact Nat.le_refl _
        -- max(sdp, sdq) < max(sp, sq): each side bounded.
        -- If degreeUpper sp > 0: ihp gives sdp < sp.
        -- If degreeUpper sp = 0: non-strict helper gives sdp ≤ 0, so sdp = 0.
        -- Symmetric for sq. At least one of sp, sq > 0 from hp (max > 0).
        have hmax_lt : Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                                 (degreeUpper (polySimplify (polyDerivative q)))
                     < Nat.max (degreeUpper (polySimplify p))
                                (degreeUpper (polySimplify q)) := by
          -- Show both sides of the LHS max are < max(sp, sq) individually.
          -- For each side, dispatch on whether the corresponding sp or sq is 0:
          -- when 0, the side's polyDerivative simplifies to 0 too (via non-strict
          -- helper + polyIsZeroConst_degreeUpper); when > 0, the strict IH applies.
          apply Nat.max_lt.mpr
          refine ⟨?_, ?_⟩
          · -- degreeUpper sdp < max(sp, sq).
            by_cases hsp_pos : degreeUpper (polySimplify p) > 0
            · exact Nat.lt_of_lt_of_le (ihp hsp_pos) (Nat.le_max_left _ _)
            · -- ¬(sp > 0) means sp = 0; sdp ≤ sp = 0 via non-strict helper.
              have hsp_eq : degreeUpper (polySimplify p) = 0 :=
                Nat.le_zero.mp (Nat.not_lt.mp hsp_pos)
              have hsdp_eq : degreeUpper (polySimplify (polyDerivative p)) = 0 :=
                Nat.le_zero.mp (hsp_eq ▸ polyDerivative_degreeUpper_le_after_simplify p)
              rw [hsdp_eq]; exact hp
          · -- degreeUpper sdq < max(sp, sq).
            by_cases hsq_pos : degreeUpper (polySimplify q) > 0
            · exact Nat.lt_of_lt_of_le (ihq hsq_pos) (Nat.le_max_right _ _)
            · have hsq_eq : degreeUpper (polySimplify q) = 0 :=
                Nat.le_zero.mp (Nat.not_lt.mp hsq_pos)
              have hsdq_eq : degreeUpper (polySimplify (polyDerivative q)) = 0 :=
                Nat.le_zero.mp (hsq_eq ▸ polyDerivative_degreeUpper_le_after_simplify q)
              rw [hsdq_eq]; exact hp
        exact Nat.lt_of_le_of_lt hLHS_le_max hmax_lt
  | sub p q ihp ihq =>
    -- 2 sub-cases on polySimplify (sub p q) (sub only collapses on the right):
    --   polyIsZeroConst sq → RHS = degreeUpper sp; LHS reduces via the helper.
    --   else              → RHS = max(sp, sq); LHS bounded as in add's
    --                       "neither" sub-case.
    by_cases hsq : polyIsZeroConst (polySimplify q) = true
    · have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
        polyIsZeroConst_polyDerivative_after_simplify q hsq
      have hRHS_eq : degreeUpper (polySimplify (Poly.sub p q))
                   = degreeUpper (polySimplify p) := by
        congr 1
        conv => lhs; unfold polySimplify
        rw [if_pos hsq]
      have hLHS_eq : degreeUpper (polySimplify (polyDerivative (Poly.sub p q)))
                   = degreeUpper (polySimplify (polyDerivative p)) := by
        show degreeUpper (polySimplify
                (Poly.sub (polyDerivative p) (polyDerivative q)))
             = degreeUpper (polySimplify (polyDerivative p))
        congr 1
        conv => lhs; unfold polySimplify
        rw [if_pos hsdq]
      rw [hLHS_eq, hRHS_eq]
      rw [hRHS_eq] at hp
      exact ihp hp
    · -- ¬polyIsZeroConst sq. RHS = sub sp sq, degreeUpper = max(sp, sq).
      have hRHS_eq : degreeUpper (polySimplify (Poly.sub p q))
                   = Nat.max (degreeUpper (polySimplify p))
                              (degreeUpper (polySimplify q)) := by
        have : polySimplify (Poly.sub p q)
             = Poly.sub (polySimplify p) (polySimplify q) := by
          conv => lhs; unfold polySimplify
          rw [if_neg hsq]
        rw [this]; rfl
      rw [hRHS_eq] at hp
      rw [hRHS_eq]
      -- LHS bound: ≤ max(sdp, sdq) via the sub-of-polyDerivatives rule.
      have hLHS_le_max : degreeUpper (polySimplify
              (Poly.sub (polyDerivative p) (polyDerivative q)))
            ≤ Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                       (degreeUpper (polySimplify (polyDerivative q))) := by
        conv => lhs; unfold polySimplify
        by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
        · rw [if_pos hsdq]; exact Nat.le_max_left _ _
        · rw [if_neg hsdq]; exact Nat.le_refl _
      -- max(sdp, sdq) < max(sp, sq) by the same per-side dispatch as add's
      -- neither sub-case.
      have hmax_lt : Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                               (degreeUpper (polySimplify (polyDerivative q)))
                   < Nat.max (degreeUpper (polySimplify p))
                              (degreeUpper (polySimplify q)) := by
        apply Nat.max_lt.mpr
        refine ⟨?_, ?_⟩
        · by_cases hsp_pos : degreeUpper (polySimplify p) > 0
          · exact Nat.lt_of_lt_of_le (ihp hsp_pos) (Nat.le_max_left _ _)
          · have hsp_eq : degreeUpper (polySimplify p) = 0 :=
              Nat.le_zero.mp (Nat.not_lt.mp hsp_pos)
            have hsdp_eq : degreeUpper (polySimplify (polyDerivative p)) = 0 :=
              Nat.le_zero.mp (hsp_eq ▸ polyDerivative_degreeUpper_le_after_simplify p)
            rw [hsdp_eq]; exact hp
        · by_cases hsq_pos : degreeUpper (polySimplify q) > 0
          · exact Nat.lt_of_lt_of_le (ihq hsq_pos) (Nat.le_max_right _ _)
          · have hsq_eq : degreeUpper (polySimplify q) = 0 :=
              Nat.le_zero.mp (Nat.not_lt.mp hsq_pos)
            have hsdq_eq : degreeUpper (polySimplify (polyDerivative q)) = 0 :=
              Nat.le_zero.mp (hsq_eq ▸ polyDerivative_degreeUpper_le_after_simplify q)
            rw [hsdq_eq]; exact hp
      show degreeUpper (polySimplify
              (Poly.sub (polyDerivative p) (polyDerivative q)))
           < Nat.max (degreeUpper (polySimplify p))
                      (degreeUpper (polySimplify q))
      exact Nat.lt_of_le_of_lt hLHS_le_max hmax_lt
  | mul p q ihp ihq =>
    -- 5 sub-cases on polySimplify (Poly.mul p q):
    --   polyIsZeroConst sp → RHS = 0; hp : 0 > 0 vacuous.
    --   polyIsZeroConst sq → symmetric.
    --   polyIsOneConst sp  → RHS = degreeUpper sq; both inner muls of the
    --                        polyDerivative collapse via the polyIsOneConst
    --                        helper; LHS = sdq; ihq strict closes.
    --   polyIsOneConst sq  → symmetric.
    --   neither            → RHS = sp + sq > 0; the side that's > 0 gets
    --                        the strict IH, the other ≤ via the non-strict
    --                        helper; sum strict-bound via Nat.add_lt_add_of.
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · -- polySimplify (mul p q) = const 0; degreeUpper = 0; hp : 0 > 0.
      exfalso
      have hzero : polyIsZeroConst (polySimplify (Poly.mul p q)) = true := by
        conv => lhs; unfold polySimplify
        rw [if_pos hsp]
        exact polyIsZeroConst_const_zero
      have : degreeUpper (polySimplify (Poly.mul p q)) = 0 :=
        polyIsZeroConst_degreeUpper _ hzero
      rw [this] at hp
      exact Nat.lt_irrefl 0 hp
    · by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · exfalso
        have hzero : polyIsZeroConst (polySimplify (Poly.mul p q)) = true := by
          conv => lhs; unfold polySimplify
          rw [if_neg hsp, if_pos hsq]
          exact polyIsZeroConst_const_zero
        have : degreeUpper (polySimplify (Poly.mul p q)) = 0 :=
          polyIsZeroConst_degreeUpper _ hzero
        rw [this] at hp
        exact Nat.lt_irrefl 0 hp
      · by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · -- polySimplify (mul p q) = polySimplify q (polyIsOneConst sp rule).
          have hRHS_eq : degreeUpper (polySimplify (Poly.mul p q))
                       = degreeUpper (polySimplify q) := by
            congr 1
            conv => lhs; unfold polySimplify
            rw [if_neg hsp, if_neg hsq, if_pos h1sp]
          rw [hRHS_eq] at hp
          rw [hRHS_eq]
          -- Helpers: sdp simplifies to const 0 (polyIsOneConst rule); sp is const 1
          -- so polyIsZeroConst sp = false but polyIsOneConst sp = true.
          have hsdp_zero : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
            polyIsOneConst_polyDerivative_zero_after_simplify p h1sp
          have hsdp_eq : polySimplify (polyDerivative p) = Poly.const 0 :=
            polyIsZeroConst_iff_const_zero _ hsdp_zero
          -- polySimplify (mul dp q) = const 0 (polyIsZeroConst sdp rule).
          have h_left : polySimplify (Poly.mul (polyDerivative p) q)
                      = Poly.const 0 := by
            conv => lhs; unfold polySimplify
            rw [if_pos hsdp_zero]
          -- polySimplify (mul p dq) = polySimplify dq (polyIsOneConst sp rule, after
          -- both polyIsZeroConst tests fail). Case on whether polyIsZeroConst sdq
          -- fires first, which would short-circuit to const 0.
          have hLHS_eq : degreeUpper (polySimplify (polyDerivative (Poly.mul p q)))
                       = degreeUpper (polySimplify (polyDerivative q)) := by
            show degreeUpper (polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q))))
                 = degreeUpper (polySimplify (polyDerivative q))
            -- The outer add reduces to polySimplify (mul p dq) via zero-left collapse
            -- (h_left says polySimplify (mul dp q) = const 0, so polyIsZeroConst = true).
            have h_outer_eq : polySimplify
                  (Poly.add (Poly.mul (polyDerivative p) q)
                            (Poly.mul p (polyDerivative q)))
                = polySimplify (Poly.mul p (polyDerivative q)) := by
              conv => lhs; unfold polySimplify
              have h_left_zero : polyIsZeroConst
                    (polySimplify (Poly.mul (polyDerivative p) q)) = true := by
                rw [h_left]; exact polyIsZeroConst_const_zero
              rw [if_pos h_left_zero]
            rw [h_outer_eq]
            congr 1
            -- polySimplify (mul p dq): sp not zero-const (hsp), polyIsOneConst sp = true.
            conv => lhs; unfold polySimplify
            rw [if_neg hsp]
            by_cases hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true
            · rw [if_pos hsdq]
              -- result = const 0 = polySimplify (polyDerivative q) (via hsdq).
              exact (polyIsZeroConst_iff_const_zero _ hsdq).symm
            · rw [if_neg hsdq, if_pos h1sp]
          rw [hLHS_eq]
          exact ihq hp
        · by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · -- Symmetric to h1sp case.
            have hRHS_eq : degreeUpper (polySimplify (Poly.mul p q))
                         = degreeUpper (polySimplify p) := by
              congr 1
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_neg hsq, if_neg h1sp, if_pos h1sq]
            rw [hRHS_eq] at hp
            rw [hRHS_eq]
            have hsdq_zero : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
              polyIsOneConst_polyDerivative_zero_after_simplify q h1sq
            have hsdq_eq : polySimplify (polyDerivative q) = Poly.const 0 :=
              polyIsZeroConst_iff_const_zero _ hsdq_zero
            have h_right : polySimplify (Poly.mul p (polyDerivative q))
                         = Poly.const 0 := by
              conv => lhs; unfold polySimplify
              rw [if_neg hsp, if_pos hsdq_zero]
            have hLHS_eq : degreeUpper (polySimplify (polyDerivative (Poly.mul p q)))
                         = degreeUpper (polySimplify (polyDerivative p)) := by
              show degreeUpper (polySimplify
                      (Poly.add (Poly.mul (polyDerivative p) q)
                                (Poly.mul p (polyDerivative q))))
                   = degreeUpper (polySimplify (polyDerivative p))
              -- Outer add: polyIsZeroConst left = ?, polyIsZeroConst right = true.
              -- Need to dispatch on left to compute the result.
              have h_outer_eq : polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q)))
                  = polySimplify (Poly.mul (polyDerivative p) q) := by
                conv => lhs; unfold polySimplify
                have h_right_zero : polyIsZeroConst
                      (polySimplify (Poly.mul p (polyDerivative q))) = true := by
                  rw [h_right]; exact polyIsZeroConst_const_zero
                by_cases hldp : polyIsZeroConst
                      (polySimplify (Poly.mul (polyDerivative p) q)) = true
                · rw [if_pos hldp]
                  -- result = polySimplify (mul p dq) = const 0
                  --   = polySimplify (mul dp q) (via hldp).
                  rw [h_right]
                  exact (polyIsZeroConst_iff_const_zero _ hldp).symm
                · rw [if_neg hldp, if_pos h_right_zero]
              rw [h_outer_eq]
              congr 1
              -- polySimplify (mul dp q): sq not zero, polyIsOneConst sq = true.
              conv => lhs; unfold polySimplify
              by_cases hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true
              · rw [if_pos hsdp]
                exact (polyIsZeroConst_iff_const_zero _ hsdp).symm
              · rw [if_neg hsdp, if_neg hsq]
                by_cases h1sdp : polyIsOneConst (polySimplify (polyDerivative p)) = true
                · rw [if_pos h1sdp]
                  -- result = polySimplify q = ? need polySimplify (polyDerivative p).
                  -- polyIsOneConst sdp = true → sdp = const 1.
                  -- degreeUpper sdp ≤ degreeUpper sp via non-strict helper.
                  -- And polyIsOneConst sq = true (h1sq) → sq = const 1.
                  -- So polySimplify q = const 1 = sdp. Hence result equation.
                  have hsdp_one : polySimplify (polyDerivative p) = Poly.const 1 := by
                    cases h : polySimplify (polyDerivative p) with
                    | const c =>
                      unfold polyIsOneConst at h1sdp
                      rw [h] at h1sdp
                      by_cases hc : c = 1
                      · rw [hc]
                      · simp [hc] at h1sdp
                    | var =>
                      rw [h] at h1sdp
                      unfold polyIsOneConst at h1sdp; simp at h1sdp
                    | add _ _ =>
                      rw [h] at h1sdp
                      unfold polyIsOneConst at h1sdp; simp at h1sdp
                    | sub _ _ =>
                      rw [h] at h1sdp
                      unfold polyIsOneConst at h1sdp; simp at h1sdp
                    | mul _ _ =>
                      rw [h] at h1sdp
                      unfold polyIsOneConst at h1sdp; simp at h1sdp
                  have hsq_one : polySimplify q = Poly.const 1 := by
                    cases h : polySimplify q with
                    | const c =>
                      unfold polyIsOneConst at h1sq
                      rw [h] at h1sq
                      by_cases hc : c = 1
                      · rw [hc]
                      · simp [hc] at h1sq
                    | var =>
                      rw [h] at h1sq; unfold polyIsOneConst at h1sq; simp at h1sq
                    | add _ _ =>
                      rw [h] at h1sq; unfold polyIsOneConst at h1sq; simp at h1sq
                    | sub _ _ =>
                      rw [h] at h1sq; unfold polyIsOneConst at h1sq; simp at h1sq
                    | mul _ _ =>
                      rw [h] at h1sq; unfold polyIsOneConst at h1sq; simp at h1sq
                  rw [hsdp_one, hsq_one]
                · rw [if_neg h1sdp, if_pos h1sq]
            rw [hLHS_eq]
            exact ihp hp
          · -- Neither polyIsOneConst sp nor polyIsOneConst sq. RHS = sp + sq.
            have hRHS_eq : degreeUpper (polySimplify (Poly.mul p q))
                         = degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
              have : polySimplify (Poly.mul p q)
                   = Poly.mul (polySimplify p) (polySimplify q) := by
                conv => lhs; unfold polySimplify
                rw [if_neg hsp, if_neg hsq, if_neg h1sp, if_neg h1sq]
              rw [this]; rfl
            rw [hRHS_eq] at hp
            rw [hRHS_eq]
            -- LHS ≤ max of inner mul bounds; each inner mul ≤ sp+sq via degreeUpper_polySimplify_mul_le.
            have h_a : degreeUpper (polySimplify (Poly.mul (polyDerivative p) q))
                     ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) :=
              Nat.le_trans (degreeUpper_polySimplify_mul_le (polyDerivative p) q)
                (Nat.add_le_add_right
                  (polyDerivative_degreeUpper_le_after_simplify p) _)
            have h_b : degreeUpper (polySimplify (Poly.mul p (polyDerivative q)))
                     ≤ degreeUpper (polySimplify p) + degreeUpper (polySimplify q) :=
              Nat.le_trans (degreeUpper_polySimplify_mul_le p (polyDerivative q))
                (Nat.add_le_add_left
                  (polyDerivative_degreeUpper_le_after_simplify q) _)
            -- For STRICT: dispatch on which factor has degreeUpper > 0.
            -- The side that's > 0 admits the strict IH; the other uses ≤.
            have h_strict : degreeUpper (polySimplify
                  (Poly.add (Poly.mul (polyDerivative p) q)
                            (Poly.mul p (polyDerivative q))))
                  < degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
              -- The outer add's result is one of {a', b', add a' b'}; degreeUpper ≤ max(a', b').
              have h_outer : degreeUpper (polySimplify
                    (Poly.add (Poly.mul (polyDerivative p) q)
                              (Poly.mul p (polyDerivative q))))
                  ≤ Nat.max (degreeUpper (polySimplify
                          (Poly.mul (polyDerivative p) q)))
                            (degreeUpper (polySimplify
                          (Poly.mul p (polyDerivative q)))) := by
                conv => lhs; unfold polySimplify
                by_cases hla : polyIsZeroConst (polySimplify
                      (Poly.mul (polyDerivative p) q)) = true
                · rw [if_pos hla]; exact Nat.le_max_right _ _
                · rw [if_neg hla]
                  by_cases hlb : polyIsZeroConst (polySimplify
                        (Poly.mul p (polyDerivative q))) = true
                  · rw [if_pos hlb]; exact Nat.le_max_left _ _
                  · rw [if_neg hlb]; exact Nat.le_refl _
              -- Now show max(a', b') < sp + sq, using strict IH on at least one side.
              -- Dispatch on which factor has degreeUpper > 0. Cases B/C
              -- (asymmetric) close via the polyDerivative_zero_when_simplified_degree_zero
              -- helper, which forces the outer polySimplify (add a' b') to
              -- collapse via zero-right when the "small" side has deg 0.
              by_cases hsp_pos : degreeUpper (polySimplify p) > 0
              · by_cases hsq_pos : degreeUpper (polySimplify q) > 0
                · -- Case A: both > 0. Each strict IH gives strict on its inner mul.
                  -- max_lt closes.
                  have h_a_strict :
                      degreeUpper (polySimplify (Poly.mul (polyDerivative p) q))
                    < degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
                    apply Nat.lt_of_le_of_lt
                      (degreeUpper_polySimplify_mul_le (polyDerivative p) q)
                    exact Nat.add_lt_add_right (ihp hsp_pos) _
                  have h_b_strict :
                      degreeUpper (polySimplify (Poly.mul p (polyDerivative q)))
                    < degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
                    apply Nat.lt_of_le_of_lt
                      (degreeUpper_polySimplify_mul_le p (polyDerivative q))
                    exact Nat.add_lt_add_left (ihq hsq_pos) _
                  exact Nat.lt_of_le_of_lt h_outer
                    (Nat.max_lt.mpr ⟨h_a_strict, h_b_strict⟩)
                · -- Case B: sp > 0 ∧ sq = 0. Use the helper to force b' = const 0,
                  -- which makes the outer collapse to a' < sp + sq via ihp.
                  have hsq_eq : degreeUpper (polySimplify q) = 0 :=
                    Nat.le_zero.mp (Nat.not_lt.mp hsq_pos)
                  have hsdq : polyIsZeroConst (polySimplify (polyDerivative q)) = true :=
                    polyDerivative_zero_when_simplified_degree_zero q hsq_eq
                  have h_b_zero : polyIsZeroConst (polySimplify
                                      (Poly.mul p (polyDerivative q))) = true := by
                    conv => lhs; unfold polySimplify
                    rw [if_neg hsp, if_pos hsdq]
                    exact polyIsZeroConst_const_zero
                  -- Outer polySimplify (add a' b'): polyIsZeroConst a' = ? polyIsZeroConst b' = true.
                  -- If polyIsZeroConst a' = true: LHS = b' = 0 < sp + sq (sp > 0).
                  -- If polyIsZeroConst a' = false: LHS = a' < sp + sq via h_a_strict.
                  have h_a_strict :
                      degreeUpper (polySimplify (Poly.mul (polyDerivative p) q))
                    < degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
                    apply Nat.lt_of_le_of_lt
                      (degreeUpper_polySimplify_mul_le (polyDerivative p) q)
                    exact Nat.add_lt_add_right (ihp hsp_pos) _
                  have h_outer_collapse :
                      degreeUpper (polySimplify
                        (Poly.add (Poly.mul (polyDerivative p) q)
                                  (Poly.mul p (polyDerivative q))))
                    ≤ degreeUpper (polySimplify (Poly.mul (polyDerivative p) q)) := by
                    conv => lhs; unfold polySimplify
                    by_cases hla : polyIsZeroConst (polySimplify
                          (Poly.mul (polyDerivative p) q)) = true
                    · rw [if_pos hla]
                      -- result = polySimplify (mul p dq). degreeUpper = 0 via h_b_zero.
                      have hb_zero_deg : degreeUpper (polySimplify
                              (Poly.mul p (polyDerivative q))) = 0 :=
                        polyIsZeroConst_degreeUpper _ h_b_zero
                      rw [hb_zero_deg]; exact Nat.zero_le _
                    · rw [if_neg hla, if_pos h_b_zero]; exact Nat.le_refl _
                  exact Nat.lt_of_le_of_lt h_outer_collapse h_a_strict
              · -- Case C: sp = 0 ∧ sq > 0. Symmetric to B.
                have hsp_eq : degreeUpper (polySimplify p) = 0 :=
                  Nat.le_zero.mp (Nat.not_lt.mp hsp_pos)
                rw [hsp_eq, Nat.zero_add] at hp
                have hsq_pos : degreeUpper (polySimplify q) > 0 := hp
                have hsdp : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
                  polyDerivative_zero_when_simplified_degree_zero p hsp_eq
                have h_a_zero : polyIsZeroConst (polySimplify
                                    (Poly.mul (polyDerivative p) q)) = true := by
                  conv => lhs; unfold polySimplify
                  rw [if_pos hsdp]
                  exact polyIsZeroConst_const_zero
                have h_b_strict :
                    degreeUpper (polySimplify (Poly.mul p (polyDerivative q)))
                  < degreeUpper (polySimplify p) + degreeUpper (polySimplify q) := by
                  apply Nat.lt_of_le_of_lt
                    (degreeUpper_polySimplify_mul_le p (polyDerivative q))
                  exact Nat.add_lt_add_left (ihq hsq_pos) _
                have h_outer_collapse :
                    degreeUpper (polySimplify
                      (Poly.add (Poly.mul (polyDerivative p) q)
                                (Poly.mul p (polyDerivative q))))
                  ≤ degreeUpper (polySimplify (Poly.mul p (polyDerivative q))) := by
                  conv => lhs; unfold polySimplify
                  rw [if_pos h_a_zero]; exact Nat.le_refl _
                exact Nat.lt_of_le_of_lt h_outer_collapse h_b_strict
            exact h_strict

/-! ## Helpers for the FTA bound proof (chunk 3 prep)

`degreeUpper_polySimplify_le_self` and `eval_constant_when_degreeUpper_zero`
let us bridge the effective degree (degreeUpper of polySimplify) to the
syntactic degree, and let us conclude that a polynomial with effective
degree 0 evaluates to a constant. Both are used in the FTA constructive
proof below. -/

/-- polySimplify can only collapse, never expand: the simplified
polynomial's syntactic degreeUpper is at most the original's. -/
theorem degreeUpper_polySimplify_le_self (p : Poly) :
    degreeUpper (polySimplify p) ≤ degreeUpper p := by
  induction p with
  | const _ => exact Nat.le_refl 0
  | var => exact Nat.le_refl 1
  | add p q ihp ihq =>
    conv => lhs; unfold polySimplify
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hsp]
      exact Nat.le_trans ihq (Nat.le_max_right _ _)
    · rw [if_neg hsp]
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq]
        exact Nat.le_trans ihp (Nat.le_max_left _ _)
      · rw [if_neg hsq]
        show Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
          ≤ Nat.max (degreeUpper p) (degreeUpper q)
        exact Nat.max_le.mpr ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
                              Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | sub p q ihp ihq =>
    conv => lhs; unfold polySimplify
    by_cases hsq : polyIsZeroConst (polySimplify q) = true
    · rw [if_pos hsq]
      exact Nat.le_trans ihp (Nat.le_max_left _ _)
    · rw [if_neg hsq]
      show Nat.max (degreeUpper (polySimplify p)) (degreeUpper (polySimplify q))
        ≤ Nat.max (degreeUpper p) (degreeUpper q)
      exact Nat.max_le.mpr ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
                            Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | mul p q ihp ihq =>
    conv => lhs; unfold polySimplify
    by_cases hsp : polyIsZeroConst (polySimplify p) = true
    · rw [if_pos hsp]; exact Nat.zero_le _
    · rw [if_neg hsp]
      by_cases hsq : polyIsZeroConst (polySimplify q) = true
      · rw [if_pos hsq]; exact Nat.zero_le _
      · rw [if_neg hsq]
        by_cases h1sp : polyIsOneConst (polySimplify p) = true
        · rw [if_pos h1sp]
          show degreeUpper (polySimplify q) ≤ degreeUpper p + degreeUpper q
          exact Nat.le_trans ihq (Nat.le_add_left _ _)
        · rw [if_neg h1sp]
          by_cases h1sq : polyIsOneConst (polySimplify q) = true
          · rw [if_pos h1sq]
            show degreeUpper (polySimplify p) ≤ degreeUpper p + degreeUpper q
            exact Nat.le_trans ihp (Nat.le_add_right _ _)
          · rw [if_neg h1sq]
            show degreeUpper (polySimplify p) + degreeUpper (polySimplify q)
              ≤ degreeUpper p + degreeUpper q
            exact Nat.add_le_add ihp ihq

/-- A polynomial with syntactic degreeUpper 0 evaluates to a constant
(doesn't depend on the input). Used in the FTA base case to conclude
that a polynomial with effective degree 0 and a non-zero witness has
no roots. -/
theorem eval_constant_when_degreeUpper_zero (p : Poly) (h : degreeUpper p = 0)
    (x y : Real) :
    Poly.eval p x = Poly.eval p y := by
  induction p with
  | const c => rfl
  | var =>
    -- degreeUpper var = 1; h : 1 = 0 is impossible.
    unfold degreeUpper at h
    exact absurd h (by decide)
  | add p q ihp ihq =>
    have hmax : Nat.max (degreeUpper p) (degreeUpper q) = 0 := h
    have hp_zero : degreeUpper p = 0 :=
      Nat.le_zero.mp (hmax ▸ Nat.le_max_left _ _)
    have hq_zero : degreeUpper q = 0 :=
      Nat.le_zero.mp (hmax ▸ Nat.le_max_right _ _)
    show Poly.eval p x + Poly.eval q x = Poly.eval p y + Poly.eval q y
    rw [ihp hp_zero, ihq hq_zero]
  | sub p q ihp ihq =>
    have hmax : Nat.max (degreeUpper p) (degreeUpper q) = 0 := h
    have hp_zero : degreeUpper p = 0 :=
      Nat.le_zero.mp (hmax ▸ Nat.le_max_left _ _)
    have hq_zero : degreeUpper q = 0 :=
      Nat.le_zero.mp (hmax ▸ Nat.le_max_right _ _)
    show Poly.eval p x - Poly.eval q x = Poly.eval p y - Poly.eval q y
    rw [ihp hp_zero, ihq hq_zero]
  | mul p q ihp ihq =>
    have hsum : degreeUpper p + degreeUpper q = 0 := h
    have hp_zero : degreeUpper p = 0 := by omega
    have hq_zero : degreeUpper q = 0 := by omega
    show Poly.eval p x * Poly.eval q x = Poly.eval p y * Poly.eval q y
    rw [ihp hp_zero, ihq hq_zero]

/-- If `polyDerivative p` evaluates to 0 everywhere, then `p` evaluates to
a constant. Proof: for any two real points, apply MVT to `Poly.eval p`;
the derivative at the witness c equals `Poly.eval (polyDerivative p) c = 0`
by `polyHasDerivAt_eval`, so the MVT identity `f(b) - f(a) = f'(c)(b - a)`
collapses to `f(b) = f(a)`. -/
theorem polyDerivative_zero_implies_eval_constant (p : Poly)
    (h_deriv_zero : ∀ x : Real, Poly.eval (polyDerivative p) x = 0) :
    ∀ x y : Real, Poly.eval p x = Poly.eval p y := by
  -- Trichotomy on the two points.
  have h_aux : ∀ a b : Real, a < b → Poly.eval p a = Poly.eval p b := by
    intro a b hab
    -- Apply MVT on (a, b).
    have hdiff : ∀ c : Real, a ≤ c → c ≤ b →
        ∃ f' : Real, MachLib.Real.HasDerivAt (Poly.eval p) f' c := by
      intro c _ _
      exact ⟨Poly.eval (polyDerivative p) c, polyHasDerivAt_eval p c⟩
    obtain ⟨c, f'_c, hca, hcb, hf'_c, hmvt⟩ :=
      MachLib.Real.mean_value_theorem_ct (Poly.eval p) a b hab hdiff
    -- hf'_c : HasDerivAt (Poly.eval p) f'_c c.
    -- By polyHasDerivAt_eval, the derivative at c is Poly.eval (polyDerivative p) c = 0.
    -- HasDerivAt_unique gives f'_c = 0.
    have hderiv_at_c : MachLib.Real.HasDerivAt (Poly.eval p)
                          (Poly.eval (polyDerivative p) c) c :=
      polyHasDerivAt_eval p c
    have hf'_c_zero : f'_c = Poly.eval (polyDerivative p) c :=
      MachLib.Real.HasDerivAt_unique (Poly.eval p) f'_c
        (Poly.eval (polyDerivative p) c) c hf'_c hderiv_at_c
    rw [h_deriv_zero c] at hf'_c_zero
    -- hf'_c_zero : f'_c = 0.
    -- hmvt : Poly.eval p b - Poly.eval p a = f'_c * (b - a).
    rw [hf'_c_zero, zero_mul] at hmvt
    -- hmvt : Poly.eval p b - Poly.eval p a = 0.
    -- Conclude Poly.eval p b = Poly.eval p a.
    have h_eq : Poly.eval p b - Poly.eval p a = 0 := hmvt
    -- a - b = 0 → a = b. Use sub_def + add_neg.
    have : Poly.eval p b = Poly.eval p a + (Poly.eval p b - Poly.eval p a) := by
      rw [sub_def]
      calc Poly.eval p b
          = Poly.eval p b + 0 := (add_zero _).symm
        _ = Poly.eval p b + (-Poly.eval p a + Poly.eval p a) := by rw [neg_add_self]
        _ = (Poly.eval p b + -Poly.eval p a) + Poly.eval p a := by rw [← add_assoc]
        _ = Poly.eval p a + (Poly.eval p b + -Poly.eval p a) := add_comm _ _
    rw [h_eq, add_zero] at this
    exact this.symm
  -- Trichotomy: x < y, x = y (trivial), or y < x.
  intro x y
  rcases lt_total x y with hxy | hxy | hxy
  · exact h_aux x y hxy
  · rw [hxy]
  · exact (h_aux y x hxy).symm

/-! ## Polynomial fundamental theorem of algebra — constructive proof (chunk 3)

Khovanskii sprint week 1 chunk 3 (2026-06-11). Strong induction on the
effective degree `degreeUpper (polySimplify p)`. Base case (effDeg 0):
the polynomial evaluates to a constant; combined with `hne`, this
constant is non-zero, so no roots. Inductive step: case on whether
`polyDerivative p` is identically zero. If yes, `p` evaluates to a
constant (via MVT helper). If no, apply Rolle's `zero_count_bound_by_deriv`
with the strict degreeUpper bound from chunk 2 and the IH on the
derivative. -/

/-- Auxiliary effective-degree FTA bound, by strong induction on n. The
visible `poly_root_count_bound` below derives the syntactic-degree
form via `degreeUpper_polySimplify_le_self`. -/
theorem poly_root_count_bound_eff_aux :
    ∀ n : Nat, ∀ p : Poly,
    degreeUpper (polySimplify p) = n →
    ∀ a b : Real, a < b →
    (∃ x : Real, Poly.eval p x ≠ 0) →
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Poly.eval p z = 0) →
      zeros.length ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p heff a b hab hne zeros hnodup hzeros
    by_cases hn : n = 0
    · -- Base case: effDeg p = 0. polySimplify p evaluates to a constant.
      -- Combined with hne, that constant is non-zero ⇒ no roots.
      rw [hn] at heff
      have hconst : ∀ x y : Real,
          Poly.eval (polySimplify p) x = Poly.eval (polySimplify p) y :=
        fun x y => eval_constant_when_degreeUpper_zero (polySimplify p) heff x y
      have hp_const : ∀ x y : Real, Poly.eval p x = Poly.eval p y := by
        intro x y
        rw [← polySimplify_eval p x, ← polySimplify_eval p y]
        exact hconst x y
      obtain ⟨x_0, hx_0⟩ := hne
      have hp_ne : ∀ z : Real, Poly.eval p z ≠ 0 := by
        intro z hz_eq
        apply hx_0
        rw [hp_const x_0 z]; exact hz_eq
      cases zeros with
      | nil => rw [hn]; exact Nat.zero_le _
      | cons z rest =>
        have hz_in : z ∈ z :: rest := List.mem_cons_self _ _
        have := hzeros z hz_in
        exact absurd this.2.2 (hp_ne z)
    · -- Inductive step: n > 0.
      have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
      by_cases hderiv_zero : ∀ x : Real, Poly.eval (polyDerivative p) x = 0
      · -- polyDerivative p is identically 0 ⇒ p evaluates to a constant.
        have hp_const : ∀ x y : Real, Poly.eval p x = Poly.eval p y :=
          polyDerivative_zero_implies_eval_constant p hderiv_zero
        obtain ⟨x_0, hx_0⟩ := hne
        have hp_ne : ∀ z : Real, Poly.eval p z ≠ 0 := by
          intro z hz_eq
          apply hx_0
          rw [hp_const x_0 z]; exact hz_eq
        cases zeros with
        | nil => exact Nat.zero_le _
        | cons z rest =>
          have hz_in : z ∈ z :: rest := List.mem_cons_self _ _
          have := hzeros z hz_in
          exact absurd this.2.2 (hp_ne z)
      · -- polyDerivative p has NonzeroWitness (extract classically).
        have hne_dp : ∃ x : Real, Poly.eval (polyDerivative p) x ≠ 0 := by
          apply Classical.byContradiction
          intro h_all
          apply hderiv_zero
          intro x
          apply Classical.byContradiction
          intro hne_x
          apply h_all
          exact ⟨x, hne_x⟩
        -- effDeg(polyDerivative p) < n via the chunk-2 strict bound.
        have hpd_eff : degreeUpper (polySimplify (polyDerivative p)) < n := by
          rw [← heff]
          have hp_pos : degreeUpper (polySimplify p) > 0 := heff ▸ hn_pos
          exact polyDerivative_degreeUpper_lt_after_simplify p hp_pos
        -- IH on polyDerivative p.
        have ih_dp : ∀ zeros_dp : List Real,
            zeros_dp.Nodup →
            (∀ z ∈ zeros_dp, a < z ∧ z < b ∧ Poly.eval (polyDerivative p) z = 0) →
            zeros_dp.length ≤ degreeUpper (polySimplify (polyDerivative p)) :=
          ih _ hpd_eff (polyDerivative p) rfl a b hab hne_dp
        -- Translate ih_dp into hf'_bound form (HasDerivAt language).
        have hf'_bound : ∀ zeros_f' : List Real,
            zeros_f'.Nodup →
            (∀ z ∈ zeros_f', a < z ∧ z < b ∧
              ∃ f'' : Real, MachLib.Real.HasDerivAt (Poly.eval p) f'' z ∧ f'' = 0) →
            zeros_f'.length ≤ degreeUpper (polySimplify (polyDerivative p)) := by
          intro zeros_f' hnodup_f' hzeros_f'
          apply ih_dp zeros_f' hnodup_f'
          intro z hz_in
          obtain ⟨ha_z, hb_z, f'', hderiv, hf''_zero⟩ := hzeros_f' z hz_in
          refine ⟨ha_z, hb_z, ?_⟩
          have hderiv_poly : MachLib.Real.HasDerivAt (Poly.eval p)
                                (Poly.eval (polyDerivative p) z) z :=
            polyHasDerivAt_eval p z
          have h_eq : f'' = Poly.eval (polyDerivative p) z :=
            MachLib.Real.HasDerivAt_unique (Poly.eval p) f''
              (Poly.eval (polyDerivative p) z) z hderiv hderiv_poly
          rw [← h_eq]; exact hf''_zero
        have hdiff : ∀ c : Real, a < c → c < b →
            ∃ f' : Real, MachLib.Real.HasDerivAt (Poly.eval p) f' c := by
          intro c _ _
          exact ⟨Poly.eval (polyDerivative p) c, polyHasDerivAt_eval p c⟩
        have h_bound : zeros.length
                     ≤ degreeUpper (polySimplify (polyDerivative p)) + 1 :=
          MachLib.Real.zero_count_bound_by_deriv (Poly.eval p) a b hab hdiff
            (degreeUpper (polySimplify (polyDerivative p))) hf'_bound
            zeros hnodup hzeros
        exact Nat.le_trans h_bound hpd_eff

/-- **Polynomial FTA bound (constructive theorem, chunk 3).**

A polynomial `p` with at least one non-zero value has at most
`degreeUpper p` distinct zeros on any bounded open interval `(a, b)`.

Derived from `poly_root_count_bound_eff_aux` via
`degreeUpper_polySimplify_le_self`. Replaces the prior axiom of the
same name (chunk 3 close, 2026-06-11). -/
theorem poly_root_count_bound (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval p x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Poly.eval p z = 0) →
      zeros.length ≤ degreeUpper p := by
  intro zeros hnodup hzeros
  have h_eff : zeros.length ≤ degreeUpper (polySimplify p) :=
    poly_root_count_bound_eff_aux (degreeUpper (polySimplify p)) p rfl a b hab
      hne zeros hnodup hzeros
  exact Nat.le_trans h_eff (degreeUpper_polySimplify_le_self p)

end PolynomialRootCount
end MachLib
