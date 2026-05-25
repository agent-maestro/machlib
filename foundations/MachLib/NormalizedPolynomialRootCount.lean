import MachLib.PolynomialRootCount

/-!
MachLib.NormalizedPolynomialRootCount — coefficient-list root-count scaffold.

This module starts the normalized-polynomial route needed for a future
degree/root-count induction. It deliberately proves only the tiny checked
footholds currently supported by MachLib's local foundations:

* coefficient-list evaluation;
* a syntactic normalized-degree upper bound;
* a nonzero constant polynomial has no roots;
* the exact induction target shape for future work.

It does not prove the general polynomial root-count theorem.
-/

namespace MachLib
namespace NormalizedPolynomialRootCount

open MachLib.Real

/-- Coefficient-list polynomials, stored low-to-high:
`[a0, a1, a2]` means `a0 + a1*x + a2*x*x`.

This is a normal-form target, separate from the existing expression AST.
-/
abbrev CoeffPoly := List Real

/-- Evaluate a coefficient-list polynomial by Horner recursion. -/
noncomputable def eval : CoeffPoly → Real → Real
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

/-- A point is a root of a coefficient-list polynomial. -/
def Root (p : CoeffPoly) (x : Real) : Prop :=
  eval p x = 0

/-- A coefficient-list polynomial has a witness that it is not the zero
function. This is intentionally semantic; future work should connect it to
normal-form leading-coefficient evidence. -/
def NonzeroWitness (p : CoeffPoly) : Prop :=
  ∃ x : Real, eval p x ≠ 0

/-- The last coefficient is nonzero. This is the minimal normalized-list
predicate needed before degree induction can be trusted. -/
def LastNonzero : CoeffPoly → Prop
  | [] => False
  | [c] => c ≠ 0
  | _ :: cs => LastNonzero cs

/-- Syntactic degree upper bound for coefficient lists. For normalized nonzero
lists this is intended to become exact degree, but that exactness is not proved
here. -/
def degreeBound : CoeffPoly → Nat
  | [] => 0
  | [_] => 0
  | _ :: cs => Nat.succ (degreeBound cs)

/-- Finite root-list soundness for coefficient-list polynomials. -/
def RootListSound (p : CoeffPoly) (roots : List Real) : Prop :=
  ∀ x : Real, Root p x → x ∈ roots

/-- Duplicate-free root list predicate mirroring the AST packet layer. -/
def RootListDistinct : List Real → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ RootListDistinct xs

/-- Root-list length respects the coefficient-list degree bound. -/
def RootListDegreeBound (p : CoeffPoly) (roots : List Real) : Prop :=
  roots.length ≤ degreeBound p

/-- The normalized finite-root packet shape for future induction. -/
structure NormalizedFiniteRootPacket where
  coeffs : CoeffPoly
  normalized : LastNonzero coeffs
  roots : List Real
  sound : RootListSound coeffs roots
  distinct : RootListDistinct roots
  degree_bound : RootListDegreeBound coeffs roots

/-- Empty coefficient lists evaluate to zero. -/
theorem eval_nil (x : Real) :
    eval [] x = 0 := rfl

/-- Singleton coefficient lists evaluate to their constant. -/
theorem eval_singleton (c x : Real) :
    eval [c] x = c := by
  unfold eval
  change c + x * 0 = c
  rw [mul_zero, add_zero]

/-- Singleton coefficient lists have degree bound zero. -/
theorem degreeBound_singleton (c : Real) :
    degreeBound [c] = 0 := rfl

/-- A nonzero singleton coefficient list is normalized. -/
theorem singleton_lastNonzero {c : Real} (hc : c ≠ 0) :
    LastNonzero [c] := hc

/-- A nonzero constant coefficient-list polynomial has no roots. -/
theorem nonzeroConstant_no_root {c x : Real} (hc : c ≠ 0) :
    ¬ Root [c] x := by
  intro h
  unfold Root at h
  rw [eval_singleton] at h
  exact hc h

/-- The empty root list is sound for a nonzero constant polynomial. -/
theorem nonzeroConstant_emptyRootListSound {c : Real} (hc : c ≠ 0) :
    RootListSound [c] [] := by
  intro x hx
  exact False.elim (nonzeroConstant_no_root (c := c) (x := x) hc hx)

/-- The empty root list is distinct. -/
theorem emptyRootListDistinct :
    RootListDistinct ([] : List Real) := by
  simp [RootListDistinct]

/-- The empty root list is bounded by the degree of a nonzero constant. -/
theorem nonzeroConstant_emptyRootListDegreeBound (c : Real) :
    RootListDegreeBound [c] [] := by
  simp [RootListDegreeBound, degreeBound_singleton]

/-- Checked finite-root packet for a nonzero constant polynomial. -/
noncomputable def nonzeroConstantFiniteRootPacket
    (c : Real) (hc : c ≠ 0) : NormalizedFiniteRootPacket where
  coeffs := [c]
  normalized := singleton_lastNonzero hc
  roots := []
  sound := nonzeroConstant_emptyRootListSound hc
  distinct := emptyRootListDistinct
  degree_bound := nonzeroConstant_emptyRootListDegreeBound c

/-- The future induction claim shape. It is a definition of the target
property, not a proved theorem. -/
def RootCountInductionTarget : Prop :=
  ∀ p : CoeffPoly,
    LastNonzero p →
    ∃ roots : List Real,
      RootListSound p roots ∧
      RootListDistinct roots ∧
      RootListDegreeBound p roots

end NormalizedPolynomialRootCount
end MachLib
