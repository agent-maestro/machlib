import MachLib.FiniteZeroPacket

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

end PolynomialRootCount
end MachLib
