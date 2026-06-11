import MachLib.FiniteZeroPacket
import MachLib.Differentiation

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

/-! ## Polynomial fundamental theorem of algebra (axiomatized) -/

/-- **Polynomial FTA bound.** A non-zero polynomial `p` has at most
`degreeUpper p` distinct zeros on any bounded open interval `(a, b)`.

The classical proof: induct on degree. Base case (degree 0): non-zero
constant has 0 zeros. Inductive step (degree d > 0): if `p` has a root
`r`, factor `p = (x - r) * q` with `degreeUpper q ≤ d - 1` by polynomial
division. By IH, `q` has ≤ d - 1 zeros. So `p` has ≤ 1 + (d - 1) = d
zeros. Alternatively: use Rolle's theorem + induction on degree via
`(Poly.derivative p)` (degreeUpper drops by 1).

Axiomatized for now; constructive proof requires polynomial division
infrastructure (~200 lines) OR a `Poly.derivative` + Rolle chain
(~150 lines). Both are substantive standalone artifacts. -/
axiom poly_root_count_bound (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval p x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Poly.eval p z = 0) →
      zeros.length ≤ degreeUpper p

end PolynomialRootCount
end MachLib
