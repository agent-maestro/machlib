import MachLib.PolynomialRootCount
import MachLib.Ring

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
open MachLib.PolynomialEvidence

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

/-- Coefficient-list version of the linear factor `(x - r)`, stored low-to-high. -/
noncomputable def linearCoeff (r : Real) : CoeffPoly :=
  [-r, 1]

/-- A small monic quadratic coefficient-list example, stored low-to-high. -/
noncomputable def monicQuadraticCoeff (a b : Real) : CoeffPoly :=
  [a, b, 1]

/-- Explicit coefficient-list product of two linear factors. -/
noncomputable def linearLinearCoeff (r s : Real) : CoeffPoly :=
  [(-r) * (-s), (-r) * 1 + 1 * (-s), 1]

/-- Explicit coefficient-list product of three linear factors, represented
through a staging coefficient list. -/
noncomputable def stagedTripleLinearCoeff (r s t : Real) : CoeffPoly :=
  [((-r) * (-s)) * (-t),
   ((-r) * (-s)) * 1 + ((-r) * 1 + 1 * (-s)) * (-t),
   ((-r) * 1 + 1 * (-s)) * 1 + 1 * (-t),
   1]

/-- Explicit constant-scale linear product. -/
noncomputable def scaledLinearCoeff (a r : Real) : CoeffPoly :=
  [a * (-r), a]

/-- Explicit linear times monic-quadratic product. -/
noncomputable def linearQuadraticCoeff (r a b : Real) : CoeffPoly :=
  [(-r) * a, (-r) * b + 1 * a, (-r) * 1 + 1 * b, 1]

/-- Drop trailing zero coefficients from a low-to-high coefficient list.
This is intentionally tiny and list-shaped; it does not prove full polynomial
canonical-form uniqueness. -/
noncomputable def normalizeCoeff : CoeffPoly → CoeffPoly
  | [] => []
  | c :: cs =>
      by
        classical
        let rest := normalizeCoeff cs
        exact if rest = [] then
          if c = 0 then [] else [c]
        else
          c :: rest

/-- Pointwise coefficient-list addition. Missing coefficients are treated as
zero, so this is the normalized-list substrate for polynomial addition. -/
noncomputable def addCoeff : CoeffPoly → CoeffPoly → CoeffPoly
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => (c + d) :: addCoeff cs ds

/-- Multiply every coefficient by a scalar. -/
noncomputable def scalarMulCoeff (a : Real) : CoeffPoly → CoeffPoly
  | [] => []
  | c :: cs => (a * c) :: scalarMulCoeff a cs

/-- Multiply a coefficient list by `x`, i.e. shift coefficients up by one
degree. -/
noncomputable def shiftCoeff (p : CoeffPoly) : CoeffPoly :=
  0 :: p

/-- Recursive coefficient-list convolution. For `p = c + x*cs`, the product
with `q` is `c*q + x*(cs*q)`. -/
noncomputable def mulCoeff : CoeffPoly → CoeffPoly → CoeffPoly
  | [], _ => []
  | c :: cs, q => addCoeff (scalarMulCoeff c q) (shiftCoeff (mulCoeff cs q))

/-- Named normalized product output. -/
noncomputable def normalizedProductCoeff (p q : CoeffPoly) : CoeffPoly :=
  normalizeCoeff (mulCoeff p q)

/-- A semantic product certificate. It avoids claiming we have a complete
coefficient-list convolution normalizer yet: a candidate product list is
accepted only when its evaluator is pointwise equal to the product of the
operand evaluators. -/
def MulEvalSound (product p q : CoeffPoly) : Prop :=
  ∀ x : Real, eval product x = eval p x * eval q x

/-- Real integral-domain step needed by root-count induction: a product can
be zero only when one factor is zero. Derived from MachLib's existing field
axioms (`mul_inv`, commutativity, associativity, and zero multiplication). -/
theorem mul_eq_zero_or_left_or_right
    {a b : Real} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    calc b
        = 1 * b := (one_mul_thm b).symm
      _ = (a * (1 / a)) * b := by rw [mul_inv a ha]
      _ = ((1 / a) * a) * b := by rw [mul_comm a (1 / a)]
      _ = (1 / a) * (a * b) := by rw [mul_assoc]
      _ = (1 / a) * 0 := by rw [h]
      _ = 0 := mul_zero (1 / a)

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

/-- Add a root to a list only if it is not already present. This is the
minimal duplicate-control primitive needed before product root lists can be
assembled from factor root lists. -/
noncomputable def insertUniqueRoot (x : Real) (roots : List Real) : List Real :=
  by
    classical
    exact if x ∈ roots then roots else x :: roots

/-- Union root lists while avoiding newly introduced duplicates. This is a
constructive list-level operation, not a finite-set library replacement. -/
noncomputable def unionUniqueRoots : List Real → List Real → List Real
  | [], ys => ys
  | x :: xs, ys => insertUniqueRoot x (unionUniqueRoots xs ys)

/-- Degree arithmetic target for coefficient-list products. The general
theorem is the next induction bridge; this definition names the exact shape. -/
def ProductDegreeBoundTarget : Prop :=
  ∀ p q : CoeffPoly, degreeBound (mulCoeff p q) ≤ degreeBound p + degreeBound q

/-- A product degree certificate for the current coefficient product. The
general constructor for this certificate is still future work. -/
def ProductDegreeBoundCert (product p q : CoeffPoly) : Prop :=
  degreeBound product ≤ degreeBound p + degreeBound q

/-- A product degree-growth certificate. Root-count induction needs this
direction: the product must have enough degree budget to cover the union of
factor roots. For nonzero normalized products this should eventually come
from exact degree arithmetic. -/
def ProductDegreeGrowthCert (product p q : CoeffPoly) : Prop :=
  degreeBound p + degreeBound q ≤ degreeBound product

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

/-- Pointwise coefficient-list addition evaluates to pointwise addition. -/
theorem eval_addCoeff (p q : CoeffPoly) (x : Real) :
    eval (addCoeff p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil =>
          unfold addCoeff eval
          rw [add_zero]
      | cons d ds =>
          unfold addCoeff eval
          rw [zero_add]
  | cons c cs ih =>
      cases q with
      | nil =>
          unfold addCoeff eval
          rw [add_zero]
      | cons d ds =>
          unfold addCoeff eval
          rw [ih ds]
          rw [mul_distrib]
          ac_rfl

/-- Scalar multiplication of coefficients evaluates to scalar multiplication
of the polynomial value. -/
theorem eval_scalarMulCoeff (a : Real) (p : CoeffPoly) (x : Real) :
    eval (scalarMulCoeff a p) x = a * eval p x := by
  induction p with
  | nil =>
      unfold scalarMulCoeff eval
      rw [mul_zero]
  | cons c cs ih =>
      unfold scalarMulCoeff eval
      rw [ih]
      have hswap : x * (a * eval cs x) = a * (x * eval cs x) := by
        calc x * (a * eval cs x)
            = (x * a) * eval cs x := (mul_assoc x a (eval cs x)).symm
          _ = (a * x) * eval cs x := by rw [mul_comm x a]
          _ = a * (x * eval cs x) := mul_assoc a x (eval cs x)
      rw [hswap]
      rw [mul_distrib]

/-- Shifting coefficients evaluates as multiplication by `x`. -/
theorem eval_shiftCoeff (p : CoeffPoly) (x : Real) :
    eval (shiftCoeff p) x = x * eval p x := by
  unfold shiftCoeff
  cases p with
  | nil =>
      unfold eval
      rw [eval_nil, mul_zero, add_zero]
  | cons c cs =>
      unfold eval
      rw [zero_add]
      change x * (c + x * eval cs x) = x * (c + x * eval cs x)
      rfl

/-- Coefficient-list convolution evaluates to the product of the operand
evaluations. This is the concrete product soundness bridge needed before
root-list induction can move beyond semantic product certificates. -/
theorem eval_mulCoeff (p q : CoeffPoly) (x : Real) :
    eval (mulCoeff p q) x = eval p x * eval q x := by
  induction p with
  | nil =>
      unfold mulCoeff eval
      rw [zero_mul]
  | cons c cs ih =>
      unfold mulCoeff
      change
        eval (addCoeff (scalarMulCoeff c q) (shiftCoeff (mulCoeff cs q))) x =
          (c + x * eval cs x) * eval q x
      rw [eval_addCoeff, eval_scalarMulCoeff, eval_shiftCoeff, ih]
      have htail : x * (eval cs x * eval q x) = eval q x * (x * eval cs x) := by
        calc x * (eval cs x * eval q x)
            = (x * eval cs x) * eval q x := (mul_assoc x (eval cs x) (eval q x)).symm
          _ = eval q x * (x * eval cs x) := by rw [mul_comm (x * eval cs x) (eval q x)]
      rw [htail]
      rw [mul_distrib_right]
      rw [mul_comm (eval q x) (x * eval cs x)]

/-- The recursive convolution product carries a semantic product certificate. -/
theorem mulCoeff_evalSound (p q : CoeffPoly) :
    MulEvalSound (mulCoeff p q) p q := by
  intro x
  exact eval_mulCoeff p q x

/-- A value already in a list remains present after unique insertion. -/
theorem mem_insertUniqueRoot_of_mem {x y : Real} {roots : List Real}
    (h : y ∈ roots) :
    y ∈ insertUniqueRoot x roots := by
  classical
  unfold insertUniqueRoot
  by_cases hx : x ∈ roots
  · simpa [hx] using h
  · simpa [hx] using List.mem_cons_of_mem x h

/-- The inserted value is present after unique insertion. -/
theorem mem_insertUniqueRoot_self (x : Real) (roots : List Real) :
    x ∈ insertUniqueRoot x roots := by
  classical
  unfold insertUniqueRoot
  by_cases hx : x ∈ roots
  · simp [hx]
  · simp [hx]

/-- Membership in the right root list is preserved by unique union. -/
theorem mem_unionUniqueRoots_right {x : Real} {left right : List Real}
    (h : x ∈ right) :
    x ∈ unionUniqueRoots left right := by
  induction left with
  | nil =>
      unfold unionUniqueRoots
      exact h
  | cons y ys ih =>
      unfold unionUniqueRoots
      exact mem_insertUniqueRoot_of_mem ih

/-- Membership in the left root list is preserved by unique union. -/
theorem mem_unionUniqueRoots_left {x : Real} {left right : List Real}
    (h : x ∈ left) :
    x ∈ unionUniqueRoots left right := by
  induction left with
  | nil =>
      cases h
  | cons y ys ih =>
      unfold unionUniqueRoots
      simp at h
      cases h with
      | inl hxy =>
          rw [hxy]
          exact mem_insertUniqueRoot_self y (unionUniqueRoots ys right)
      | inr htail =>
          exact mem_insertUniqueRoot_of_mem (ih htail)

/-- Unique insertion preserves duplicate-free root lists. -/
theorem RootListDistinct_insertUniqueRoot (x : Real) {roots : List Real}
    (hd : RootListDistinct roots) :
    RootListDistinct (insertUniqueRoot x roots) := by
  classical
  unfold insertUniqueRoot
  by_cases hx : x ∈ roots
  · simpa [hx] using hd
  · simp [hx, RootListDistinct, hd]

/-- Unique union preserves duplicate-free root lists. -/
theorem RootListDistinct_unionUniqueRoots
    {left right : List Real}
    (hleft : RootListDistinct left)
    (hright : RootListDistinct right) :
    RootListDistinct (unionUniqueRoots left right) := by
  induction left with
  | nil =>
      unfold unionUniqueRoots
      exact hright
  | cons x xs ih =>
      unfold unionUniqueRoots
      unfold RootListDistinct at hleft
      exact RootListDistinct_insertUniqueRoot x (ih hleft.right)

/-- Unique insertion increases length by at most one. -/
theorem length_insertUniqueRoot_le_succ (x : Real) (roots : List Real) :
    (insertUniqueRoot x roots).length ≤ roots.length + 1 := by
  classical
  unfold insertUniqueRoot
  by_cases hx : x ∈ roots
  · simp [hx]
  · simp [hx]

/-- Values already present do not change length under unique insertion. -/
theorem length_insertUniqueRoot_eq_of_mem {x : Real} {roots : List Real}
    (h : x ∈ roots) :
    (insertUniqueRoot x roots).length = roots.length := by
  classical
  unfold insertUniqueRoot
  simp [h]

/-- Unique union is bounded by the sum of source list lengths. -/
theorem length_unionUniqueRoots_le_add (left right : List Real) :
    (unionUniqueRoots left right).length ≤ left.length + right.length := by
  induction left with
  | nil =>
      unfold unionUniqueRoots
      simp
  | cons x xs ih =>
      unfold unionUniqueRoots
      change (insertUniqueRoot x (unionUniqueRoots xs right)).length ≤
        (xs.length + 1) + right.length
      have hinsert := length_insertUniqueRoot_le_succ x (unionUniqueRoots xs right)
      have htail := ih
      omega

/-- The product-degree arithmetic base case is checked. The general degree
arithmetic theorem still needs induction over normalized convolution output. -/
theorem productDegreeBound_nil_left (q : CoeffPoly) :
    degreeBound (mulCoeff [] q) ≤ degreeBound [] + degreeBound q := by
  unfold mulCoeff degreeBound
  simp

/-- Empty lists normalize to empty lists. -/
theorem normalizeCoeff_nil :
    normalizeCoeff [] = [] := rfl

/-- A nonzero singleton is already normalized. -/
theorem normalizeCoeff_singleton_nonzero {c : Real} (hc : c ≠ 0) :
    normalizeCoeff [c] = [c] := by
  unfold normalizeCoeff
  simp [normalizeCoeff_nil, hc]

/-- A zero singleton normalizes away. -/
theorem normalizeCoeff_singleton_zero :
    normalizeCoeff [0] = ([] : CoeffPoly) := by
  unfold normalizeCoeff
  simp [normalizeCoeff_nil]

/-- Already-normalized coefficient lists are unchanged by the tiny normalizer. -/
theorem normalizeCoeff_of_LastNonzero {p : CoeffPoly}
    (h : LastNonzero p) :
    normalizeCoeff p = p := by
  induction p with
  | nil =>
      cases h
  | cons c cs ih =>
      cases cs with
      | nil =>
          unfold LastNonzero at h
          exact normalizeCoeff_singleton_nonzero h
      | cons d ds =>
          unfold LastNonzero at h
          unfold normalizeCoeff
          have htail : normalizeCoeff (d :: ds) = d :: ds := ih h
          simp [htail]

/-- Normalization preserves degree bound for lists that are already normalized. -/
theorem degreeBound_normalizeCoeff_eq_of_LastNonzero {p : CoeffPoly}
    (h : LastNonzero p) :
    degreeBound (normalizeCoeff p) = degreeBound p := by
  rw [normalizeCoeff_of_LastNonzero h]

/-- Singleton coefficient lists have degree bound zero. -/
theorem degreeBound_singleton (c : Real) :
    degreeBound [c] = 0 := rfl

/-- A coefficient-list linear factor has degree bound one. -/
theorem degreeBound_linearCoeff (r : Real) :
    degreeBound (linearCoeff r) = 1 := rfl

/-- A monic quadratic example has degree bound two. -/
theorem degreeBound_monicQuadraticCoeff (a b : Real) :
    degreeBound (monicQuadraticCoeff a b) = 2 := rfl

/-- A coefficient-list linear factor is normalized because its last
coefficient is one. -/
theorem linearCoeff_lastNonzero (r : Real) :
    LastNonzero (linearCoeff r) := by
  unfold linearCoeff LastNonzero
  exact one_ne_zero

/-- Linear coefficient lists are unchanged by normalization. -/
theorem normalizeCoeff_linearCoeff (r : Real) :
    normalizeCoeff (linearCoeff r) = linearCoeff r :=
  normalizeCoeff_of_LastNonzero (linearCoeff_lastNonzero r)

/-- The coefficient-list linear factor evaluates to the same expression as
the AST linear factor. -/
theorem eval_linearCoeff_eq_linearFactor (r x : Real) :
    eval (linearCoeff r) x = Poly.eval (Poly.linearFactor r) x := by
  unfold linearCoeff eval Poly.linearFactor Poly.eval
  change -r + x * (1 + x * 0) = x - r
  rw [mul_zero, add_zero, mul_one_ax, sub_def, add_comm]

/-- Root equivalence between the normalized coefficient-list linear factor
and the existing AST linear-factor packet. -/
theorem linearCoeff_root_iff_linearFactor_root (r x : Real) :
    Root (linearCoeff r) x ↔
      PolynomialRootCount.Root (Poly.linearFactor r) x := by
  unfold Root PolynomialRootCount.Root
  rw [eval_linearCoeff_eq_linearFactor]

/-- The singleton root list is sound for a coefficient-list linear factor. -/
theorem linearCoeff_rootListSound (r : Real) :
    RootListSound (linearCoeff r) [r] := by
  intro x hx
  have hast : PolynomialRootCount.Root (Poly.linearFactor r) x :=
    (linearCoeff_root_iff_linearFactor_root r x).mp hx
  have hx_eq : x = r := PolynomialRootCount.linearFactor_root_unique r x hast
  rw [hx_eq]
  simp

/-- Singleton root lists are distinct in the coefficient-list layer. -/
theorem singletonCoeffRootListDistinct (r : Real) :
    RootListDistinct [r] := by
  simp [RootListDistinct]

/-- The singleton root list for a coefficient-list linear factor is degree-bounded. -/
theorem linearCoeff_rootListDegreeBound (r : Real) :
    RootListDegreeBound (linearCoeff r) [r] := by
  simp [RootListDegreeBound, degreeBound_linearCoeff]

/-- The explicit constant-scaled linear product evaluates as a product. -/
theorem scaledLinearCoeff_evalSound (a r : Real) :
    MulEvalSound (scaledLinearCoeff a r) [a] (linearCoeff r) := by
  intro x
  unfold scaledLinearCoeff linearCoeff eval
  change a * -r + x * (a + x * 0) = (a + x * 0) * (-r + x * (1 + x * 0))
  mach_ring

/-- The explicit product of two linear factors evaluates as a product. -/
theorem linearLinearCoeff_evalSound (r s : Real) :
    MulEvalSound (linearLinearCoeff r s) (linearCoeff r) (linearCoeff s) := by
  intro x
  unfold linearLinearCoeff linearCoeff eval
  change
    (-r) * (-s) + x * (((-r) * 1 + 1 * (-s)) + x * (1 + x * 0)) =
      (-r + x * (1 + x * 0)) * (-s + x * (1 + x * 0))
  mach_ring
  ac_rfl

/-- The explicit linear times monic-quadratic product evaluates as a product. -/
theorem linearQuadraticCoeff_evalSound (r a b : Real) :
    MulEvalSound
      (linearQuadraticCoeff r a b) (linearCoeff r) (monicQuadraticCoeff a b) := by
  intro x
  unfold linearQuadraticCoeff linearCoeff monicQuadraticCoeff eval
  change
    (-r) * a + x * (((-r) * b + 1 * a) + x * (((-r) * 1 + 1 * b) + x * (1 + x * 0))) =
      (-r + x * (1 + x * 0)) * (a + x * (b + x * (1 + x * 0)))
  mach_ring
  ac_rfl

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

/-- A root of a semantically certified product must be a root of one factor.
This is the first product-root bridge needed for a root-count induction. -/
theorem productRoot_split
    {product p q : CoeffPoly} (hmul : MulEvalSound product p q)
    {x : Real} (hroot : Root product x) :
    Root p x ∨ Root q x := by
  unfold Root at hroot
  rw [hmul x] at hroot
  exact mul_eq_zero_or_left_or_right hroot

/-- If the left factor is known not to vanish at a point, a product root must
come from the right factor. -/
theorem productRoot_right_of_left_nonroot
    {product p q : CoeffPoly} (hmul : MulEvalSound product p q)
    {x : Real} (hleft : eval p x ≠ 0) (hroot : Root product x) :
    Root q x := by
  have split := productRoot_split (product := product) (p := p) (q := q) hmul hroot
  cases split with
  | inl hp =>
      unfold Root at hp
      exact False.elim (hleft hp)
  | inr hq => exact hq

/-- If the right factor is known not to vanish at a point, a product root must
come from the left factor. -/
theorem productRoot_left_of_right_nonroot
    {product p q : CoeffPoly} (hmul : MulEvalSound product p q)
    {x : Real} (hright : eval q x ≠ 0) (hroot : Root product x) :
    Root p x := by
  have split := productRoot_split (product := product) (p := p) (q := q) hmul hroot
  cases split with
  | inl hp => exact hp
  | inr hq =>
      unfold Root at hq
      exact False.elim (hright hq)

/-- Product root-list soundness: if each factor has a sound finite root list,
then a semantically certified product has roots in the unique union of those
factor lists. -/
theorem productRootListSound_union
    {product p q : CoeffPoly}
    {rootsP rootsQ : List Real}
    (hmul : MulEvalSound product p q)
    (hp : RootListSound p rootsP)
    (hq : RootListSound q rootsQ) :
    RootListSound product (unionUniqueRoots rootsP rootsQ) := by
  intro x hroot
  have split := productRoot_split (product := product) (p := p) (q := q) hmul hroot
  cases split with
  | inl hpRoot =>
      exact mem_unionUniqueRoots_left (hp x hpRoot)
  | inr hqRoot =>
      exact mem_unionUniqueRoots_right (hq x hqRoot)

/-- Convolution-specific product root-list soundness. -/
theorem mulCoeffRootListSound_union
    {p q : CoeffPoly}
    {rootsP rootsQ : List Real}
    (hp : RootListSound p rootsP)
    (hq : RootListSound q rootsQ) :
    RootListSound (mulCoeff p q) (unionUniqueRoots rootsP rootsQ) :=
  productRootListSound_union (hmul := mulCoeff_evalSound p q) hp hq

/-- Product root-list distinctness follows from duplicate-free factor lists
because `unionUniqueRoots` inserts only missing roots. -/
theorem productRootListDistinct_union
    {rootsP rootsQ : List Real}
    (hp : RootListDistinct rootsP)
    (hq : RootListDistinct rootsQ) :
    RootListDistinct (unionUniqueRoots rootsP rootsQ) :=
  RootListDistinct_unionUniqueRoots hp hq

/-- Product root-list cardinality is bounded by the sum of factor root-list
cardinalities. -/
theorem productRootListLength_union_le_add
    (rootsP rootsQ : List Real) :
    (unionUniqueRoots rootsP rootsQ).length ≤ rootsP.length + rootsQ.length :=
  length_unionUniqueRoots_le_add rootsP rootsQ

/-- If a product has a degree certificate, then bounded factor root lists
produce a bounded product root list. This is the honest bridge between checked
root-list union arithmetic and the still-separate product-degree arithmetic. -/
theorem productRootListDegreeBound_union_of_cert
    {product p q : CoeffPoly}
    {rootsP rootsQ : List Real}
    (hcert : ProductDegreeGrowthCert product p q)
    (hp : RootListDegreeBound p rootsP)
    (hq : RootListDegreeBound q rootsQ) :
    RootListDegreeBound product (unionUniqueRoots rootsP rootsQ) := by
  unfold RootListDegreeBound ProductDegreeGrowthCert at *
  have hlen := length_unionUniqueRoots_le_add rootsP rootsQ
  omega

/-! ## Checked concrete examples

These examples exercise the bridge on small normalized products. They are
evidence examples, not the general root-count induction theorem.
-/

/-- Example 1: constant times constant has exact structural degree growth. -/
theorem example_growth_const_const (a b : Real) :
    ProductDegreeGrowthCert [a * b] [a] [b] := by
  unfold ProductDegreeGrowthCert degreeBound
  change 0 ≤ 0
  omega

/-- Example 2: constant times linear has exact structural degree growth. -/
theorem example_growth_const_linear (a r : Real) :
    ProductDegreeGrowthCert [a * (-r), a] [a] (linearCoeff r) := by
  unfold ProductDegreeGrowthCert linearCoeff degreeBound
  change 1 ≤ 1
  omega

/-- Example 3: linear times constant has exact structural degree growth. -/
theorem example_growth_linear_const (r a : Real) :
    ProductDegreeGrowthCert [(-r) * a, a] (linearCoeff r) [a] := by
  unfold ProductDegreeGrowthCert linearCoeff degreeBound
  change 1 ≤ 1
  omega

/-- Example 4: linear times linear has exact structural degree growth. -/
theorem example_growth_linear_linear (r s : Real) :
    ProductDegreeGrowthCert
      [(-r) * (-s), (-r) * 1 + 1 * (-s), 1]
      (linearCoeff r) (linearCoeff s) := by
  unfold ProductDegreeGrowthCert linearCoeff degreeBound
  change 2 ≤ 2
  omega

/-- Example 5: linear times monic quadratic has exact structural degree growth. -/
theorem example_growth_linear_quadratic (r a b : Real) :
    ProductDegreeGrowthCert
      [(-r) * a, (-r) * b + 1 * a, (-r) * 1 + 1 * b, 1]
      (linearCoeff r) (monicQuadraticCoeff a b) := by
  unfold ProductDegreeGrowthCert linearCoeff monicQuadraticCoeff degreeBound
  change 3 ≤ 3
  omega

/-- Example 1: product root packet bridge for two linear factors. -/
theorem example_product_linear_linear_degreeBound (r s : Real) :
    RootListDegreeBound
      [(-r) * (-s), (-r) * 1 + 1 * (-s), 1]
      (unionUniqueRoots [r] [s]) :=
  productRootListDegreeBound_union_of_cert
    (hcert := example_growth_linear_linear r s)
    (hp := linearCoeff_rootListDegreeBound r)
    (hq := linearCoeff_rootListDegreeBound s)

/-- Example 2: duplicate linear roots deduplicate and remain degree-bounded. -/
theorem example_product_repeated_linear_degreeBound (r : Real) :
    RootListDegreeBound
      [(-r) * (-r), (-r) * 1 + 1 * (-r), 1]
      (unionUniqueRoots [r] [r]) :=
  productRootListDegreeBound_union_of_cert
    (hcert := example_growth_linear_linear r r)
    (hp := linearCoeff_rootListDegreeBound r)
    (hq := linearCoeff_rootListDegreeBound r)

/-- Example 3: two singleton lists union distinctly after insertion. -/
theorem example_union_two_singletons_distinct (r s : Real) :
    RootListDistinct (unionUniqueRoots [r] [s]) :=
  productRootListDistinct_union
    (singletonCoeffRootListDistinct r)
    (singletonCoeffRootListDistinct s)

/-- Example 4: repeated singleton union stays cardinality-bounded. -/
theorem example_union_repeated_singleton_length (r : Real) :
    (unionUniqueRoots [r] [r]).length ≤ [r].length + [r].length :=
  productRootListLength_union_le_add [r] [r]

/-- Example 5: three singleton insertions stay cardinality-bounded. -/
theorem example_union_three_singletons_length (r s t : Real) :
    (unionUniqueRoots [r, s] [t]).length ≤ [r, s].length + [t].length :=
  productRootListLength_union_le_add [r, s] [t]

/-! ## Exact product-degree normalizer v8 examples

The following examples keep the product-degree frontier honest: they check
structural degree bounds for normalized product outputs, while the general
arbitrary convolution degree-growth theorem remains a target.
-/

/-- v8 quadratic times linear example 1. -/
theorem example_v8_quadratic_linear_1 (a b r : Real) :
    ProductDegreeGrowthCert
      [a * (-r), a * 1 + b * (-r), b * 1 + 1 * (-r), 1]
      (monicQuadraticCoeff a b) (linearCoeff r) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 quadratic times linear example 2, with the linear factor first. -/
theorem example_v8_quadratic_linear_2 (r a b : Real) :
    ProductDegreeGrowthCert
      (linearQuadraticCoeff r a b)
      (linearCoeff r) (monicQuadraticCoeff a b) := by
  unfold ProductDegreeGrowthCert linearQuadraticCoeff linearCoeff monicQuadraticCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 quadratic times linear example 3, specializing to a zero constant term. -/
theorem example_v8_quadratic_linear_3 (b r : Real) :
    ProductDegreeGrowthCert
      [0 * (-r), 0 * 1 + b * (-r), b * 1 + 1 * (-r), 1]
      (monicQuadraticCoeff 0 b) (linearCoeff r) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 quadratic times linear example 4, specializing to a zero linear term. -/
theorem example_v8_quadratic_linear_4 (a r : Real) :
    ProductDegreeGrowthCert
      [a * (-r), a * 1 + 0 * (-r), 0 * 1 + 1 * (-r), 1]
      (monicQuadraticCoeff a 0) (linearCoeff r) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 quadratic times linear example 5, repeated linear attachment. -/
theorem example_v8_quadratic_linear_5 (r : Real) :
    ProductDegreeGrowthCert
      (linearQuadraticCoeff r ((-r) * (-r)) ((-r) * 1 + 1 * (-r)))
      (linearCoeff r)
      [(-r) * (-r), (-r) * 1 + 1 * (-r), 1] := by
  unfold ProductDegreeGrowthCert linearQuadraticCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 quadratic times quadratic example 1. -/
theorem example_v8_quadratic_quadratic_1 (a b c d : Real) :
    ProductDegreeGrowthCert
      [a * c, a * d + b * c, a * 1 + b * d + 1 * c, b * 1 + 1 * d, 1]
      (monicQuadraticCoeff a b) (monicQuadraticCoeff c d) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 4 ≤ 4
  omega

/-- v8 quadratic times quadratic example 2, repeated quadratic. -/
theorem example_v8_quadratic_quadratic_2 (a b : Real) :
    ProductDegreeGrowthCert
      [a * a, a * b + b * a, a * 1 + b * b + 1 * a, b * 1 + 1 * b, 1]
      (monicQuadraticCoeff a b) (monicQuadraticCoeff a b) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 4 ≤ 4
  omega

/-- v8 quadratic times quadratic example 3, zero constant on the left. -/
theorem example_v8_quadratic_quadratic_3 (b c d : Real) :
    ProductDegreeGrowthCert
      [0 * c, 0 * d + b * c, 0 * 1 + b * d + 1 * c, b * 1 + 1 * d, 1]
      (monicQuadraticCoeff 0 b) (monicQuadraticCoeff c d) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 4 ≤ 4
  omega

/-- v8 quadratic times quadratic example 4, zero linear on the right. -/
theorem example_v8_quadratic_quadratic_4 (a b c : Real) :
    ProductDegreeGrowthCert
      [a * c, a * 0 + b * c, a * 1 + b * 0 + 1 * c, b * 1 + 1 * 0, 1]
      (monicQuadraticCoeff a b) (monicQuadraticCoeff c 0) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 4 ≤ 4
  omega

/-- v8 quadratic times quadratic example 5, both sparse. -/
theorem example_v8_quadratic_quadratic_5 (a c : Real) :
    ProductDegreeGrowthCert
      [a * c, a * 0 + 0 * c, a * 1 + 0 * 0 + 1 * c, 0 * 1 + 1 * 0, 1]
      (monicQuadraticCoeff a 0) (monicQuadraticCoeff c 0) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 4 ≤ 4
  omega

/-- v8 repeated-root example 1: `(x-r)^2`. -/
theorem example_v8_repeated_root_1 (r : Real) :
    ProductDegreeGrowthCert (linearLinearCoeff r r) (linearCoeff r) (linearCoeff r) := by
  unfold ProductDegreeGrowthCert linearLinearCoeff linearCoeff degreeBound
  change 2 ≤ 2
  omega

/-- v8 repeated-root example 2: staged `(x-r)^3`. -/
theorem example_v8_repeated_root_2 (r : Real) :
    ProductDegreeGrowthCert
      (stagedTripleLinearCoeff r r r)
      (linearLinearCoeff r r) (linearCoeff r) := by
  unfold ProductDegreeGrowthCert stagedTripleLinearCoeff linearLinearCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 repeated-root example 3: `(x-r)^2(x-s)`. -/
theorem example_v8_repeated_root_3 (r s : Real) :
    ProductDegreeGrowthCert
      (stagedTripleLinearCoeff r r s)
      (linearLinearCoeff r r) (linearCoeff s) := by
  unfold ProductDegreeGrowthCert stagedTripleLinearCoeff linearLinearCoeff linearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 repeated-root example 4: `(x-r)(x-s)^2`. -/
theorem example_v8_repeated_root_4 (r s : Real) :
    ProductDegreeGrowthCert
      (stagedTripleLinearCoeff r s s)
      (linearLinearCoeff r s) (linearCoeff s) := by
  unfold ProductDegreeGrowthCert stagedTripleLinearCoeff linearLinearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 repeated-root example 5: `(x-r)^3` viewed as linear times quadratic. -/
theorem example_v8_repeated_root_5 (r : Real) :
    ProductDegreeGrowthCert
      (linearQuadraticCoeff r ((-r) * (-r)) ((-r) * 1 + 1 * (-r)))
      (linearCoeff r) (linearLinearCoeff r r) := by
  unfold ProductDegreeGrowthCert linearQuadraticCoeff linearCoeff linearLinearCoeff degreeBound
  change 3 ≤ 3
  omega

/-- v8 scaled product example 1: nonzero constant times linear shape. -/
theorem example_v8_scaled_product_1 (a r : Real) :
    ProductDegreeGrowthCert (scaledLinearCoeff a r) [a] (linearCoeff r) := by
  unfold ProductDegreeGrowthCert scaledLinearCoeff linearCoeff degreeBound
  change 1 ≤ 1
  omega

/-- v8 scaled product example 2: linear times constant shape. -/
theorem example_v8_scaled_product_2 (r a : Real) :
    ProductDegreeGrowthCert [(-r) * a, 1 * a] (linearCoeff r) [a] := by
  unfold ProductDegreeGrowthCert linearCoeff degreeBound
  change 1 ≤ 1
  omega

/-- v8 scaled product example 3: constant times monic quadratic shape. -/
theorem example_v8_scaled_product_3 (a b c : Real) :
    ProductDegreeGrowthCert [a * b, a * c, a] [a] (monicQuadraticCoeff b c) := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 2 ≤ 2
  omega

/-- v8 scaled product example 4: monic quadratic times constant shape. -/
theorem example_v8_scaled_product_4 (a b c : Real) :
    ProductDegreeGrowthCert [b * a, c * a, 1 * a] (monicQuadraticCoeff b c) [a] := by
  unfold ProductDegreeGrowthCert monicQuadraticCoeff degreeBound
  change 2 ≤ 2
  omega

/-- v8 scaled product example 5: constant times repeated-root quadratic. -/
theorem example_v8_scaled_product_5 (a r : Real) :
    ProductDegreeGrowthCert
      [a * ((-r) * (-r)), a * ((-r) * 1 + 1 * (-r)), a]
      [a] (linearLinearCoeff r r) := by
  unfold ProductDegreeGrowthCert linearLinearCoeff degreeBound
  change 2 ≤ 2
  omega

/-- v8 cleanup example 1: empty list normalizes to empty. -/
theorem example_v8_cleanup_1 :
    normalizeCoeff ([] : CoeffPoly) = [] :=
  normalizeCoeff_nil

/-- v8 cleanup example 2: singleton zero normalizes away. -/
theorem example_v8_cleanup_2 :
    normalizeCoeff [0] = ([] : CoeffPoly) :=
  normalizeCoeff_singleton_zero

/-- v8 cleanup example 3: nonzero singleton is already normalized. -/
theorem example_v8_cleanup_3 {c : Real} (hc : c ≠ 0) :
    normalizeCoeff [c] = [c] :=
  normalizeCoeff_singleton_nonzero hc

/-- v8 cleanup example 4: linear coefficient lists are already normalized. -/
theorem example_v8_cleanup_4 (r : Real) :
    normalizeCoeff (linearCoeff r) = linearCoeff r :=
  normalizeCoeff_linearCoeff r

/-- v8 cleanup example 5: LastNonzero inputs preserve degree under normalization. -/
theorem example_v8_cleanup_5 {p : CoeffPoly} (h : LastNonzero p) :
    degreeBound (normalizeCoeff p) = degreeBound p :=
  degreeBound_normalizeCoeff_eq_of_LastNonzero h

/-- v8 root-packet example 1: `(x-r)(x-s)` gets the union of singleton roots. -/
theorem example_v8_root_packet_linear_linear (r s : Real) :
    RootListDegreeBound (linearLinearCoeff r s) (unionUniqueRoots [r] [s]) :=
  productRootListDegreeBound_union_of_cert
    (hcert := by
      unfold ProductDegreeGrowthCert linearLinearCoeff linearCoeff degreeBound
      change 2 ≤ 2
      omega)
    (hp := linearCoeff_rootListDegreeBound r)
    (hq := linearCoeff_rootListDegreeBound s)

/-- v8 root-packet example 2: `(x-r)^2` deduplicates repeated singleton roots. -/
theorem example_v8_root_packet_repeated_linear (r : Real) :
    RootListDegreeBound (linearLinearCoeff r r) (unionUniqueRoots [r] [r]) :=
  example_v8_root_packet_linear_linear r r

/-- v8 root-packet example 3: `(x-r)(x-s)(x-t)` as a staged product packet. -/
theorem example_v8_root_packet_staged_triple (r s t : Real) :
    RootListDegreeBound
      (stagedTripleLinearCoeff r s t)
      (unionUniqueRoots (unionUniqueRoots [r] [s]) [t]) :=
  productRootListDegreeBound_union_of_cert
    (hcert := by
      unfold ProductDegreeGrowthCert stagedTripleLinearCoeff linearLinearCoeff linearCoeff degreeBound
      change 3 ≤ 3
      omega)
    (hp := example_v8_root_packet_linear_linear r s)
    (hq := linearCoeff_rootListDegreeBound t)

/-- v8 root-packet example 4: constant-scale times linear, degree-bound layer. -/
theorem example_v8_root_packet_scaled_linear (a r : Real) :
    RootListDegreeBound (scaledLinearCoeff a r) (unionUniqueRoots [] [r]) :=
  productRootListDegreeBound_union_of_cert
    (hcert := example_v8_scaled_product_1 a r)
    (hp := by
      unfold RootListDegreeBound degreeBound
      change 0 ≤ 0
      omega)
    (hq := linearCoeff_rootListDegreeBound r)

/-- v8 root-packet example 5: linear times quadratic with a provided
quadratic root-degree certificate. -/
theorem example_v8_root_packet_linear_quadratic_with_certificate
    (r a b : Real) {rootsQ : List Real}
    (hq : RootListDegreeBound (monicQuadraticCoeff a b) rootsQ) :
    RootListDegreeBound
      (linearQuadraticCoeff r a b)
      (unionUniqueRoots [r] rootsQ) :=
  productRootListDegreeBound_union_of_cert
    (hcert := example_v8_quadratic_linear_2 r a b)
    (hp := linearCoeff_rootListDegreeBound r)
    (hq := hq)

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
