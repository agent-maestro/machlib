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
