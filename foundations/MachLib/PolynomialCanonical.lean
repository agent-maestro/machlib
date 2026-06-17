import MachLib.PolynomialEvidence
import MachLib.Ring

/-!
# MachLib.PolynomialCanonical — coefficient-list canonical form for `Poly`

The `Poly` AST in `PolynomialEvidence.lean` is a free term algebra: two
syntactically distinct ASTs can represent the same polynomial (e.g.
`add p (const 0)` vs `p`, or `sub (add p q) q` vs `p`).
`PolynomialRootCount.polySimplify` folds zero/one constants but does not
perform ring cancellation — making it inadequate for the strict-descent
proofs in path-c (`KhovanskiiReduction.singleExp_reduceStep`'s
`h_bridge`).

This module ships the **coefficient-list canonical form**: an
order-preserving list `[c_0, c_1, …, c_n]` representing
`c_0 + c_1·x + … + c_n·x^n`. Two ring-equivalent ASTs collapse to the
same canonical coefficient list automatically because the recursion is
itself the polynomial-ring operation.

## Roadmap

- **Phase A (this commit):** definitions of `listAddR`, `listSubR`,
  `listScaleR`, `listMulR`, `polyCoeffs`; structural sanity lemmas.
- **Phase B:** eval preservation — `evalCoeffs (polyCoeffs p) x = Poly.eval p x`.
- **Phase C:** `polyCanonDegree` (true degree via stripped coefficient list).
- **Phase D:** ring laws for the zip-arithmetic helpers (the cancellation
  theorems needed by `h_bridge`).
- **Phase E:** the strict-descent lemma plus `h_bridge` closure.

Zero Mathlib dependency. -/

namespace MachLib
namespace PolynomialCanonical

open MachLib.Real
open MachLib.PolynomialEvidence

/-! ## List arithmetic over `Real`

Pointwise addition/subtraction extending the shorter list with zeros;
scalar multiplication; convolution for multiplication. These are the
ring operations on the abstract polynomial ring `Real[x]`. -/

/-- Pointwise addition of two coefficient lists. The shorter list is
implicitly extended with zeros. -/
noncomputable def listAddR : List Real → List Real → List Real
  | [],       qs       => qs
  | ps,       []       => ps
  | p :: ps,  q :: qs  => (p + q) :: listAddR ps qs

theorem listAddR_nil_left (qs : List Real) :
    listAddR [] qs = qs := by
  cases qs <;> rfl

theorem listAddR_nil_right (ps : List Real) :
    listAddR ps [] = ps := by
  cases ps <;> rfl

theorem listAddR_cons_cons (p q : Real) (ps qs : List Real) :
    listAddR (p :: ps) (q :: qs) = (p + q) :: listAddR ps qs := rfl

/-- Pointwise subtraction. The shorter list is implicitly extended with
zeros (negated on the right). -/
noncomputable def listSubR : List Real → List Real → List Real
  | [],       []       => []
  | [],       q :: qs  => (0 - q) :: listSubR [] qs
  | p :: ps,  []       => p :: ps
  | p :: ps,  q :: qs  => (p - q) :: listSubR ps qs

theorem listSubR_nil_nil :
    listSubR [] [] = [] := rfl

theorem listSubR_nil_cons (q : Real) (qs : List Real) :
    listSubR [] (q :: qs) = (0 - q) :: listSubR [] qs := rfl

theorem listSubR_cons_nil (p : Real) (ps : List Real) :
    listSubR (p :: ps) [] = p :: ps := rfl

theorem listSubR_cons_cons (p q : Real) (ps qs : List Real) :
    listSubR (p :: ps) (q :: qs) = (p - q) :: listSubR ps qs := rfl

/-- Scalar multiplication of a coefficient list. -/
noncomputable def listScaleR (r : Real) : List Real → List Real
  | []       => []
  | q :: qs  => (r * q) :: listScaleR r qs

theorem listScaleR_nil (r : Real) :
    listScaleR r [] = [] := rfl

theorem listScaleR_cons (r q : Real) (qs : List Real) :
    listScaleR r (q :: qs) = (r * q) :: listScaleR r qs := rfl

/-- Convolution of two coefficient lists (polynomial multiplication).
For `[p_0, …, p_m] * [q_0, …, q_n]`, the result at position `k` is
`Σ_{i+j=k} p_i * q_j`. -/
noncomputable def listMulR : List Real → List Real → List Real
  | [],       _   => []
  | p :: ps,  qs  => listAddR (listScaleR p qs) (0 :: listMulR ps qs)

theorem listMulR_nil (qs : List Real) :
    listMulR [] qs = [] := rfl

theorem listMulR_cons (p : Real) (ps qs : List Real) :
    listMulR (p :: ps) qs =
    listAddR (listScaleR p qs) (0 :: listMulR ps qs) := rfl

/-! ## The canonical coefficient list

`polyCoeffs p` is the `Real`-coefficient list representing `p` in
increasing-power order. The recursion is identical to the polynomial
ring's operations on coefficient lists, so ring-equivalent ASTs produce
equal lists by construction. -/

/-- Coefficient list of a `Poly`. -/
noncomputable def polyCoeffs : Poly → List Real
  | Poly.const c   => [c]
  | Poly.var       => [0, 1]
  | Poly.add p q   => listAddR (polyCoeffs p) (polyCoeffs q)
  | Poly.sub p q   => listSubR (polyCoeffs p) (polyCoeffs q)
  | Poly.mul p q   => listMulR (polyCoeffs p) (polyCoeffs q)

theorem polyCoeffs_const (c : Real) :
    polyCoeffs (Poly.const c) = [c] := rfl

theorem polyCoeffs_var :
    polyCoeffs Poly.var = [0, 1] := rfl

theorem polyCoeffs_add (p q : Poly) :
    polyCoeffs (Poly.add p q) = listAddR (polyCoeffs p) (polyCoeffs q) := rfl

theorem polyCoeffs_sub (p q : Poly) :
    polyCoeffs (Poly.sub p q) = listSubR (polyCoeffs p) (polyCoeffs q) := rfl

theorem polyCoeffs_mul (p q : Poly) :
    polyCoeffs (Poly.mul p q) = listMulR (polyCoeffs p) (polyCoeffs q) := rfl

/-! ## Non-emptiness

`polyCoeffs` always produces a non-empty list. The base cases give
length-1 or length-2; the recursive cases preserve non-emptiness through
the list arithmetic. -/

theorem listAddR_nonempty {ps qs : List Real}
    (h : ps ≠ [] ∨ qs ≠ []) : listAddR ps qs ≠ [] := by
  cases ps with
  | nil =>
    rcases h with h | h
    · exact (h rfl).elim
    · rw [listAddR_nil_left]; exact h
  | cons p ps' =>
    cases qs with
    | nil => rw [listAddR_nil_right]; intro hc; cases hc
    | cons q qs' => rw [listAddR_cons_cons]; intro hc; cases hc

theorem listSubR_nonempty {ps qs : List Real}
    (h : ps ≠ [] ∨ qs ≠ []) : listSubR ps qs ≠ [] := by
  cases ps with
  | nil =>
    rcases h with h | h
    · exact (h rfl).elim
    · cases qs with
      | nil => exact (h rfl).elim
      | cons q qs' => rw [listSubR_nil_cons]; intro hc; cases hc
  | cons p ps' =>
    cases qs with
    | nil => rw [listSubR_cons_nil]; intro hc; cases hc
    | cons q qs' => rw [listSubR_cons_cons]; intro hc; cases hc

theorem listMulR_nonempty {ps qs : List Real}
    (hp : ps ≠ []) (_hq : qs ≠ []) : listMulR ps qs ≠ [] := by
  cases ps with
  | nil => exact (hp rfl).elim
  | cons p ps' =>
    rw [listMulR_cons]
    apply listAddR_nonempty
    right
    intro hc; cases hc

theorem polyCoeffs_nonempty (p : Poly) : polyCoeffs p ≠ [] := by
  induction p with
  | const c => rw [polyCoeffs_const]; intro hc; cases hc
  | var => rw [polyCoeffs_var]; intro hc; cases hc
  | add p q ihp _ihq =>
    rw [polyCoeffs_add]
    exact listAddR_nonempty (Or.inl ihp)
  | sub p q ihp _ihq =>
    rw [polyCoeffs_sub]
    exact listSubR_nonempty (Or.inl ihp)
  | mul p q ihp ihq =>
    rw [polyCoeffs_mul]
    exact listMulR_nonempty ihp ihq

end PolynomialCanonical
end MachLib
