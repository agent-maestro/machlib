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

/-! ## Phase B — eval preservation

`evalCoeffs L x` interprets `L = [c_0, c_1, …, c_n]` as the polynomial
`c_0 + c_1·x + c_2·x² + … + c_n·xⁿ`, evaluated at `x`. We use
Horner form for the recursion. The headline theorem `polyCoeffs_eval`
shows the canonical form is semantically faithful:
`evalCoeffs (polyCoeffs p) x = Poly.eval p x`. -/

/-- Horner-form evaluation of a coefficient list at a point. -/
noncomputable def evalCoeffs : List Real → Real → Real
  | [],       _ => 0
  | c :: cs,  x => c + x * evalCoeffs cs x

theorem evalCoeffs_nil (x : Real) : evalCoeffs [] x = 0 := rfl

theorem evalCoeffs_cons (c : Real) (cs : List Real) (x : Real) :
    evalCoeffs (c :: cs) x = c + x * evalCoeffs cs x := rfl

/-! ### Ring identities used in distributivity proofs

The `Real` ring law shapes that arise from expanding the Horner form
through pointwise list arithmetic. Each helper takes abstract `Real`
arguments so `mach_ring` can close it by pure ring arithmetic — and
then the parametric instances close the per-call rewrite without
re-running the AC search at every call site. -/

theorem add_interchange_helper (a b c d : Real) :
    (a + b) + (c + d) = (a + c) + (b + d) := by mach_ring

theorem sub_interchange_helper (a b c d : Real) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  rw [sub_def, sub_def, sub_def, neg_add]
  show (a + -b) + (c + -d) = (a + c) + (-b + -d)
  rw [add_assoc a (-b) (c + -d), ← add_assoc (-b) c (-d),
      add_comm (-b) c, add_assoc c (-b) (-d), ← add_assoc a c (-b + -d)]

theorem sub_zero_pair_helper (a b : Real) :
    (0 - a) + (0 - b) = 0 - (a + b) := by mach_ring

theorem mul_outer_distrib_helper (r a b : Real) :
    r * (a + b) = r * a + r * b := mul_distrib r a b

theorem scale_horner_helper (r q x t : Real) :
    (r * q) + x * (r * t) = r * (q + x * t) := by
  rw [mul_outer_distrib_helper]
  show (r * q) + x * (r * t) = r * q + r * (x * t)
  have : x * (r * t) = r * (x * t) := by
    rw [← mul_assoc, ← mul_assoc, mul_comm x r]
  rw [this]

theorem mul_horner_helper (p qval pval' x : Real) :
    p * qval + (0 + x * (pval' * qval)) = (p + x * pval') * qval := by
  rw [zero_add, mul_comm (p + x * pval') qval, mul_distrib]
  show p * qval + x * (pval' * qval) =
       qval * p + qval * (x * pval')
  have h1 : p * qval = qval * p := mul_comm _ _
  have h2 : x * (pval' * qval) = qval * (x * pval') := by
    rw [mul_comm pval' qval, ← mul_assoc, ← mul_assoc, mul_comm x qval]
  rw [h1, h2]

/-! ### Distributivity of `evalCoeffs` over the list arithmetic -/

theorem evalCoeffs_listAddR (ps qs : List Real) (x : Real) :
    evalCoeffs (listAddR ps qs) x = evalCoeffs ps x + evalCoeffs qs x := by
  induction ps generalizing qs with
  | nil =>
    rw [listAddR_nil_left, evalCoeffs_nil]
    show evalCoeffs qs x = 0 + evalCoeffs qs x
    rw [zero_add]
  | cons p ps' ih =>
    cases qs with
    | nil =>
      rw [listAddR_nil_right, evalCoeffs_nil]
      show evalCoeffs (p :: ps') x = evalCoeffs (p :: ps') x + 0
      rw [add_zero]
    | cons q qs' =>
      rw [listAddR_cons_cons, evalCoeffs_cons, evalCoeffs_cons, evalCoeffs_cons]
      rw [ih qs']
      show (p + q) + x * (evalCoeffs ps' x + evalCoeffs qs' x) =
           (p + x * evalCoeffs ps' x) + (q + x * evalCoeffs qs' x)
      rw [mul_distrib]
      exact add_interchange_helper p q _ _

/-- Multiplication distributes over subtraction (right). -/
theorem mul_sub_distrib_helper (x a b : Real) :
    x * (a - b) = x * a - x * b := by
  rw [sub_def, sub_def, mul_distrib, mul_neg]

/-- Helper used by `evalCoeffs_listSubR`: `listSubR []` is the
pointwise negation. -/
theorem evalCoeffs_listSubR_nil_left (qs : List Real) (x : Real) :
    evalCoeffs (listSubR [] qs) x = 0 - evalCoeffs qs x := by
  induction qs with
  | nil =>
    rw [listSubR_nil_nil]
    show (0 : Real) = 0 - 0
    rw [sub_self]
  | cons q qs' ih =>
    rw [listSubR_nil_cons, evalCoeffs_cons, ih, evalCoeffs_cons]
    show (0 - q) + x * (0 - evalCoeffs qs' x) =
         0 - (q + x * evalCoeffs qs' x)
    rw [mul_sub_distrib_helper, mul_zero]
    exact sub_zero_pair_helper q _

theorem evalCoeffs_listSubR (ps qs : List Real) (x : Real) :
    evalCoeffs (listSubR ps qs) x = evalCoeffs ps x - evalCoeffs qs x := by
  induction ps generalizing qs with
  | nil =>
    rw [evalCoeffs_nil]
    exact evalCoeffs_listSubR_nil_left qs x
  | cons p ps' ih =>
    cases qs with
    | nil =>
      rw [listSubR_cons_nil, evalCoeffs_nil]
      show evalCoeffs (p :: ps') x = evalCoeffs (p :: ps') x - 0
      rw [sub_def, neg_zero, add_zero]
    | cons q qs' =>
      rw [listSubR_cons_cons, evalCoeffs_cons, evalCoeffs_cons, evalCoeffs_cons]
      rw [ih qs']
      show (p - q) + x * (evalCoeffs ps' x - evalCoeffs qs' x) =
           (p + x * evalCoeffs ps' x) - (q + x * evalCoeffs qs' x)
      rw [mul_sub_distrib_helper]
      exact sub_interchange_helper p q _ _

theorem evalCoeffs_listScaleR (r : Real) (qs : List Real) (x : Real) :
    evalCoeffs (listScaleR r qs) x = r * evalCoeffs qs x := by
  induction qs with
  | nil =>
    rw [listScaleR_nil, evalCoeffs_nil]
    show (0 : Real) = r * 0
    rw [mul_zero]
  | cons q qs' ih =>
    rw [listScaleR_cons, evalCoeffs_cons, evalCoeffs_cons, ih]
    exact scale_horner_helper r q x _

theorem evalCoeffs_listMulR (ps qs : List Real) (x : Real) :
    evalCoeffs (listMulR ps qs) x = evalCoeffs ps x * evalCoeffs qs x := by
  induction ps with
  | nil =>
    rw [listMulR_nil, evalCoeffs_nil]
    show (0 : Real) = 0 * evalCoeffs qs x
    rw [zero_mul]
  | cons p ps' ih =>
    rw [listMulR_cons, evalCoeffs_listAddR, evalCoeffs_listScaleR]
    rw [evalCoeffs_cons, ih]
    rw [evalCoeffs_cons]
    exact mul_horner_helper p (evalCoeffs qs x) (evalCoeffs ps' x) x

/-! ### The headline theorem — `polyCoeffs` faithfully represents `Poly.eval` -/

theorem polyCoeffs_eval (p : Poly) (x : Real) :
    evalCoeffs (polyCoeffs p) x = Poly.eval p x := by
  induction p with
  | const c =>
    rw [polyCoeffs_const, evalCoeffs_cons, evalCoeffs_nil]
    show c + x * 0 = c
    mach_ring
  | var =>
    rw [polyCoeffs_var, evalCoeffs_cons, evalCoeffs_cons, evalCoeffs_nil]
    show (0 : Real) + x * (1 + x * 0) = x
    mach_ring
  | add p q ihp ihq =>
    rw [polyCoeffs_add, evalCoeffs_listAddR, ihp, ihq]
    rfl
  | sub p q ihp ihq =>
    rw [polyCoeffs_sub, evalCoeffs_listSubR, ihp, ihq]
    rfl
  | mul p q ihp ihq =>
    rw [polyCoeffs_mul, evalCoeffs_listMulR, ihp, ihq]
    rfl

/-! ## Phase D — ring laws for the list-arithmetic helpers

Foundational identities that make the abstract polynomial-ring
structure of `List Real` (under `listAddR`, `listSubR`, `listMulR`)
provable at the list level. These are building blocks for the
canonical-form-via-eval lemma (PIT, Phase E) and the
polynomial-derivative strict-decrease theorem (Phase F). -/

/-- The all-zero list of given length. -/
noncomputable def zeroList : Nat → List Real
  | 0     => []
  | n + 1 => 0 :: zeroList n

theorem zeroList_zero : zeroList 0 = [] := rfl

theorem zeroList_succ (n : Nat) : zeroList (n + 1) = 0 :: zeroList n := rfl

theorem zeroList_length (n : Nat) : (zeroList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zeroList_succ]
    show (zeroList n).length + 1 = n + 1
    rw [ih]

/-- Evaluating the all-zero list gives zero at every point. -/
theorem evalCoeffs_zeroList (n : Nat) (x : Real) :
    evalCoeffs (zeroList n) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zeroList_succ, evalCoeffs_cons, ih]
    show (0 : Real) + x * 0 = 0
    rw [mul_zero, add_zero]

/-- `listAddR` is commutative. -/
theorem listAddR_comm (ps qs : List Real) :
    listAddR ps qs = listAddR qs ps := by
  induction ps generalizing qs with
  | nil => rw [listAddR_nil_left, listAddR_nil_right]
  | cons p ps' ih =>
    cases qs with
    | nil => rw [listAddR_nil_right, listAddR_nil_left]
    | cons q qs' =>
      rw [listAddR_cons_cons, listAddR_cons_cons, ih]
      show (p + q) :: _ = (q + p) :: _
      rw [add_comm p q]

/-- `listAddR` is associative. -/
theorem listAddR_assoc (ps qs rs : List Real) :
    listAddR (listAddR ps qs) rs = listAddR ps (listAddR qs rs) := by
  induction ps generalizing qs rs with
  | nil => rw [listAddR_nil_left, listAddR_nil_left]
  | cons p ps' ih =>
    cases qs with
    | nil => rw [listAddR_nil_right, listAddR_nil_left]
    | cons q qs' =>
      cases rs with
      | nil => rw [listAddR_nil_right, listAddR_nil_right]
      | cons r rs' =>
        rw [listAddR_cons_cons, listAddR_cons_cons,
            listAddR_cons_cons, listAddR_cons_cons, ih]
        show ((p + q) + r) :: _ = (p + (q + r)) :: _
        rw [add_assoc]

/-- `listSubR` written as a self-add identity at the eval level:
the canonical "self subtraction" eval-collapses to zero. -/
theorem evalCoeffs_listSubR_self (ps : List Real) (x : Real) :
    evalCoeffs (listSubR ps ps) x = 0 := by
  rw [evalCoeffs_listSubR]
  show evalCoeffs ps x - evalCoeffs ps x = 0
  rw [sub_self]

/-- The headline cancellation: `(P + Q) - Q` and `P` evaluate to the
same value at every point. This is the eval-level cancellation that
the `h_bridge` closure ultimately needs — though the syntactic-list
equality requires the polynomial identity theorem (Phase E). -/
theorem evalCoeffs_listSubR_listAddR_self (P Q : List Real) (x : Real) :
    evalCoeffs (listSubR (listAddR P Q) Q) x = evalCoeffs P x := by
  rw [evalCoeffs_listSubR, evalCoeffs_listAddR]
  show (evalCoeffs P x + evalCoeffs Q x) - evalCoeffs Q x = evalCoeffs P x
  rw [sub_def, add_assoc, add_neg, add_zero]

/-- A direct consequence for `polyCoeffs`: `sub (add p q) q` eval-
equals `p` at every point. This is the canonicalization claim at
the eval level — the syntactic claim at the coefficient-list level
needs PIT (Phase E). -/
theorem polyCoeffs_eval_sub_add_self (p q : Poly) (x : Real) :
    evalCoeffs (polyCoeffs (Poly.sub (Poly.add p q) q)) x =
    evalCoeffs (polyCoeffs p) x := by
  rw [polyCoeffs_sub, polyCoeffs_add]
  exact evalCoeffs_listSubR_listAddR_self _ _ x

end PolynomialCanonical
end MachLib
