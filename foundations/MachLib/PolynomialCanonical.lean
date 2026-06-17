import MachLib.PolynomialEvidence
import MachLib.PolynomialRootCount
import MachLib.Differentiation
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

/-! ## Phase E — polynomial identity theorem (PIT)

Headline: `(∀ x, evalCoeffs L x = 0) → ∀ c ∈ L, c = 0`.

Strategy: convert `evalCoeffs L` into a concrete `Poly` (via the
Horner-form `polyFromCoeffs`), bound its `degreeUpper`, then use
`poly_root_count_bound` with `L.length + 1` distinct `Real.natCast`
roots to derive contradiction if any coefficient is nonzero.

This is the eval-canonicalization lemma the `h_bridge` closure
ultimately rests on: eval-equal coefficient lists differ only by
trailing zeros. Phase F then composes PIT with the polynomial-
derivative degree-drop. -/

/-! ### Horner-form `polyFromCoeffs` -/

/-- Convert a coefficient list to a `Poly` in Horner form. -/
noncomputable def polyFromCoeffs : List Real → Poly
  | []      => Poly.const 0
  | c :: cs => Poly.add (Poly.const c) (Poly.mul Poly.var (polyFromCoeffs cs))

theorem polyFromCoeffs_nil : polyFromCoeffs [] = Poly.const 0 := rfl

theorem polyFromCoeffs_cons (c : Real) (cs : List Real) :
    polyFromCoeffs (c :: cs) =
    Poly.add (Poly.const c) (Poly.mul Poly.var (polyFromCoeffs cs)) := rfl

/-- `polyFromCoeffs L` evaluated at `x` matches `evalCoeffs L x`. -/
theorem polyFromCoeffs_eval (L : List Real) (x : Real) :
    Poly.eval (polyFromCoeffs L) x = evalCoeffs L x := by
  induction L with
  | nil =>
    rw [polyFromCoeffs_nil, evalCoeffs_nil]
    rfl
  | cons c cs ih =>
    rw [polyFromCoeffs_cons, evalCoeffs_cons]
    show Poly.eval (Poly.const c) x +
         Poly.eval (Poly.var) x * Poly.eval (polyFromCoeffs cs) x =
         c + x * evalCoeffs cs x
    rw [ih]
    rfl

/-- `degreeUpper (polyFromCoeffs L) ≤ L.length`. The Horner form
adds exactly one to `degreeUpper` per list element via the
`mul var (...)` factor. -/
theorem polyFromCoeffs_degreeUpper_le (L : List Real) :
    MachLib.PolynomialRootCount.degreeUpper (polyFromCoeffs L) ≤ L.length := by
  induction L with
  | nil =>
    show MachLib.PolynomialRootCount.degreeUpper (Poly.const 0) ≤ 0
    exact Nat.le_refl 0
  | cons c cs ih =>
    rw [polyFromCoeffs_cons]
    -- degreeUpper of add = max of children's degreeUpper.
    -- LHS: max (deg const c) (deg (mul var (polyFromCoeffs cs)))
    --    = max 0 (1 + deg (polyFromCoeffs cs))
    --    = 1 + deg (polyFromCoeffs cs)
    -- IH: deg (polyFromCoeffs cs) ≤ cs.length.
    -- Conclude: 1 + deg ≤ 1 + cs.length = (c :: cs).length.
    show Nat.max 0 (1 +
      MachLib.PolynomialRootCount.degreeUpper (polyFromCoeffs cs))
      ≤ cs.length + 1
    refine Nat.max_le.mpr ⟨Nat.zero_le _, ?_⟩
    omega

/-! ### `Real.natCast` strict monotonicity (distinctness for the root list) -/

/-- `natCast n < natCast (n + 1)`. The +1 in `natCast_succ` is
strictly positive (`zero_lt_one_ax`). -/
theorem natCast_lt_succ (n : Nat) :
    natCast n < natCast (n + 1) := by
  rw [natCast_succ]
  have h : (0 : Real) < 1 := zero_lt_one_ax
  have := add_lt_add_left h (natCast n)
  rw [add_zero] at this
  exact this

/-- `natCast` is strictly monotone: `m < n → natCast m < natCast n`. -/
theorem natCast_strict_mono : ∀ {m n : Nat}, m < n → natCast m < natCast n := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n' ih =>
    have h_le : m ≤ n' := Nat.lt_succ_iff.mp hmn
    rcases Nat.lt_or_eq_of_le h_le with hlt | heq
    · exact lt_trans_ax (ih hlt) (natCast_lt_succ n')
    · subst heq; exact natCast_lt_succ m

/-- `natCast` is injective on `Nat`: distinct `Nat`s map to distinct
`Real`s. -/
theorem natCast_injective : ∀ {m n : Nat}, m ≠ n → natCast m ≠ natCast n := by
  intro m n hmn h_eq
  rcases Nat.lt_or_ge m n with hlt | hge
  · have h_lt : natCast m < natCast n := natCast_strict_mono hlt
    rw [h_eq] at h_lt
    exact lt_irrefl_ax _ h_lt
  · rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · have h_gt : natCast n < natCast m := natCast_strict_mono hgt
      rw [h_eq] at h_gt
      exact lt_irrefl_ax _ h_gt
    · exact hmn heq.symm

/-! ### List of distinct positive `natCast` roots

For the root-count contradiction we need `L.length + 1` distinct
nonzero reals in some interval. We pick `[natCast 1, natCast 2, …,
natCast (n + 1)]`. -/

/-- `natCastList from n` produces `[natCast from, natCast (from+1), …,
natCast (from + n - 1)]`. -/
noncomputable def natCastList : Nat → Nat → List Real
  | _,    0     => []
  | from', n + 1 => natCast from' :: natCastList (from' + 1) n

theorem natCastList_length (from' n : Nat) :
    (natCastList from' n).length = n := by
  induction n generalizing from' with
  | zero => rfl
  | succ n ih =>
    show (natCast from' :: natCastList (from' + 1) n).length = n + 1
    rw [List.length_cons, ih]

/-- Transitivity of `≤` for `Real`. -/
theorem real_le_trans {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp h1 with h1lt | h1eq
  · rcases (le_iff_lt_or_eq b c).mp h2 with h2lt | h2eq
    · exact (le_iff_lt_or_eq _ _).mpr (Or.inl (lt_trans_ax h1lt h2lt))
    · exact h2eq ▸ (le_iff_lt_or_eq _ _).mpr (Or.inl h1lt)
  · exact h1eq ▸ h2

/-- All entries of `natCastList from n` are bounded above by
`natCast (from + n)`. -/
theorem natCastList_lt_upper (from' n : Nat) :
    ∀ z ∈ natCastList from' n, z < natCast (from' + n) := by
  induction n generalizing from' with
  | zero => intro z hz; cases hz
  | succ n ih =>
    intro z hz
    change z ∈ natCast from' :: natCastList (from' + 1) n at hz
    rcases List.mem_cons.mp hz with rfl | hz_in
    · apply natCast_strict_mono; omega
    · have h_ih := ih (from' + 1) z hz_in
      have h_eq : from' + 1 + n = from' + (n + 1) := by omega
      rw [h_eq] at h_ih
      exact h_ih

/-- All entries of `natCastList from n` are at least `natCast from`. -/
theorem natCastList_ge_lower (from' n : Nat) :
    ∀ z ∈ natCastList from' n, natCast from' ≤ z := by
  induction n generalizing from' with
  | zero => intro z hz; cases hz
  | succ n ih =>
    intro z hz
    change z ∈ natCast from' :: natCastList (from' + 1) n at hz
    rcases List.mem_cons.mp hz with rfl | hz_in
    · exact (le_iff_lt_or_eq _ _).mpr (Or.inr rfl)
    · have h_ih := ih (from' + 1) z hz_in
      have h_step : natCast from' ≤ natCast (from' + 1) :=
        (le_iff_lt_or_eq _ _).mpr (Or.inl (natCast_lt_succ _))
      exact real_le_trans h_step h_ih

/-- `natCastList` is Nodup: all entries are pairwise distinct. -/
theorem natCastList_nodup (from' n : Nat) :
    (natCastList from' n).Nodup := by
  induction n generalizing from' with
  | zero =>
    show (([] : List Real)).Nodup
    exact List.Pairwise.nil
  | succ n ih =>
    show (natCast from' :: natCastList (from' + 1) n).Nodup
    refine List.nodup_cons.mpr ⟨?_, ih (from' + 1)⟩
    intro h_mem
    have h_lb := natCastList_ge_lower (from' + 1) n _ h_mem
    have h_lt_step : natCast from' < natCast (from' + 1) :=
      natCast_lt_succ from'
    rcases (le_iff_lt_or_eq _ _).mp h_lb with h_lt | h_eq
    · exact lt_irrefl_ax _ (lt_trans_ax h_lt_step h_lt)
    · exact lt_irrefl_ax _ (h_eq ▸ h_lt_step)

/-! ### Eval-zero extension via root-count

If `evalCoeffs L` is zero on `{1, 2, …, L.length + 1}` (concretely
the entries of `natCastList 1 (L.length + 1)`), then by the
root-count bound `polyFromCoeffs L` has no nonzero witness — i.e.
`evalCoeffs L` is identically zero. -/

/-- The extension lemma: eval-zero on enough distinct points
forces identical-zero. -/
theorem evalCoeffs_zero_of_zero_on_natCastList (L : List Real)
    (h : ∀ z ∈ natCastList 1 (L.length + 1), evalCoeffs L z = 0) :
    ∀ x : Real, evalCoeffs L x = 0 := by
  intro x
  apply Classical.byContradiction
  intro h_ne
  -- We need a nonzero witness for poly_root_count_bound.
  have hne_poly : ∃ y : Real, Poly.eval (polyFromCoeffs L) y ≠ 0 :=
    ⟨x, by rw [polyFromCoeffs_eval]; exact h_ne⟩
  -- Pick the interval (natCast 0, natCast (L.length + 2)).
  let a := natCast 0
  let b := natCast (L.length + 2)
  have hab : a < b := by
    show natCast 0 < natCast (L.length + 2)
    exact natCast_strict_mono (by omega)
  -- The list of roots.
  let zeros := natCastList 1 (L.length + 1)
  have h_len : zeros.length = L.length + 1 := natCastList_length _ _
  have h_nodup : zeros.Nodup := natCastList_nodup _ _
  have h_in_interval : ∀ z ∈ zeros, a < z ∧ z < b ∧
                       Poly.eval (polyFromCoeffs L) z = 0 := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩
    · -- a = natCast 0 < z: z ≥ natCast 1 > natCast 0.
      have h_ge_one : natCast 1 ≤ z := natCastList_ge_lower 1 _ z hz
      have h_zero_lt_one : natCast 0 < natCast 1 :=
        natCast_strict_mono (by omega)
      rcases (le_iff_lt_or_eq _ _).mp h_ge_one with h_lt | h_eq
      · exact lt_trans_ax h_zero_lt_one h_lt
      · exact h_eq ▸ h_zero_lt_one
    · -- z < b = natCast (L.length + 2): z < natCast (1 + (L.length + 1)) =
      -- natCast (L.length + 2).
      have h_lt_upper : z < natCast (1 + (L.length + 1)) :=
        natCastList_lt_upper 1 _ z hz
      have h_eq : 1 + (L.length + 1) = L.length + 2 := by omega
      rw [h_eq] at h_lt_upper
      exact h_lt_upper
    · rw [polyFromCoeffs_eval]
      exact h z hz
  -- Apply poly_root_count_bound.
  have h_bound : zeros.length ≤
      MachLib.PolynomialRootCount.degreeUpper (polyFromCoeffs L) :=
    MachLib.PolynomialRootCount.poly_root_count_bound
      (polyFromCoeffs L) a b hab hne_poly zeros h_nodup h_in_interval
  -- Contradiction: zeros.length = L.length + 1 > degreeUpper ≤ L.length.
  rw [h_len] at h_bound
  have h_deg_le : MachLib.PolynomialRootCount.degreeUpper
                    (polyFromCoeffs L) ≤ L.length :=
    polyFromCoeffs_degreeUpper_le L
  omega

/-! ### The polynomial identity theorem -/

/-- Cancellation: if `z ≠ 0` and `z * y = 0`, then `y = 0`. -/
theorem zero_of_mul_left_ne_zero (z y : Real)
    (hz : z ≠ 0) (h : z * y = 0) : y = 0 := by
  have h_inv : (1 / z) * z = 1 := by
    rw [mul_comm]; exact mul_inv z hz
  calc y
      = 1 * y               := (one_mul_thm y).symm
    _ = ((1 / z) * z) * y    := by rw [h_inv]
    _ = (1 / z) * (z * y)    := by rw [mul_assoc]
    _ = (1 / z) * 0          := by rw [h]
    _ = 0                    := mul_zero _

/-- **PIT.** If `evalCoeffs L x = 0` for every `x`, then every
coefficient in `L` is zero. -/
theorem evalCoeffs_zero_iff_all_zero (L : List Real)
    (h : ∀ x : Real, evalCoeffs L x = 0) :
    ∀ c ∈ L, c = 0 := by
  induction L with
  | nil => intro c hc; cases hc
  | cons c cs ih =>
    have h_c : c = 0 := by
      have h0 := h 0
      rw [evalCoeffs_cons] at h0
      show c = 0
      have : c + 0 * evalCoeffs cs 0 = 0 := h0
      rw [zero_mul, add_zero] at this
      exact this
    -- Recurse: need `∀ x, evalCoeffs cs x = 0`.
    have h_cs : ∀ x : Real, evalCoeffs cs x = 0 := by
      apply evalCoeffs_zero_of_zero_on_natCastList
      intro z hz
      have h_z := h z
      rw [evalCoeffs_cons, h_c, zero_add] at h_z
      -- h_z : z * evalCoeffs cs z = 0
      -- z > 0 → z ≠ 0 → evalCoeffs cs z = 0.
      have h_z_pos : (0 : Real) < z := by
        have h_lb : natCast 1 ≤ z := natCastList_ge_lower 1 _ z hz
        have h_zero_lt_one : (0 : Real) < natCast 1 := by
          have : natCast 0 < natCast 1 := natCast_strict_mono (by omega)
          rw [natCast_zero] at this
          exact this
        rcases (le_iff_lt_or_eq _ _).mp h_lb with h_lt | h_eq
        · exact lt_trans_ax h_zero_lt_one h_lt
        · exact h_eq ▸ h_zero_lt_one
      have h_z_ne : z ≠ 0 := fun heq => lt_irrefl_ax _ (heq ▸ h_z_pos)
      exact zero_of_mul_left_ne_zero z _ h_z_ne h_z
    intro c' hc'
    change c' ∈ c :: cs at hc'
    rcases List.mem_cons.mp hc' with rfl | hc'_in
    · exact h_c
    · exact ih h_cs c' hc'_in

/-! ## Phase F — polynomial derivative at the coefficient-list level

Coefficient-list mirror of the polynomial derivative
(`PolynomialRootCount.polyDerivative` works on the AST). With these
in hand, the strict-decrease theorem on canonical degree under
derivative — and ultimately the `h_bridge` closure — becomes a
matter of bookkeeping.

`polyDerivativeCoeffs [c_0, c_1, c_2, …, c_n] = [c_1, 2·c_2, 3·c_3, …, n·c_n]`:
drops the constant term and scales each remaining coefficient by
its position. -/

/-- Scale each entry of a list by its position (offset by `start`):
`listScaleByPos [c_0, c_1, …] k = [k·c_0, (k+1)·c_1, …]`. -/
noncomputable def listScaleByPos : List Real → Nat → List Real
  | [],       _ => []
  | c :: cs,  k => natCast k * c :: listScaleByPos cs (k + 1)

theorem listScaleByPos_nil (k : Nat) : listScaleByPos [] k = [] := rfl

theorem listScaleByPos_cons (c : Real) (cs : List Real) (k : Nat) :
    listScaleByPos (c :: cs) k = natCast k * c :: listScaleByPos cs (k + 1) := rfl

/-- The coefficient-list polynomial derivative. -/
noncomputable def polyDerivativeCoeffs : List Real → List Real
  | []       => []
  | _ :: cs  => listScaleByPos cs 1

theorem polyDerivativeCoeffs_nil : polyDerivativeCoeffs [] = [] := rfl

theorem polyDerivativeCoeffs_cons (c : Real) (cs : List Real) :
    polyDerivativeCoeffs (c :: cs) = listScaleByPos cs 1 := rfl

/-! ### Step-shift identity for `listScaleByPos`

`eval (listScaleByPos cs (k+1)) x = eval cs x + eval (listScaleByPos cs k) x`.
Both sides represent `Σ_i (k + i + 1) c_i x^i`; the +1 shift contributes
exactly an extra `Σ_i c_i x^i = eval cs x`. -/

/-- AC identity used by the step-shift proof:
`(a + b) + (X + Y) = (b + X) + (a + Y)`. -/
theorem step_shift_helper (a b X Y : Real) :
    (a + b) + (X + Y) = (b + X) + (a + Y) := by mach_ring

theorem evalCoeffs_listScaleByPos_succ (cs : List Real) (k : Nat) (x : Real) :
    evalCoeffs (listScaleByPos cs (k + 1)) x =
    evalCoeffs cs x + evalCoeffs (listScaleByPos cs k) x := by
  induction cs generalizing k with
  | nil =>
    rw [listScaleByPos_nil, evalCoeffs_nil]
    show (0 : Real) = 0 + 0
    rw [add_zero]
  | cons c cs' ih =>
    rw [listScaleByPos_cons, listScaleByPos_cons, evalCoeffs_cons]
    -- LHS: natCast (k+1) * c + x * evalCoeffs (listScaleByPos cs' (k+1+1)) x
    rw [ih (k + 1)]
    -- LHS: natCast (k+1) * c + x * (evalCoeffs cs' x + evalCoeffs (listScaleByPos cs' (k+1)) x)
    rw [evalCoeffs_cons]
    -- RHS: (c + x * evalCoeffs cs' x) + evalCoeffs (natCast k * c :: listScaleByPos cs' (k+1)) x
    rw [evalCoeffs_cons]
    -- RHS: (c + x * evalCoeffs cs' x) + (natCast k * c + x * evalCoeffs (listScaleByPos cs' (k+1)) x)
    rw [natCast_succ, mul_distrib_right, one_mul_thm, mul_distrib]
    -- LHS: (natCast k * c + c) + (x * evalCoeffs cs' x + x * evalCoeffs (listScaleByPos cs' (k+1)) x)
    -- RHS: (c + x * evalCoeffs cs' x) + (natCast k * c + x * evalCoeffs (listScaleByPos cs' (k+1)) x)
    exact step_shift_helper (natCast k * c) c _ _

/-- The structural recursion for `polyDerivativeCoeffs` at eval level:
`eval (polyDerivativeCoeffs (c :: cs)) x = eval cs x + x · eval (polyDerivativeCoeffs cs) x`.
This is what makes the product rule fall out cleanly in the
HasDerivAt proof. -/
theorem evalCoeffs_polyDerivativeCoeffs_cons (c : Real) (cs : List Real) (x : Real) :
    evalCoeffs (polyDerivativeCoeffs (c :: cs)) x =
    evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x := by
  rw [polyDerivativeCoeffs_cons]
  -- Apply step-shift with k = 0: eval (listScaleByPos cs 1) = eval cs + eval (listScaleByPos cs 0).
  rw [evalCoeffs_listScaleByPos_succ cs 0 x]
  -- Need: evalCoeffs cs x + evalCoeffs (listScaleByPos cs 0) x =
  --       evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x.
  show evalCoeffs cs x + evalCoeffs (listScaleByPos cs 0) x =
       evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x
  -- Strip the common `evalCoeffs cs x +` on both sides.
  congr 1
  -- Now: evalCoeffs (listScaleByPos cs 0) x = x * evalCoeffs (polyDerivativeCoeffs cs) x.
  cases cs with
  | nil =>
    rw [listScaleByPos_nil, polyDerivativeCoeffs_nil, evalCoeffs_nil]
    show (0 : Real) = x * 0
    rw [mul_zero]
  | cons c' cs' =>
    rw [listScaleByPos_cons, evalCoeffs_cons,
        natCast_zero, zero_mul, zero_add, polyDerivativeCoeffs_cons]

/-! ### HasDerivAt correspondence

The formal derivative `polyDerivativeCoeffs` matches the analytic
derivative of `evalCoeffs` everywhere. Standard sum/product rule
induction. -/

theorem polyDerivativeCoeffs_hasDerivAt (L : List Real) (x : Real) :
    HasDerivAt (evalCoeffs L) (evalCoeffs (polyDerivativeCoeffs L) x) x := by
  induction L with
  | nil =>
    rw [polyDerivativeCoeffs_nil, evalCoeffs_nil]
    show HasDerivAt (fun y => evalCoeffs ([] : List Real) y) 0 x
    show HasDerivAt (fun _ => (0 : Real)) 0 x
    exact HasDerivAt_const 0 x
  | cons c cs ih =>
    rw [evalCoeffs_polyDerivativeCoeffs_cons]
    -- Want: HasDerivAt (eval (c :: cs)) (eval cs x + x * eval (polyDerivativeCoeffs cs) x) x.
    -- eval (c :: cs) y = c + y * eval cs y.
    -- d/dy at y=x: 0 + (1 * eval cs x + x * eval (polyDerivativeCoeffs cs) x).
    show HasDerivAt (fun y => evalCoeffs (c :: cs) y)
           (evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x) x
    have h_unfold : (fun y => evalCoeffs (c :: cs) y) =
                    (fun y => c + y * evalCoeffs cs y) := by
      funext y; rw [evalCoeffs_cons]
    rw [h_unfold]
    -- Sum rule on `c + (y * evalCoeffs cs y)`:
    have h_const : HasDerivAt (fun _ : Real => c) 0 x := HasDerivAt_const c x
    have h_id : HasDerivAt (fun y : Real => y) 1 x := HasDerivAt_id x
    have h_mul : HasDerivAt (fun y => y * evalCoeffs cs y)
                  (1 * evalCoeffs cs x +
                   x * evalCoeffs (polyDerivativeCoeffs cs) x) x :=
      HasDerivAt_mul (fun y => y) (evalCoeffs cs) 1
        (evalCoeffs (polyDerivativeCoeffs cs) x) x h_id ih
    have h_sum := HasDerivAt_add (fun _ => c) (fun y => y * evalCoeffs cs y)
                    0 (1 * evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x)
                    x h_const h_mul
    -- The derivative provided by h_sum is 0 + (1 * evalCoeffs cs x + x * ...).
    -- We need it as: evalCoeffs cs x + x * ....
    have h_eq : (0 : Real) + (1 * evalCoeffs cs x +
                  x * evalCoeffs (polyDerivativeCoeffs cs) x) =
                evalCoeffs cs x + x * evalCoeffs (polyDerivativeCoeffs cs) x := by
      rw [zero_add, one_mul_thm]
    rw [← h_eq]
    exact h_sum

/-! ## Phase G — `polyTrueDegree` + strict decrease + PIT bridge

The actual canonical degree: the smallest `n` such that all
coefficient-list entries at positions > n are zero. Built via
`Nat.find` over a classically-decidable predicate.

This is the eval-canonical degree the `h_bridge` closure rides on:
ring-equivalent polynomials produce equal `polyTrueDegree`, and
the polynomial derivative drops it by exactly one (when positive). -/

/-! ### Indexed coefficient extraction -/

/-- `coeffAt L k` is the coefficient at position `k` in `L`, with
0 for out-of-range indices. -/
noncomputable def coeffAt : List Real → Nat → Real
  | [],       _     => 0
  | c :: _,   0     => c
  | _ :: cs,  k + 1 => coeffAt cs k

theorem coeffAt_nil (k : Nat) : coeffAt [] k = 0 := by
  cases k <;> rfl

theorem coeffAt_cons_zero (c : Real) (cs : List Real) :
    coeffAt (c :: cs) 0 = c := rfl

theorem coeffAt_cons_succ (c : Real) (cs : List Real) (k : Nat) :
    coeffAt (c :: cs) (k + 1) = coeffAt cs k := rfl

theorem coeffAt_out_of_range (L : List Real) (k : Nat) (h : k ≥ L.length) :
    coeffAt L k = 0 := by
  induction L generalizing k with
  | nil => exact coeffAt_nil k
  | cons c cs ih =>
    cases k with
    | zero =>
      show c = 0
      exfalso; simp at h
    | succ k' =>
      rw [coeffAt_cons_succ]
      apply ih
      simp at h
      omega

/-! ### `polyDegreeBoundedBy` and `polyTrueDegree` -/

/-- `polyDegreeBoundedBy L n`: every coefficient of `L` at position
`> n` is zero. -/
def polyDegreeBoundedBy (L : List Real) (n : Nat) : Prop :=
  ∀ k, k > n → coeffAt L k = 0

theorem polyDegreeBoundedBy_at_length (L : List Real) :
    polyDegreeBoundedBy L L.length := by
  intro k hk
  exact coeffAt_out_of_range L k (Nat.le_of_lt hk)

theorem polyDegreeBoundedBy_exists (L : List Real) :
    ∃ n, polyDegreeBoundedBy L n :=
  ⟨L.length, polyDegreeBoundedBy_at_length L⟩

/-- The well-ordering principle for `Nat`: every non-empty subset
(presented as a `Prop`-valued predicate with an existential witness)
has a least element. Proven by strong induction on the witness; no
Mathlib dependency. -/
theorem nat_least_element (P : Nat → Prop) (h_ex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨witness, h_w⟩ := h_ex
  induction witness using Nat.strongRecOn with
  | _ k ih =>
    by_cases h_min : ∀ m, m < k → ¬ P m
    · exact ⟨k, h_w, h_min⟩
    · -- ¬ ∀ m, m < k → ¬ P m ⇒ ∃ m < k, P m.
      have h_exists : ∃ m, m < k ∧ P m := by
        apply Classical.byContradiction
        intro h_no
        apply h_min
        intro m hm_lt hm_P
        exact h_no ⟨m, hm_lt, hm_P⟩
      obtain ⟨m, hm_lt, hm_P⟩ := h_exists
      exact ih m hm_lt hm_P

/-- The true polynomial degree of a coefficient list: the smallest
`n` such that positions > n have zero coefficient. -/
noncomputable def polyTrueDegree (L : List Real) : Nat :=
  Classical.choose (nat_least_element _ (polyDegreeBoundedBy_exists L))

/-- `polyTrueDegree L` is itself a valid bound. -/
theorem polyTrueDegree_spec (L : List Real) :
    polyDegreeBoundedBy L (polyTrueDegree L) :=
  (Classical.choose_spec (nat_least_element _ (polyDegreeBoundedBy_exists L))).1

/-- Below `polyTrueDegree` the predicate fails (the bound is tight). -/
theorem not_polyDegreeBoundedBy_below (L : List Real) (k : Nat)
    (hk : k < polyTrueDegree L) : ¬ polyDegreeBoundedBy L k :=
  (Classical.choose_spec (nat_least_element _ (polyDegreeBoundedBy_exists L))).2 k hk

/-- Minimality: any valid bound is at least `polyTrueDegree`. -/
theorem polyTrueDegree_le_of_bounded (L : List Real) (n : Nat)
    (h : polyDegreeBoundedBy L n) : polyTrueDegree L ≤ n := by
  apply Classical.byContradiction
  intro h_not_le
  have h_lt : n < polyTrueDegree L := Nat.lt_of_not_le h_not_le
  exact not_polyDegreeBoundedBy_below L n h_lt h

/-! ### `coeffAt` for `listScaleByPos` and `polyDerivativeCoeffs` -/

theorem coeffAt_listScaleByPos (cs : List Real) (start k : Nat) :
    coeffAt (listScaleByPos cs start) k = natCast (start + k) * coeffAt cs k := by
  induction cs generalizing start k with
  | nil =>
    simp only [listScaleByPos_nil, coeffAt_nil]
    rw [mul_zero]
  | cons c cs' ih =>
    rw [listScaleByPos_cons]
    cases k with
    | zero =>
      simp only [coeffAt_cons_zero]
      show natCast start * c = natCast (start + 0) * c
      rw [Nat.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ]
      rw [ih]
      show natCast (start + 1 + k') * coeffAt cs' k' = natCast (start + (k' + 1)) * coeffAt cs' k'
      have : start + 1 + k' = start + (k' + 1) := by omega
      rw [this]

theorem coeffAt_polyDerivativeCoeffs (L : List Real) (k : Nat) :
    coeffAt (polyDerivativeCoeffs L) k = natCast (k + 1) * coeffAt L (k + 1) := by
  cases L with
  | nil =>
    rw [polyDerivativeCoeffs_nil, coeffAt_nil, coeffAt_nil, mul_zero]
  | cons c cs =>
    rw [polyDerivativeCoeffs_cons, coeffAt_listScaleByPos, coeffAt_cons_succ]
    show natCast (1 + k) * coeffAt cs k = natCast (k + 1) * coeffAt cs k
    have : (1 + k) = (k + 1) := by omega
    rw [this]

/-! ### Strict decrease of `polyTrueDegree` under `polyDerivativeCoeffs`

If `polyTrueDegree L > 0`, then there's a nonzero coefficient at
some position > polyTrueDegree L - 1. Applying `polyDerivativeCoeffs`
scales by `(k+1) > 0`, so the result has a bound of
`polyTrueDegree L - 1`. -/

/-- `natCast (k+1) ≠ 0` for any `k : Nat`. -/
theorem natCast_succ_ne_zero (k : Nat) : natCast (k + 1) ≠ 0 := by
  intro h_eq
  have h_pos : (0 : Real) < natCast (k + 1) := by
    have : natCast 0 < natCast (k + 1) := natCast_strict_mono (by omega)
    rw [natCast_zero] at this
    exact this
  rw [h_eq] at h_pos
  exact lt_irrefl_ax _ h_pos

/-- Product cancellation: `a ≠ 0` and `b ≠ 0` ⇒ `a * b ≠ 0`. -/
theorem mul_ne_zero_helper (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h_zero
  -- a * b = 0 with a ≠ 0 ⇒ b = 0 (zero_of_mul_left_ne_zero).
  exact hb (zero_of_mul_left_ne_zero a b ha h_zero)

/-- The strict-decrease theorem at coefficient-list level:
`polyTrueDegree (polyDerivativeCoeffs L) < polyTrueDegree L`
when `polyTrueDegree L > 0`. -/
theorem polyTrueDegree_polyDerivativeCoeffs_lt (L : List Real)
    (h : polyTrueDegree L > 0) :
    polyTrueDegree (polyDerivativeCoeffs L) < polyTrueDegree L := by
  have h_bounded :
      polyDegreeBoundedBy (polyDerivativeCoeffs L) (polyTrueDegree L - 1) := by
    intro j hj
    have hj' : j + 1 > polyTrueDegree L := by omega
    have h_zero : coeffAt L (j + 1) = 0 := polyTrueDegree_spec L (j + 1) hj'
    rw [coeffAt_polyDerivativeCoeffs, h_zero, mul_zero]
  have h_le : polyTrueDegree (polyDerivativeCoeffs L) ≤ polyTrueDegree L - 1 :=
    polyTrueDegree_le_of_bounded (polyDerivativeCoeffs L)
      (polyTrueDegree L - 1) h_bounded
  omega

/-! ### PIT bridge: eval-equal lists have equal `polyTrueDegree`

If `L1` and `L2` evaluate to the same function, then PIT applied to
`listSubR L1 L2` (which evaluates to identically zero) gives all
its coefficients are zero, hence `coeffAt L1 k = coeffAt L2 k` for
every position. Therefore `polyDegreeBoundedBy L1 = polyDegreeBoundedBy L2`,
and `polyTrueDegree L1 = polyTrueDegree L2`. -/

/-- `coeffAt` of `listSubR` at position `k`: it's the element-wise
sub at `k` (with out-of-range positions treated as 0). -/
theorem coeffAt_listSubR (L1 L2 : List Real) (k : Nat) :
    coeffAt (listSubR L1 L2) k = coeffAt L1 k - coeffAt L2 k := by
  induction L1 generalizing L2 k with
  | nil =>
    induction L2 generalizing k with
    | nil =>
      simp only [listSubR_nil_nil, coeffAt_nil]
      rw [sub_self]
    | cons q qs' ih_q =>
      rw [listSubR_nil_cons]
      cases k with
      | zero =>
        simp only [coeffAt_cons_zero, coeffAt_nil]
      | succ k' =>
        rw [coeffAt_cons_succ, ih_q k']
        simp only [coeffAt_cons_succ, coeffAt_nil]
  | cons p ps' ih =>
    cases L2 with
    | nil =>
      rw [listSubR_cons_nil]
      cases k with
      | zero =>
        simp only [coeffAt_cons_zero, coeffAt_nil]
        rw [sub_def, neg_zero, add_zero]
      | succ k' =>
        simp only [coeffAt_cons_succ, coeffAt_nil]
        rw [sub_def, neg_zero, add_zero]
    | cons q qs' =>
      rw [listSubR_cons_cons]
      cases k with
      | zero => simp only [coeffAt_cons_zero]
      | succ k' =>
        simp only [coeffAt_cons_succ]
        exact ih qs' k'

/-- If `listSubR L1 L2` has all coefficients zero (in the PIT sense),
then `coeffAt L1 = coeffAt L2` everywhere. -/
theorem coeffAt_eq_of_evalCoeffs_eq (L1 L2 : List Real)
    (h_eval : ∀ x, evalCoeffs L1 x = evalCoeffs L2 x) :
    ∀ k, coeffAt L1 k = coeffAt L2 k := by
  -- The difference list listSubR L1 L2 evaluates to 0 everywhere.
  have h_diff_zero : ∀ x, evalCoeffs (listSubR L1 L2) x = 0 := by
    intro x
    rw [evalCoeffs_listSubR, h_eval x]
    exact sub_self _
  -- PIT: every entry of listSubR L1 L2 is zero.
  have h_pit : ∀ c ∈ listSubR L1 L2, c = 0 :=
    evalCoeffs_zero_iff_all_zero (listSubR L1 L2) h_diff_zero
  -- Now: coeffAt (listSubR L1 L2) k = 0 for every k.
  intro k
  have h_coeff_zero : coeffAt (listSubR L1 L2) k = 0 := by
    -- coeffAt (listSubR L1 L2) k is either a list entry (in which case h_pit gives 0)
    -- or out-of-range (in which case coeffAt = 0 by coeffAt_out_of_range).
    by_cases h_k : k < (listSubR L1 L2).length
    · -- In range: the k-th entry is in the list, and h_pit says it's 0.
      exact coeffAt_in_list_zero (listSubR L1 L2) k h_k h_pit
    · -- Out of range.
      exact coeffAt_out_of_range _ k (Nat.not_lt.mp h_k)
  -- Combine with coeffAt_listSubR.
  rw [coeffAt_listSubR] at h_coeff_zero
  -- h_coeff_zero : coeffAt L1 k - coeffAt L2 k = 0
  -- ⇒ coeffAt L1 k = coeffAt L2 k.
  have : coeffAt L1 k = 0 + coeffAt L2 k := by
    rw [sub_def] at h_coeff_zero
    -- coeffAt L1 k + (- coeffAt L2 k) = 0
    -- ⇒ coeffAt L1 k = - (- coeffAt L2 k) = coeffAt L2 k.
    have h_inv : coeffAt L1 k + (- coeffAt L2 k) = 0 := h_coeff_zero
    -- Add coeffAt L2 k to both sides.
    have h_step : (coeffAt L1 k + (- coeffAt L2 k)) + coeffAt L2 k =
                  0 + coeffAt L2 k := by rw [h_inv]
    rw [add_assoc] at h_step
    rw [add_comm (- coeffAt L2 k) (coeffAt L2 k), add_neg, add_zero] at h_step
    exact h_step
  rw [zero_add] at this
  exact this
where
  /-- Helper: if all entries of a list are zero, then `coeffAt` at any
  in-range position is zero. -/
  coeffAt_in_list_zero (L : List Real) (k : Nat) (hk : k < L.length)
      (h : ∀ c ∈ L, c = 0) : coeffAt L k = 0 := by
    induction L generalizing k with
    | nil => simp at hk
    | cons c cs ih_cs =>
      cases k with
      | zero =>
        rw [coeffAt_cons_zero]
        exact h c (List.mem_cons_self _ _)
      | succ k' =>
        rw [coeffAt_cons_succ]
        apply ih_cs k' (by simp at hk; omega)
        intro c' hc'
        exact h c' (List.mem_cons_of_mem _ hc')

/-- The headline PIT-bridged degree-equality theorem. -/
theorem polyTrueDegree_eq_of_evalCoeffs_eq (L1 L2 : List Real)
    (h_eval : ∀ x, evalCoeffs L1 x = evalCoeffs L2 x) :
    polyTrueDegree L1 = polyTrueDegree L2 := by
  have h_coeff : ∀ k, coeffAt L1 k = coeffAt L2 k :=
    coeffAt_eq_of_evalCoeffs_eq L1 L2 h_eval
  -- polyDegreeBoundedBy depends only on coeffAt. So it's the same for L1 and L2.
  have h_iff : ∀ n, polyDegreeBoundedBy L1 n ↔ polyDegreeBoundedBy L2 n := by
    intro n
    constructor
    · intro h k hk
      rw [← h_coeff k]
      exact h k hk
    · intro h k hk
      rw [h_coeff k]
      exact h k hk
  -- Both directions of ≤ via the iff + minimality.
  apply Nat.le_antisymm
  · exact polyTrueDegree_le_of_bounded L1 (polyTrueDegree L2)
      ((h_iff _).mpr (polyTrueDegree_spec L2))
  · exact polyTrueDegree_le_of_bounded L2 (polyTrueDegree L1)
      ((h_iff _).mp (polyTrueDegree_spec L1))

end PolynomialCanonical
end MachLib
