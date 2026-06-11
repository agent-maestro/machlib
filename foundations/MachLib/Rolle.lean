import MachLib.Exp
import MachLib.Log
import MachLib.Differentiation
import MachLib.AnalyticFiniteZeros
import MachLib.Ring

/-!
# Rolle's Theorem — header port (Phase B of Pfaffian programme)

Axiomatizes Rolle's theorem and its zero-count corollary. The proofs
are deferred to Phase C (the constructive Khovanskii proof) which
combines Rolle + induction-on-Pfaffian-chain-order to derive the
zero bound.

**Strategic purpose:** Phase B is the building block for Phase C.
Rolle's theorem says: between any two zeros of a differentiable
function, the derivative has a zero. Iterating: a function of
Pfaffian order `n` has zero count bounded by a polynomial in n+1
applications of Rolle to derive zero bounds inductively.

**Scope of this file:**

1. `rolle` axiom: standard Rolle's theorem.
2. `zero_count_bound_by_deriv` axiom: zero count of f is at most
   1 + zero count of f', expressed in the list-of-zeros form
   compatible with `PfaffianFunction.zero_count_le`.

**Phase C plan:**

Phase C uses Rolle + induction on Pfaffian chain order to prove:
- Base case: order-0 Pfaffian functions are polynomials in x alone,
  with bounded zero count via `PolynomialRootCount` (already in
  MachLib).
- Inductive step: f of order n has derivative f' which is Pfaffian
  of order ≤ n (the chain stays the same, the polynomial degree
  changes). Apply `zero_count_bound_by_deriv` and use the inductive
  hypothesis.

The final theorem (Phase C) replaces Phase A's
`PfaffianFunction.zero_bound` axiom with a constructive proof.

**Honest scope:** This file ports the Rolle statement; it does NOT
prove it. Continuity + extreme-value-theorem-based proof of Rolle
is itself non-trivial and would require porting MachLib's
`IsAnalyticOnReals` framework (from `AnalyticFiniteZeros.lean`) with
continuity bridges, plus an axiomatic extreme value theorem. Phase
B's role is to commit to the STATEMENT so that Phase C can use it.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## Rolle's theorem (axiomatized) -/

/-- **Rolle's theorem.** If `f` is differentiable on `(a, b)` (every
point has a derivative) and `f a = f b`, then there exists a point
`c ∈ (a, b)` where the derivative of `f` is zero.

Axiomatized. The classical proof uses the extreme value theorem +
the necessary-condition lemma for extrema (`Fermat's theorem`); both
require continuity infrastructure not yet in MachLib.

The differentiability hypothesis is encoded as: for every `c ∈ (a, b)`,
there exists some `f' : Real` with `HasDerivAt f f' c`. -/
axiom rolle (f : Real → Real) (a b : Real) (hab : a < b)
    (hfa_eq_fb : f a = f b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, a < c ∧ c < b ∧ HasDerivAt f 0 c

/-! ## Mean Value Theorem (consequence of Rolle)

**Khovanskii sprint week 1 chunk 1 (2026-06-11):** axiom-to-theorem
conversion landed. The prior session's `mach_ring` block at the
`h a = h b` step left residue on the AC normalisation of an 8-term
polynomial. Replaced with the explicit factor-cancel:

  (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    = (b - a) * (f b - f a) - (f b - f a) * (b - a)   [mul_distrib + mul_neg]
    = (b - a) * (f b - f a) - (b - a) * (f b - f a)   [mul_comm]
    = 0                                                [sub_self]

Two other surprises hit during the closure:

1. MachLib has no `mul_sub` axiom. Derived inline via
   `sub_def + mul_distrib + mul_neg`.

2. `rw [sub_def]` only rewrites a single subtraction occurrence per
   call (each `rw` step targets the first match). The prior session's
   chain mixed pre- and post-`sub_def` forms and failed pattern
   match on the later steps. Fixed by using `simp only [sub_def]`
   to normalise all subtractions in one pass before continuing with
   targeted rewrites.

The axiom previously at this position has been removed; the two
KhovanskiiLemma.lean consumers automatically pick up the theorem
because the name is preserved. -/

/-- **Mean Value Theorem.** If `f` is differentiable on `(a, b)`, there
exists `c ∈ (a, b)` and `f' : Real` such that `HasDerivAt f f' c`
and `f b - f a = f' * (b - a)`.

Constructive proof via Rolle applied to the auxiliary function
`h(x) := (b - a) * f(x) - (b - a) * f(a) - (f(b) - f(a)) * (x - a)`,
which is crafted so that `h a = h b = 0`. -/
theorem mean_value_theorem (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, ∃ f' : Real, a < c ∧ c < b ∧ HasDerivAt f f' c ∧
      f b - f a = f' * (b - a) := by
  -- Auxiliary function h(x) = (b-a)*f(x) - (b-a)*f(a) - (f(b) - f(a))*(x - a).
  -- Crafted so that h(a) = h(b) = 0 algebraically, making Rolle applicable.
  let h : Real → Real := fun x =>
    (b - a) * f x - (b - a) * f a - (f b - f a) * (x - a)
  -- Step 1: h a = h b.
  have hfa_eq_fb : h a = h b := by
    show (b - a) * f a - (b - a) * f a - (f b - f a) * (a - a) =
         (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    rw [sub_self a, mul_zero, sub_zero]
    -- Goal: (b - a) * f a - (b - a) * f a =
    --       (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    have hlhs : (b - a) * f a - (b - a) * f a = 0 := sub_self _
    rw [hlhs]
    -- Goal: 0 = (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    -- Explicit factor-cancel replacing the prior session's failed mach_ring.
    -- MachLib has no `mul_sub` axiom; derive it from sub_def + mul_distrib + mul_neg.
    have hidentity :
        (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a) = 0 := by
      have step1 : (b - a) * (f b - f a) = (b - a) * f b - (b - a) * f a := by
        -- sub_def rewrites only one subtraction per `rw` call, so use simp
        -- only to normalise both `f b - f a` and the outer `-` consistently.
        simp only [sub_def]
        rw [mul_distrib, mul_neg]
      have step2 : (f b - f a) * (b - a) = (b - a) * (f b - f a) := mul_comm _ _
      rw [← step1, step2]
      exact sub_self _
    rw [hidentity]
  -- Step 2: h is differentiable on (a, b) with derivative
  --   h'(c) = (b - a) * f'_c - 0 - (f b - f a).
  have h_diff : ∀ c : Real, a < c → c < b →
      ∃ h' : Real, HasDerivAt h h' c := by
    intro c hca hcb
    obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
    -- g1(x) = (b - a) * f x;  g1'(c) = (b - a) * f'_c.
    have hg1 : HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c := by
      have h_const : HasDerivAt (fun _ : Real => b - a) 0 c := HasDerivAt_const (b - a) c
      have h_prod := HasDerivAt_mul (fun _ => b - a) f 0 f'_c c h_const hf'_c
      have h_simp : (0 : Real) * f c + (b - a) * f'_c = (b - a) * f'_c := by
        rw [zero_mul, zero_add]
      rw [h_simp] at h_prod
      exact h_prod
    -- g2(x) = (b - a) * f a (constant); g2'(c) = 0.
    have hg2 : HasDerivAt (fun _ : Real => (b - a) * f a) 0 c :=
      HasDerivAt_const _ c
    -- g3(x) = (f b - f a) * (x - a); g3'(c) = f b - f a.
    have hg3 : HasDerivAt (fun x => (f b - f a) * (x - a)) (f b - f a) c := by
      have h_id : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
      have h_const_a : HasDerivAt (fun _ : Real => a) 0 c := HasDerivAt_const a c
      have h_sub : HasDerivAt (fun y => y - a) (1 - 0) c :=
        HasDerivAt_sub (fun y => y) (fun _ => a) 1 0 c h_id h_const_a
      have h_sub_simp : (1 : Real) - 0 = 1 := sub_zero 1
      rw [h_sub_simp] at h_sub
      have h_const_fba : HasDerivAt (fun _ : Real => f b - f a) 0 c := HasDerivAt_const _ c
      have h_prod := HasDerivAt_mul (fun _ => f b - f a) (fun x => x - a) 0 1 c h_const_fba h_sub
      have h_simp : (0 : Real) * (c - a) + (f b - f a) * 1 = f b - f a := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [h_simp] at h_prod
      exact h_prod
    -- h = g1 - g2 - g3.
    have h_g12 : HasDerivAt (fun x => (b - a) * f x - (b - a) * f a) ((b - a) * f'_c - 0) c :=
      HasDerivAt_sub _ _ _ _ c hg1 hg2
    have h_full : HasDerivAt h ((b - a) * f'_c - 0 - (f b - f a)) c :=
      HasDerivAt_sub _ _ _ _ c h_g12 hg3
    exact ⟨(b - a) * f'_c - 0 - (f b - f a), h_full⟩
  -- Step 3: apply Rolle to h, obtain c ∈ (a, b) with h'(c) = 0.
  obtain ⟨c, hca, hcb, h_zero⟩ := rolle h a b hab hfa_eq_fb h_diff
  obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
  -- Re-derive h's derivative at c so we can compare with the 0 from Rolle.
  have h_derived : HasDerivAt h ((b - a) * f'_c - 0 - (f b - f a)) c := by
    have hg1 : HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c := by
      have h_const : HasDerivAt (fun _ : Real => b - a) 0 c := HasDerivAt_const (b - a) c
      have h_prod := HasDerivAt_mul (fun _ => b - a) f 0 f'_c c h_const hf'_c
      have h_simp : (0 : Real) * f c + (b - a) * f'_c = (b - a) * f'_c := by
        rw [zero_mul, zero_add]
      rw [h_simp] at h_prod
      exact h_prod
    have hg2 : HasDerivAt (fun _ : Real => (b - a) * f a) 0 c := HasDerivAt_const _ c
    have hg3 : HasDerivAt (fun x => (f b - f a) * (x - a)) (f b - f a) c := by
      have h_id : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
      have h_const_a : HasDerivAt (fun _ : Real => a) 0 c := HasDerivAt_const a c
      have h_sub : HasDerivAt (fun y => y - a) (1 - 0) c :=
        HasDerivAt_sub (fun y => y) (fun _ => a) 1 0 c h_id h_const_a
      have h_sub_simp : (1 : Real) - 0 = 1 := sub_zero 1
      rw [h_sub_simp] at h_sub
      have h_const_fba : HasDerivAt (fun _ : Real => f b - f a) 0 c := HasDerivAt_const _ c
      have h_prod := HasDerivAt_mul (fun _ => f b - f a) (fun x => x - a) 0 1 c h_const_fba h_sub
      have h_simp : (0 : Real) * (c - a) + (f b - f a) * 1 = f b - f a := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [h_simp] at h_prod
      exact h_prod
    have h_g12 : HasDerivAt (fun x => (b - a) * f x - (b - a) * f a) ((b - a) * f'_c - 0) c :=
      HasDerivAt_sub _ _ _ _ c hg1 hg2
    exact HasDerivAt_sub _ _ _ _ c h_g12 hg3
  -- By HasDerivAt_unique: 0 = (b - a) * f'_c - 0 - (f b - f a).
  have h_eq : (0 : Real) = (b - a) * f'_c - 0 - (f b - f a) :=
    HasDerivAt_unique h 0 _ c h_zero h_derived
  -- Algebra: f b - f a = (b - a) * f'_c = f'_c * (b - a).
  have h_simp1 : (b - a) * f'_c - 0 - (f b - f a) = (b - a) * f'_c - (f b - f a) := by
    rw [sub_zero]
  rw [h_simp1] at h_eq
  -- From h_eq : 0 = (b - a) * f'_c - (f b - f a).
  -- Derive f b - f a = (b - a) * f'_c via the identity x = (x - y) + y,
  -- which after the substitution h_eq.symm becomes x = 0 + y = y.
  -- This avoids the prior session's mixed-form rewrite chain that
  -- failed on the sub_def vs post-sub_def pattern mismatch.
  have h_step : f b - f a = (b - a) * f'_c := by
    have h_sym : (b - a) * f'_c - (f b - f a) = 0 := h_eq.symm
    have h_id : (b - a) * f'_c
        = ((b - a) * f'_c - (f b - f a)) + (f b - f a) := by
      -- Use simp only for sub_def so the inner `(b - a)` subtraction isn't
      -- the only one touched — we need the outer `- (f b - f a)` rewritten too.
      simp only [sub_def]
      rw [add_assoc]
      have h_inv : -(f b + -f a) + (f b + -f a) = 0 := by
        rw [add_comm]; exact add_neg _
      rw [h_inv, add_zero]
    rw [h_sym, zero_add] at h_id
    exact h_id.symm
  have h_final : f b - f a = f'_c * (b - a) := by
    rw [h_step]; exact mul_comm (b - a) f'_c
  exact ⟨c, f'_c, hca, hcb, hf'_c, h_final⟩


/-! ## Zero count bound via Rolle's theorem -/

/-- **Zero count of f ≤ 1 + zero count of f'**, on a bounded open
interval `(a, b)`. Iterated Rolle gives this bound: if `f` has zeros
at `z_1 < z_2 < ... < z_N`, then by Rolle applied between consecutive
zeros, `f'` has zeros at `c_1 < c_2 < ... < c_{N-1}` (one between
each consecutive pair).

Axiomatized for Phase B. Provable from `rolle` plus list-manipulation
lemmas.

The statement: for any list `zeros_f` of zeros of `f` on `(a, b)`,
there exists a corresponding list of `zeros_f.length - 1` zeros of
the derivative `f'`. Equivalently, if `f'` has at most `N` zeros on
`(a, b)`, then `f` has at most `N + 1` zeros on `(a, b)`. -/
axiom zero_count_bound_by_deriv (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c)
    (N : Nat)
    (hf'_bound : ∀ zeros_f' : List Real,
        zeros_f'.Nodup →
        (∀ z ∈ zeros_f', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt f f'' z ∧ f'' = 0) →
        zeros_f'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f z = 0) →
      zeros_f.length ≤ N + 1

/-! ## Phase C plan (documented here as roadmap)

Phase C constructs the Pfaffian zero bound (Phase A's
`pfaffian_zero_count_bound`) via induction on Pfaffian chain order:

**Base case (order 0):** A Pfaffian function of order 0 is a
polynomial in x alone. Zero count ≤ degree, by
`PolynomialRootCount.lean` in MachLib.

**Inductive step:** A Pfaffian function `f` of order `n+1` has
derivative `f'` that, by the Pfaffian-chain-derivative axioms, is
ALSO Pfaffian of order ≤ `n+1` (the chain stays the same; only
the polynomial degree of f' in chain entries changes, bounded by
the original degree of f times the chain length).

Applying `zero_count_bound_by_deriv` (this file) + the inductive
hypothesis to f' gives a bound on the zero count of f.

Carrying out this induction explicitly yields a polynomial in
(order, degree) that matches Khovanskii's classical formula
`d · (d + 1)^{n-1}` or `2^{n(n-1)/2} · d^n`.

The induction proof is ~200-400 lines. Phase C is a 2-3 week focused
artifact.
-/

end Real
end MachLib
