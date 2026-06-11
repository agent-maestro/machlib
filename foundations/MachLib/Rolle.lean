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

/-! ## Mean Value Theorem (consequence of Rolle) -/

/-- **Mean Value Theorem.** If `f` is differentiable on `(a, b)`, there
exists `c ∈ (a, b)` and `f' : Real` such that `HasDerivAt f f' c`
and `f b - f a = f' * (b - a)`.

**Provable from Rolle.** Define `h(x) := (b - a) * f(x) - (b - a) *
f(a) - (f(b) - f(a)) * (x - a)`. Then `h a = h b = 0` via algebra,
and `h` is differentiable. Apply Rolle to `h` to get
`(b - a) * f'(c) = f(b) - f(a)`.

The constructive proof is ~80 lines but bumps against algebraic
manipulation that requires AC-stronger tactics than MachLib's
`mach_ring` currently provides. Deferred — meanwhile axiomatized
to unblock downstream MVT consumers. -/
axiom mean_value_theorem (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, ∃ f' : Real, a < c ∧ c < b ∧ HasDerivAt f f' c ∧
      f b - f a = f' * (b - a)

/-! ## (Constructive MVT proof attempt — DEFERRED)

The body below is left as a documented skeleton for the constructive
proof. Each `_` marks where ~10-20 lines of dense algebraic
manipulation are needed (sub_def + add_comm + add_assoc + add_neg
+ ...). MachLib's `mach_ring` Phase 2 leaves residue on these
expansions. A focused 1-session artifact with a stronger AC tactic
(or careful manual chains) completes the proof.

```
example (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, ∃ f' : Real, a < c ∧ c < b ∧ HasDerivAt f f' c ∧
      f b - f a = f' * (b - a) := by
  -- Define the auxiliary function h(x) = (b-a) * f(x) - (b-a) * f(a) - (f(b) - f(a)) * (x - a).
  let h : Real → Real := fun x =>
    (b - a) * f x - (b - a) * f a - (f b - f a) * (x - a)
  -- Show h a = h b.
  have hfa_eq_fb : h a = h b := by
    show (b - a) * f a - (b - a) * f a - (f b - f a) * (a - a) =
         (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    rw [sub_self a]
    show (b - a) * f a - (b - a) * f a - (f b - f a) * 0 =
         (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    rw [mul_zero, sub_zero]
    -- Goal: (b - a) * f a - (b - a) * f a = (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a).
    -- LHS = 0. RHS = (b-a)(f b - f a) - (f b - f a)(b - a) = 0.
    have hlhs : (b - a) * f a - (b - a) * f a = 0 := sub_self _
    rw [hlhs]
    -- Goal: 0 = (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a).
    -- Show via algebraic identity: (b-a)(f b) - (b-a)(f a) - (f b - f a)(b-a) = 0.
    have hidentity : (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a) = 0 := by
      mach_ring
    rw [hidentity]
  -- Show h is differentiable on (a, b) with derivative h'(x) = (b-a) f'(x) - (f b - f a).
  have h_diff : ∀ c : Real, a < c → c < b →
      ∃ h' : Real, HasDerivAt h h' c := by
    intro c hca hcb
    obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
    -- Compute h's derivative at c.
    -- h(x) = (b - a) * f x - (b - a) * f a - (f b - f a) * (x - a).
    -- Let g1(x) = (b - a) * f x. g1'(c) = (b-a) * f'_c (via HasDerivAt_mul + const).
    -- Let g2(x) = (b - a) * f a (constant). g2'(c) = 0.
    -- Let g3(x) = (f b - f a) * (x - a). g3'(c) = f b - f a (via HasDerivAt_mul + id-sub-const).
    -- h(x) = g1(x) - g2(x) - g3(x). h'(c) = g1'(c) - g2'(c) - g3'(c) = (b-a) * f'_c - 0 - (f b - f a).
    have hg1 : HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c := by
      have h_const : HasDerivAt (fun _ : Real => b - a) 0 c := HasDerivAt_const (b - a) c
      have h_prod := HasDerivAt_mul (fun _ => b - a) f 0 f'_c c h_const hf'_c
      -- h_prod : HasDerivAt (fun y => (fun _ => b - a) y * f y) (0 * f c + (b - a) * f'_c) c.
      -- Need: HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c.
      -- Simplify 0 * f c = 0; 0 + (b - a) * f'_c = (b - a) * f'_c.
      have h_simp : (0 : Real) * f c + (b - a) * f'_c = (b - a) * f'_c := by
        rw [zero_mul, zero_add]
      rw [h_simp] at h_prod
      exact h_prod
    have hg2 : HasDerivAt (fun _ : Real => (b - a) * f a) 0 c :=
      HasDerivAt_const _ c
    have hg3 : HasDerivAt (fun x => (f b - f a) * (x - a)) (f b - f a) c := by
      -- (x - a) has derivative 1.
      have h_id : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
      have h_const_a : HasDerivAt (fun _ : Real => a) 0 c := HasDerivAt_const a c
      have h_sub : HasDerivAt (fun y => y - a) (1 - 0) c :=
        HasDerivAt_sub (fun y => y) (fun _ => a) 1 0 c h_id h_const_a
      have h_sub_simp : (1 : Real) - 0 = 1 := sub_zero 1
      rw [h_sub_simp] at h_sub
      have h_const_fba : HasDerivAt (fun _ : Real => f b - f a) 0 c := HasDerivAt_const _ c
      have h_prod := HasDerivAt_mul (fun _ => f b - f a) (fun x => x - a) 0 1 c h_const_fba h_sub
      -- h_prod : HasDerivAt (fun y => (fun _ => f b - f a) y * ((fun x => x - a) y)) (0 * (c - a) + (f b - f a) * 1) c.
      have h_simp : (0 : Real) * (c - a) + (f b - f a) * 1 = f b - f a := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [h_simp] at h_prod
      exact h_prod
    -- h = g1 - g2 - g3.
    have h_g12 : HasDerivAt (fun x => (b - a) * f x - (b - a) * f a) ((b - a) * f'_c - 0) c :=
      HasDerivAt_sub _ _ _ _ c hg1 hg2
    have h_full : HasDerivAt h ((b - a) * f'_c - 0 - (f b - f a)) c :=
      HasDerivAt_sub _ _ _ _ c h_g12 hg3
    refine ⟨(b - a) * f'_c - 0 - (f b - f a), h_full⟩
  -- Apply Rolle to h.
  obtain ⟨c, hca, hcb, h_zero⟩ := rolle h a b hab hfa_eq_fb h_diff
  -- h_zero : HasDerivAt h 0 c.
  -- From the h_diff construction, the derivative we constructed at c was (b - a) * f' - 0 - (f b - f a)
  -- where f' is the derivative of f at c (from hdiff).
  obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
  -- We need: (b - a) * f'_c - 0 - (f b - f a) = 0, then f b - f a = (b - a) * f'_c = f'_c * (b - a).
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
  -- By HasDerivAt_unique, the two derivatives of h at c match: 0 = (b - a) * f'_c - 0 - (f b - f a).
  have h_eq : (0 : Real) = (b - a) * f'_c - 0 - (f b - f a) :=
    HasDerivAt_unique h 0 _ c h_zero h_derived
  -- Solve for f b - f a = (b - a) * f'_c = f'_c * (b - a).
  -- 0 = (b-a) * f'_c - 0 - (f b - f a) = (b-a) * f'_c - (f b - f a) (using sub_zero).
  -- So f b - f a = (b - a) * f'_c.
  have h_simp1 : (b - a) * f'_c - 0 - (f b - f a) = (b - a) * f'_c - (f b - f a) := by
    rw [sub_zero]
  rw [h_simp1] at h_eq
  -- h_eq : 0 = (b - a) * f'_c - (f b - f a).
  -- Add (f b - f a) to both sides: f b - f a = (b - a) * f'_c.
  have h_step : (f b - f a) = (b - a) * f'_c := by
    -- 0 = (b - a) * f'_c - (f b - f a), so f b - f a = (b - a) * f'_c.
    have step : (f b - f a) + 0 = (f b - f a) + ((b - a) * f'_c - (f b - f a)) := by rw [h_eq]
    -- Simplify LHS via add_zero.
    -- Simplify RHS via: (f b - f a) + ((b - a) * f'_c + -(f b - f a))
    --                 = ((f b - f a) + -(f b - f a)) + (b - a) * f'_c (rearrange)
    --                 = 0 + (b - a) * f'_c
    --                 = (b - a) * f'_c.
    rw [add_zero, sub_def, ← add_assoc, add_comm (f b - f a) ((b - a) * f'_c),
        add_assoc ((b - a) * f'_c) (f b - f a) (-(f b - f a)), add_neg,
        add_zero] at step
    exact step
  -- Convert to f'_c * (b - a).
  have h_final : f b - f a = f'_c * (b - a) := by
    rw [h_step]; exact mul_comm (b - a) f'_c
  exact ⟨c, f'_c, hca, hcb, hf'_c, h_final⟩
```
-/

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
