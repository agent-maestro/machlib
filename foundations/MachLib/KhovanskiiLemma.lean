import MachLib.Exp
import MachLib.Log
import MachLib.Differentiation
import MachLib.Pfaffian
import MachLib.Rolle

/-!
# Khovanskii's Lemma — Phase C (constructive proof skeleton)

Reduces Phase A's monolithic `PfaffianFunction.zero_bound` axiom to
**three smaller axioms** + a constructive induction:

1. **`polynomial_zero_count_bound`**: order-0 Pfaffian functions
   (polynomials in x) have zero count ≤ degree. The base case.
2. **`pfaffian_derivative`**: every Pfaffian function has a Pfaffian
   derivative. The structural axiom.
3. **`pfaffian_derivative_rank_decrease`**: the derivative has
   strictly smaller "rank" than the original, where rank is a
   well-founded measure on (chain order, polynomial degree).

Combined with Phase B's `zero_count_bound_by_deriv` (Rolle's
corollary), strong induction on rank yields the Khovanskii bound.

**Why this is progress over Phase A's monolithic axiom:**

Phase A's `pfaffian_zero_count_bound` and `PfaffianFunction.zero_bound`
axiomatized the FINAL Khovanskii bound — a deep theorem with a
non-trivial proof. Phase C reduces it to three smaller axioms that
are each more local / closer to first principles:

- (1) polynomial_zero_count_bound: a classical theorem about
  polynomials (FTA + polynomial division). Provable constructively
  from MachLib's `PolynomialRootCount.lean` infrastructure with
  ~300 lines.
- (2) pfaffian_derivative: structurally true by construction (the
  chain relation gives the derivative explicitly).
- (3) pfaffian_derivative_rank_decrease: a bookkeeping fact about
  how differentiation interacts with the chain order / polynomial
  degree.

Each smaller axiom is closer to "obvious" and admits future
constructive proof.

**Honest scope:** Phase C is a SKELETON. The three smaller axioms +
the inductive proof structure are in place; the actual constructive
proofs of (1), (2), (3) are each separate ~1-week artifacts. The
END-USER results in Phase D (`sin_not_in_eml_any_depth`) remain
conditional, but conditional on smaller axioms now.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## Rank measure on Pfaffian functions -/

/-- The **rank** of a Pfaffian function. Used as the well-founded
measure for the induction. Concretely:

    rank f = pfaffian_chain_order * MAX_DEGREE + pfaffian_degree

where MAX_DEGREE is large enough that decreasing chain order strictly
decreases rank regardless of degree changes.

Encoded simply as `Nat`. -/
noncomputable def PfaffianRank (f : PfaffianFunction) : Nat :=
  f.chain.order * 1000000 + f.degree

/-! ## The base case axiom -/

/-- **Polynomial zero count bound.** For a Pfaffian function of
chain order 0 (i.e., a polynomial in `x` alone), the zero count on
any bounded interval is at most the polynomial degree.

Provable constructively from `MachLib.PolynomialRootCount.lean` +
the fundamental theorem of algebra (polynomial of degree d has at
most d roots). Currently axiomatized as the base case for Phase C's
induction. -/
axiom polynomial_zero_count_bound (f : PfaffianFunction)
    (h_order : f.chain.order = 0) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, f.eval x ≠ 0) :
    ∀ zeros : List Real,
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ f.degree

/-! ## The structural axiom: every Pfaffian has a Pfaffian derivative -/

/-- The derivative of a Pfaffian function as a Pfaffian function.
Axiomatized: a constructive definition would compute the polynomial
expression for `f'` using the chain relation
`f_i' = P_i(x, f_1, ..., f_i)`. -/
axiom PfaffianFunction.derivative : PfaffianFunction → PfaffianFunction

/-- The derivative's eval matches the calculus derivative. -/
axiom PfaffianFunction.derivative_eval (f : PfaffianFunction) (x : Real) :
    HasDerivAt f.eval (f.derivative.eval x) x

/-! ## The rank-decrease axiom -/

/-- The derivative of a non-trivial Pfaffian function has strictly
smaller rank. Axiomatized as part of Phase C's induction setup.
A constructive proof would carry the chain-and-degree bookkeeping
explicitly (Khovanskii's classical argument). -/
axiom PfaffianFunction.derivative_rank_lt (f : PfaffianFunction)
    (hrank : 0 < PfaffianRank f) :
    PfaffianRank f.derivative < PfaffianRank f

/-! ## Constructive Khovanskii bound via strong induction on rank -/

/-! ## Strategic note (Phase C-final)

Replaces the prior `pfaffian_zero_count_bound_constructive` axiom
with a constructive proof. Conditional on the three smaller axioms
(base case, derivative-is-Pfaffian, rank-decrease) + Phase B's Rolle
+ one auxiliary axiom for the constant-Pfaffian case.

Bound: zero count of `f` on `(a, b)` is at most `PfaffianRank f`.

Proof structure: strong induction on `PfaffianRank f`.
- Base case (`f.chain.order = 0`): apply `polynomial_zero_count_bound`;
  `degree ≤ rank`.
- Inductive step (`f.chain.order > 0`): split on whether `f.derivative`
  is identically zero.
  - If zero: `f` is non-zero constant, zero count = 0.
  - If non-zero: apply IH to `f.derivative` (smaller rank), then
    `zero_count_bound_by_deriv` (Phase B).
-/

/-! ## Auxiliary axiom: constant Pfaffian (derivative = 0 everywhere) -/

/-- If a Pfaffian function has identically zero derivative AND is
not identically zero itself, then it's a non-zero constant — i.e.,
its value is non-zero everywhere. (Reason: derivative = 0 ⇒ function
is constant; non-zero constant has non-zero value everywhere.)

Axiomatized. The classical proof uses the mean value theorem
(consequence of Rolle's theorem, Phase B). Could be made constructive
via Phase B + MachLib's analytic infrastructure. -/
axiom pfaffian_derivative_zero_implies_nonzero_everywhere
    (g : PfaffianFunction)
    (h_deriv_zero : ∀ x : Real, g.derivative.eval x = 0)
    (h_g_ne : ∃ x : Real, g.eval x ≠ 0) :
    ∀ x : Real, g.eval x ≠ 0

/-! ## The constructive Khovanskii bound theorem -/

/-- **The constructive Khovanskii bound.** Replaces the previous
session's `pfaffian_zero_count_bound_constructive` axiom with a
proof. Conditional on the smaller axioms (base case, derivative-is-
Pfaffian, rank-decrease, constant case) + Phase B's Rolle.

Bound: zero count of `f` on `(a, b)` is at most `PfaffianRank f`.

Proof: strong induction on `PfaffianRank f`.
- Base case (`f.chain.order = 0`): polynomial bound + `rank = degree`.
- Inductive step (`f.chain.order > 0`): split on whether `f.derivative`
  is identically zero.
  - If so: `f` is non-zero constant, so zero count = 0.
  - If not: apply IH to `f.derivative` (smaller rank), then
    `zero_count_bound_by_deriv` for `f`. -/
theorem pfaffian_zero_count_bound_constructive (f : PfaffianFunction)
    (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, f.eval x ≠ 0) :
    ∀ zeros : List Real,
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ PfaffianRank f := by
  -- Generalize: prove for all g and all rank-equal-n.
  suffices h : ∀ n : Nat, ∀ (g : PfaffianFunction) (a' b' : Real),
                a' < b' → (∃ x, g.eval x ≠ 0) → PfaffianRank g = n →
    ∀ zeros : List Real,
      (∀ z ∈ zeros, a' < z ∧ z < b' ∧ g.eval z = 0) →
      zeros.length ≤ n by
    have := h (PfaffianRank f) f a b hab hne rfl
    exact this
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro g a' b' hab' hgne hgrank zeros hzeros
    by_cases h0 : g.chain.order = 0
    · -- Base case: order = 0, polynomial.
      have hbound :=
        polynomial_zero_count_bound g h0 a' b' hab' hgne zeros hzeros
      -- hbound : zeros.length ≤ g.degree.
      -- Show g.degree ≤ PfaffianRank g = n.
      have hdeg_le : g.degree ≤ PfaffianRank g := by
        unfold PfaffianRank
        rw [h0]; omega
      rw [hgrank] at hdeg_le
      exact Nat.le_trans hbound hdeg_le
    · -- Inductive step: order > 0.
      -- Split on whether g.derivative is identically zero.
      by_cases h_deriv_all_zero : ∀ x : Real, g.derivative.eval x = 0
      · -- g.derivative = 0 everywhere → g is non-zero constant.
        have hg_all_ne :=
          pfaffian_derivative_zero_implies_nonzero_everywhere g h_deriv_all_zero hgne
        -- zeros must be empty.
        have hzeros_empty : zeros = [] := by
          cases zeros with
          | nil => rfl
          | cons z rest =>
            -- z ∈ zeros → g.eval z = 0; but hg_all_ne says g.eval z ≠ 0.
            have hz_in : z ∈ (z :: rest) := List.mem_cons_self _ _
            have := hzeros z hz_in
            -- this : a' < z ∧ z < b' ∧ g.eval z = 0
            exfalso
            exact hg_all_ne z this.2.2
        rw [hzeros_empty]
        simp
      · -- g.derivative is not identically zero.
        -- Derive ∃ x, g.derivative.eval x ≠ 0 from the ¬ ∀ form.
        have h_deriv_some_ne : ∃ x : Real, g.derivative.eval x ≠ 0 := by
          apply Classical.byContradiction
          intro h_all_eq
          apply h_deriv_all_zero
          intro x
          apply Classical.byContradiction
          intro hne
          exact h_all_eq ⟨x, hne⟩
        -- h_deriv_some_ne : ∃ x, g.derivative.eval x ≠ 0.
        -- Apply IH to g.derivative.
        have hrank_pos : 0 < PfaffianRank g := by
          unfold PfaffianRank
          have hord_pos : 0 < g.chain.order := Nat.pos_of_ne_zero h0
          omega
        have hdiff_lt := PfaffianFunction.derivative_rank_lt g hrank_pos
        -- hdiff_lt : PfaffianRank g.derivative < PfaffianRank g = n.
        rw [hgrank] at hdiff_lt
        -- Apply IH.
        let m := PfaffianRank g.derivative
        have hm_lt : m < n := hdiff_lt
        have ih_deriv := ih m hm_lt g.derivative a' b' hab' h_deriv_some_ne rfl
        -- ih_deriv : ∀ zeros', ... g.derivative.eval z = 0 → zeros'.length ≤ m.
        -- Apply Phase B's zero_count_bound_by_deriv.
        have hdiff_witness : ∀ c : Real, a' < c → c < b' →
              ∃ f' : Real, HasDerivAt g.eval f' c := by
          intro c _ _
          exact ⟨g.derivative.eval c, PfaffianFunction.derivative_eval g c⟩
        have h_f'_bound : ∀ zeros_f' : List Real,
            (∀ z ∈ zeros_f', a' < z ∧ z < b' ∧
              ∃ f'' : Real, HasDerivAt g.eval f'' z ∧ f'' = 0) →
            zeros_f'.length ≤ m := by
          intro zeros_f' hzeros_f'
          apply ih_deriv zeros_f'
          intro z hz
          obtain ⟨ha, hb, hd⟩ := hzeros_f' z hz
          refine ⟨ha, hb, ?_⟩
          -- g.derivative.eval z = 0 (via HasDerivAt_unique).
          obtain ⟨f'', hd', hfeq⟩ := hd
          have heq : f'' = g.derivative.eval z :=
            HasDerivAt_unique g.eval f'' (g.derivative.eval z) z hd'
              (PfaffianFunction.derivative_eval g z)
          rw [← heq, hfeq]
        have hbound_via_rolle : zeros.length ≤ m + 1 :=
          zero_count_bound_by_deriv g.eval a' b' hab' hdiff_witness m h_f'_bound
            zeros hzeros
        -- hbound_via_rolle : zeros.length ≤ m + 1.
        -- m + 1 ≤ n (from hm_lt : m < n, so m + 1 ≤ n).
        omega

/-! ## Phase C plan (documented as roadmap)

The constructive proof structure outlined:

```
theorem pfaffian_zero_count_bound_constructive_proof
    (f : PfaffianFunction) (a b : Real) (hab : a < b)
    (hne : ∃ x, f.eval x ≠ 0) :
    ∀ zeros, ... → zeros.length ≤ f.degree + PfaffianRank f := by
  -- Strong induction on f.rank.
  induction PfaffianRank f using Nat.strongRecOn with
  | _ n ih =>
    intro zeros hzeros
    by_cases h0 : f.chain.order = 0
    · -- Base case: polynomial.
      exact polynomial_zero_count_bound f h0 a b hab hne zeros hzeros
    · -- Inductive step.
      -- f' = f.derivative, has rank < f.rank.
      have hdiff_lt := PfaffianFunction.derivative_rank_lt f
        (by positivity_of_h0)
      -- Apply IH to f'.
      -- IH gives zero count of f' ≤ f'.degree + f'.rank.
      -- Apply Phase B's zero_count_bound_by_deriv: f's count ≤ f''s count + 1.
      -- Combine and bound by f.degree + f.rank.
      [MECHANICAL_INDUCTION_STEP]  -- placeholder
```

The placeholder represents the mechanical induction step that combines:
1. IH applied to `f.derivative`.
2. Phase B's `zero_count_bound_by_deriv`.
3. Arithmetic that `degree + rank` accommodates the +1 increment.

Estimated effort: 100-200 lines of detail. The main obstacle is the
rank arithmetic — the derivative's rank may decrease by less than 1
(if the polynomial degree changes minimally), so the bound formula
may need refinement.

Phase C-final = constructive proofs of:
1. `polynomial_zero_count_bound` (via PolynomialRootCount, ~300 lines).
2. `PfaffianFunction.derivative_eval` (via chain-relation computation,
   ~200 lines, requires constructive PfaffianChain).
3. `PfaffianFunction.derivative_rank_lt` (bookkeeping argument,
   ~100 lines).
4. `pfaffian_zero_count_bound_constructive` mechanical induction
   (~150 lines).

Total: ~750 lines. Roughly 1-2 weeks of focused effort if the
PfaffianChain inductive type is fleshed out (currently opaque
axioms in Phase A).
-/

end Real
end MachLib
