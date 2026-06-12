import MachLib.PfaffianChain
import MachLib.PolynomialRootCount
import MachLib.Rolle

/-!
# MachLib.PfaffianFnBound — the chain-length-induction Pfaffian bound

This module is the **phase-4 payoff** for the `derivative_rank_lt`
refactor (see `machlib/DERIVATIVE_RANK_LT_REFACTOR_PLAN.md`). The
goal: bound the number of zeros of a `PfaffianFn` on an interval
using induction on **chain length**, replacing the broken
strong-induction-on-derivative-rank strategy from
`KhovanskiiLemma.lean`.

## What's in this commit (phase 4 skeleton)

- The closed-form `khovanskiiBound n d`: a deliberately loose
  upper bound. Tight bounds belong in a future tightening pass.
- The bound theorem statement `pfaffian_fn_zero_count_bound`.
- The **base case** (chainLength = 0): the polynomial in x alone;
  invokes `PolynomialRootCount.poly_root_count_bound`.
- The **inductive step structure**: chain-length induction with
  a structured sorry, documented in detail. The classical Khovanskii
  reduction step (project to chain of length n - 1 by composing
  with the chain relation for y_n) is the multi-session piece
  remaining.

## Why this isn't the full closure

The classical Khovanskii bound proof for a chain of length n
requires bookkeeping the polynomial degree under repeated Rolle
applications mixed with chain-relation substitutions. The argument
is several pages in the published literature (Khovanskii 1991).
Formalizing it in MachLib's zero-Mathlib setting is its own
multi-session sub-project — but the *infrastructure* (PfaffianFn,
PfaffianChain, MultiPoly, lifts, combiners) is now in place to
support it.

The deletion of `derivative_rank_lt` happens **after** the full
inductive step is proven.

Zero Mathlib dependency. -/

namespace MachLib
namespace PfaffianFnBound

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-! ## The closed-form bound

A loose bound. The exact Khovanskii formula `B(n, α, β)` involves
the chain polynomial degrees `α_i` and the function degree `β`;
this simplification uses just `(n, total_degree)`. Tightening is a
future optimization pass; for derivative_rank_lt closure we only
need *some* bound that's provable. -/
def khovanskiiBound (n d : Nat) : Nat := (d + 1) ^ (n + 1)

/-! ## Base case: chainLength = 0 → polynomial in x -/

/-- Project a `MultiPoly n` to a single-variable `Poly` by treating
all chain variables as 0 (vacuous when `n = 0`; only meaningful with
the hypothesis `n = 0`). -/
noncomputable def multiPolyToPoly {n : Nat} : MultiPoly n → Poly
  | MultiPoly.const c   => Poly.const c
  | MultiPoly.varX      => Poly.var
  | MultiPoly.varY _    => Poly.const 0  -- vacuous case; n = 0 hypothesis used in eval
  | MultiPoly.add p q   => Poly.add (multiPolyToPoly p) (multiPolyToPoly q)
  | MultiPoly.sub p q   => Poly.sub (multiPolyToPoly p) (multiPolyToPoly q)
  | MultiPoly.mul p q   => Poly.mul (multiPolyToPoly p) (multiPolyToPoly q)

/-- Under `n = 0`, the Poly projection's eval matches the MultiPoly's. -/
theorem multiPolyToPoly_eval {n : Nat} (hn : n = 0) (p : MultiPoly n)
    (x : Real) (env : Fin n → Real) :
    Poly.eval (multiPolyToPoly p) x = MultiPoly.eval p x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i => exact absurd i.isLt (by omega)
  | add p q ihp ihq =>
    show Poly.eval (multiPolyToPoly p) x + Poly.eval (multiPolyToPoly q) x =
         MultiPoly.eval p x env + MultiPoly.eval q x env
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Poly.eval (multiPolyToPoly p) x - Poly.eval (multiPolyToPoly q) x =
         MultiPoly.eval p x env - MultiPoly.eval q x env
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Poly.eval (multiPolyToPoly p) x * Poly.eval (multiPolyToPoly q) x =
         MultiPoly.eval p x env * MultiPoly.eval q x env
    rw [ihp, ihq]

theorem degreeUpper_multiPolyToPoly_le {n : Nat} (p : MultiPoly n) :
    degreeUpper (multiPolyToPoly p) ≤ MultiPoly.totalDegree p := by
  induction p with
  | const c =>
    show 0 ≤ 0
    exact Nat.le_refl _
  | varX =>
    show 1 ≤ 1
    exact Nat.le_refl _
  | varY i =>
    show 0 ≤ 1
    exact Nat.zero_le _
  | add p q ihp ihq =>
    show Nat.max (degreeUpper (multiPolyToPoly p))
                  (degreeUpper (multiPolyToPoly q)) ≤
         Nat.max (MultiPoly.totalDegree p) (MultiPoly.totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.le_max_left _ _)
    · exact Nat.le_trans ihq (Nat.le_max_right _ _)
  | sub p q ihp ihq =>
    show Nat.max (degreeUpper (multiPolyToPoly p))
                  (degreeUpper (multiPolyToPoly q)) ≤
         Nat.max (MultiPoly.totalDegree p) (MultiPoly.totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.le_max_left _ _)
    · exact Nat.le_trans ihq (Nat.le_max_right _ _)
  | mul p q ihp ihq =>
    show degreeUpper (multiPolyToPoly p) + degreeUpper (multiPolyToPoly q) ≤
         MultiPoly.totalDegree p + MultiPoly.totalDegree q
    exact Nat.add_le_add ihp ihq

/-- **Base case of the bound theorem.** For a chain-length-0
PfaffianFn, the eval is a polynomial in x; bound via polynomial FTA. -/
theorem pfaffian_fn_bound_base
    (f : PfaffianFn) (hn : f.n = 0)
    (a b : Real) (hab : a < b)
    (hne_any : ∃ x : Real, f.eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ f.totalDegree := by
  -- Cast f.poly : MultiPoly f.n to MultiPoly 0 via hn, then convert to Poly.
  -- Simpler approach: work with the eval directly and bound via poly_root_count_bound.
  intro zeros hnodup hzeros
  -- Project f.poly to a single-variable Poly. The projection is valid
  -- because f.n = 0 means no chain variables actually appear.
  let p : Poly := multiPolyToPoly f.poly
  have hp_eval : ∀ x : Real, Poly.eval p x = f.eval x := by
    intro x
    show Poly.eval (multiPolyToPoly f.poly) x =
         MultiPoly.eval f.poly x (f.chain.chainValues x)
    exact multiPolyToPoly_eval hn f.poly x (f.chain.chainValues x)
  have hp_ne : ∃ x : Real, Poly.eval p x ≠ 0 := by
    obtain ⟨x, hx_ne⟩ := hne_any
    refine ⟨x, ?_⟩
    rw [hp_eval]
    exact hx_ne
  have hp_zeros : ∀ z ∈ zeros, a < z ∧ z < b ∧ Poly.eval p z = 0 := by
    intro z hz
    obtain ⟨ha, hb, heq⟩ := hzeros z hz
    refine ⟨ha, hb, ?_⟩
    rw [hp_eval]
    exact heq
  have hbound : zeros.length ≤ degreeUpper p :=
    poly_root_count_bound p a b hab hp_ne zeros hnodup hp_zeros
  have hdeg_le : degreeUpper p ≤ f.totalDegree :=
    degreeUpper_multiPolyToPoly_le f.poly
  exact Nat.le_trans hbound hdeg_le

/-! ## The bound theorem statement + inductive structure (skeleton)

The inductive step is structured but unproven — the classical
Khovanskii chain-projection argument is multi-session work. -/

/-- **The chain-length-induction Pfaffian zero bound.**

This is the bound that REPLACES the
`pfaffian_zero_count_bound_constructive` proof using the broken
`derivative_rank_lt`. Once the inductive step is proven, the old
`derivative_rank_lt` axiom can be deleted.

**Status:** base case proven, inductive step is documented sorry. -/
theorem pfaffian_fn_zero_count_bound (f : PfaffianFn) (a b : Real)
    (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (htriangular : f.chain.IsTriangular)
    (hne : ∃ x : Real, a < x ∧ x < b ∧ f.eval x ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ khovanskiiBound f.n f.totalDegree := by
  -- Induction on chain length f.n.
  intro zeros hnodup hzeros
  generalize hN_eq : f.n = N
  induction N with
  | zero =>
    -- Base case: chain length 0. Eval is a polynomial in x.
    have hne_any : ∃ x : Real, f.eval x ≠ 0 := by
      obtain ⟨x, _, _, hx_ne⟩ := hne
      exact ⟨x, hx_ne⟩
    have hbound := pfaffian_fn_bound_base f hN_eq a b hab hne_any
                      zeros hnodup hzeros
    -- hbound : zeros.length ≤ f.totalDegree
    -- Goal (after generalize):
    --   zeros.length ≤ khovanskiiBound 0 f.totalDegree
    --                = (f.totalDegree + 1)^1 = f.totalDegree + 1
    show zeros.length ≤ khovanskiiBound 0 f.totalDegree
    unfold khovanskiiBound
    show zeros.length ≤ (f.totalDegree + 1)^(0 + 1)
    have hp : (f.totalDegree + 1)^(0 + 1) = f.totalDegree + 1 := by
      show (f.totalDegree + 1) ^ 1 = f.totalDegree + 1
      exact Nat.pow_one _
    rw [hp]
    omega
  | succ N ih =>
    -- Inductive step: chain length n + 1. Reduce to chain length n
    -- via the classical Khovanskii projection.
    --
    -- **The argument (not yet formalized):**
    --
    -- Let y_{n+1} be the last chain variable. By triangularity, the
    -- relation P_{n+1}(x, y_1, ..., y_{n+1}) doesn't involve any y_j
    -- for j > n+1 (trivially, since there are none).
    --
    -- Consider f as a polynomial in y_{n+1} with coefficients that are
    -- polynomials in (x, y_1, ..., y_n). Use Rolle on f to bound its
    -- zeros by zeros of f' + 1. The derivative f' = ∂f/∂x +
    --   ∂f/∂y_{n+1} · y_{n+1}' = ∂f/∂x + ∂f/∂y_{n+1} · P_{n+1}.
    --
    -- The total degree of f' is bounded by (degree of f) + (degree of
    -- P_{n+1}). The degree in y_{n+1} is bounded but the x-degree
    -- decreases under the iterated Rolle.
    --
    -- After d_x applications of Rolle (where d_x is the x-degree of f),
    -- we reach a function whose x-degree is 0 — a polynomial in
    -- y_1, ..., y_{n+1} alone. We then "project out" y_{n+1} using
    -- the chain relation, reducing to chain length n, and apply IH.
    --
    -- **Bookkeeping needed:** track degree growth at each Rolle step,
    -- prove the chain-relation substitution is degree-preserving in
    -- a specific sense, bound the total error. ~250-400 lines.
    --
    -- For now: structured sorry. The proof structure is clear; the
    -- formalization is multi-session.
    sorry

end PfaffianFnBound
end MachLib
