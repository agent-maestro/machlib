import MachLib.PfaffianChain
import MachLib.PolynomialRootCount
import MachLib.Rolle
import MachLib.KhovanskiiReduction

/-!
# MachLib.PfaffianFnBound — the chain-length-induction Pfaffian bound

This module bounds the number of zeros of a `PfaffianFn` on an
interval using induction on **chain length**, replacing the broken
strong-induction-on-derivative-rank strategy from `KhovanskiiLemma.lean`.

## What's in this module

- The closed-form `khovanskiiBound n d`: a deliberately loose
  upper bound. Tight bounds belong in a future tightening pass.
- The **base case** (chainLength = 0): the polynomial in x alone;
  invokes `PolynomialRootCount.poly_root_count_bound`.
- The bound theorem `pfaffian_fn_zero_count_bound`: a thin wrapper
  around `KhovanskiiReduction.khovanskii_bound_full` that takes a
  reduction witness (`IsKhovanskiiReducible`) and produces the
  closed-form bound.

## Phase-15 axiom audit retirement

The previous version of this module declared `khovanskii_chain_step`
as a classical-citation axiom encoding "the constructive Khovanskii
chain-step bound exists for any triangular PfaffianFn". When
`KhovanskiiReduction.khovanskii_bound_full` shipped (constructive
modulo a reduction witness), the axiom became redundant for any
caller able to supply a witness. The current signature exposes
the witness as a hypothesis, eliminating the classical axiom.

For callers without a hand-constructed witness: Step 3 of the
Khovanskii sprint (the general witness construction via the lex
measure `(degreeY_last, degreeX leadingCoeff)`) remains the open
multi-session piece. For SingleExpChain, the auto-witness via
`SingleExpKhovanskii.simplifiedScaledReduction` is shipped.

Zero Mathlib dependency. Zero classical axioms. -/

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

/-! ## The bound theorem — thin wrapper around `khovanskii_bound_full`

For chain length 0, the base case (a univariate polynomial) bounds via
the FTA. For chain length > 0, the caller supplies a reduction witness
(`IsKhovanskiiReducible f g k` with `g.n = 0`); the wrapper combines
the witness with `khovanskii_bound_full` to produce the closed-form
bound.

The witness-required signature is the price of retiring the
`khovanskii_chain_step` classical axiom. For callers using
SingleExpChain, the auto-witness in `SingleExpKhovanskii` discharges
this hypothesis. For general triangular chains, Step 3 (the lex-measure
termination argument) remains open. -/

/-- **The chain-length-induction Pfaffian zero bound.**

For chainLength = 0: direct from the base case (polynomial FTA).

For chainLength > 0: takes a reduction witness `h_iter` showing
f reduces via interleaved scaledReduction + dropLast steps to a
chain-length-0 g, and bounds f's zeros via g's zeros + the Rolle
counter k. -/
theorem pfaffian_fn_zero_count_bound (f : PfaffianFn) (a b : Real)
    (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (htriangular : f.chain.IsTriangular)
    (g : PfaffianFn) (k : Nat)
    (h_iter : f.IsKhovanskiiReducible g k)
    (hg0 : g.n = 0)
    (hne_g : ∃ x : Real, g.eval x ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ MultiPoly.degreeX g.poly + k :=
  PfaffianFn.khovanskii_bound_full f g k h_iter htriangular hg0 a b hab
    hcoherent hne_g

end PfaffianFnBound
end MachLib
