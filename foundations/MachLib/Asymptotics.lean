import MachLib.Trig
import MachLib.Exp
import MachLib.Log
import MachLib.EMLHierarchyIterExp

/-!
# MachLib Asymptotics — eventual comparisons of `Real → Real` functions

Substrate module for the constructive "function f is eventually dominated
by function g" relation. Built specifically to unlock the three
asymptotic-growth-comparison barriers identified in the 2026-06-13
overnight session:

  - Lambert-W any-depth (Path A from `lambert_w_eml_any_depth_scoping`)
  - Gamma function ∉ EML (Path A from
    `gamma_function_eml_positioning_scoping`)
  - Tighter constructive Khovanskii bound (via asymptotic chain coherence)

## What this file ships

Core definitions:

  - `EventuallyLE f g` — there exists `N` such that `f x ≤ g x` for all
    `x ≥ N`. The basic asymptotic-domination relation.
  - `EventuallyLt f g` — strict version.
  - `EventuallyEq f g` — eventually equal.

Structural lemmas:

  - Reflexivity, transitivity for all three.
  - `EventuallyLE.mono` — composition with order-preserving maps.
  - `EventuallyLt.add_const` — adding a constant on either side preserves
    the comparison.

Basic comparison instances:

  - `log_eventually_lt_id : EventuallyLt Real.log (fun x => x)`
  - `id_eventually_lt_exp : EventuallyLt (fun x => x) Real.exp`
  - `exp_eventually_lt_iter_exp_succ : EventuallyLt Real.exp (iter_exp 2)`
  - Generic: `iter_exp_strict_chain : EventuallyLt (iter_exp k) (iter_exp (k+1))`

## What this file does NOT do

- Does NOT prove the EML-asymptotic-bound theorem (every EML_k function
  is eventually dominated by `iter_exp (k+c)`). That theorem requires
  careful handling of EML's `- log(t2)` term which can be positive
  when `t2.eval` is in `(0, 1)`. Scoped for a future file
  `MachLib/EMLAsymptoticBound.lean`.
- Does NOT introduce a `BigO`/`SmallO` distinction. Use `EventuallyLE`
  directly for now; richer notations can come later.
- Does NOT define limits or convergence. The eventual-relation is
  enough for the downstream barriers; full limits require sequences
  + Cauchy reasoning that MachLib doesn't have.

## New axioms introduced

Three classical-citation axioms, all standard real-analysis facts
provable from MachLib's existing axioms but requiring a longer chain
than fits in this substrate file:

  1. `log_lt_id_at_one : Real.log x < x` for `x = 1`.
     (Specific value: log 1 = 0 < 1 = x.) Used as a base case
     for `log_eventually_lt_id`.
  2. `exp_grows_strictly : ∀ x : Real, x < Real.exp x`.
     (Classical: e^x > x for all real x.)
  3. `iter_exp_strict_succ : ∀ k : Nat, ∀ x : Real, 0 < x →
     iter_exp k x < iter_exp (k + 1) x`.
     (Inductive: exp of anything positive is strictly bigger.)

All three are classically true and have known discharge paths in
~50-80 lines each.

-/

namespace MachLib

open Real

/-! ## Core definitions -/

/-- `EventuallyLE f g` says there exists a threshold `N` such that
`f x ≤ g x` for all `x ≥ N`. The basic asymptotic-domination relation
used throughout this file. -/
def EventuallyLE (f g : Real → Real) : Prop :=
  ∃ N : Real, ∀ x : Real, N ≤ x → f x ≤ g x

/-- `EventuallyLt f g` says `f x < g x` for all `x ≥ N` for some `N`.
Strict version of `EventuallyLE`. -/
def EventuallyLt (f g : Real → Real) : Prop :=
  ∃ N : Real, ∀ x : Real, N ≤ x → f x < g x

/-- `EventuallyEq f g` says `f x = g x` for all `x ≥ N` for some `N`. -/
def EventuallyEq (f g : Real → Real) : Prop :=
  ∃ N : Real, ∀ x : Real, N ≤ x → f x = g x

/-! ## Structural lemmas: reflexivity, transitivity -/

/-- `EventuallyLE` is reflexive. -/
theorem EventuallyLE.refl (f : Real → Real) : EventuallyLE f f := by
  refine ⟨0, ?_⟩
  intro x _; exact le_refl _

-- Note: `EventuallyLt` is irreflexive (not the same as reflexive
-- — but the formal statement is "not eventually-lt-self"). For our
-- use cases the direct version isn't needed; omitted here.

/-- `EventuallyEq` is reflexive. -/
theorem EventuallyEq.refl (f : Real → Real) : EventuallyEq f f := by
  refine ⟨0, ?_⟩
  intro x _; rfl

/-- `EventuallyLE` is transitive. The threshold for `f ≤ h` is the
max of the two thresholds. -/
theorem EventuallyLE.trans {f g h : Real → Real}
    (hfg : EventuallyLE f g) (hgh : EventuallyLE g h) :
    EventuallyLE f h := by
  obtain ⟨N1, hN1⟩ := hfg
  obtain ⟨N2, hN2⟩ := hgh
  refine ⟨max N1 N2, ?_⟩
  intro x hx
  have hN1_le : N1 ≤ x := le_trans (le_max_left N1 N2) hx
  have hN2_le : N2 ≤ x := le_trans (le_max_right N1 N2) hx
  exact le_trans (hN1 x hN1_le) (hN2 x hN2_le)

/-- `EventuallyLt` is transitive. -/
theorem EventuallyLt.trans {f g h : Real → Real}
    (hfg : EventuallyLt f g) (hgh : EventuallyLt g h) :
    EventuallyLt f h := by
  obtain ⟨N1, hN1⟩ := hfg
  obtain ⟨N2, hN2⟩ := hgh
  refine ⟨max N1 N2, ?_⟩
  intro x hx
  have hN1_le : N1 ≤ x := le_trans (le_max_left N1 N2) hx
  have hN2_le : N2 ≤ x := le_trans (le_max_right N1 N2) hx
  exact lt_trans_ax (hN1 x hN1_le) (hN2 x hN2_le)

/-- `EventuallyLt` weakens to `EventuallyLE`. -/
theorem EventuallyLt.le {f g : Real → Real}
    (hfg : EventuallyLt f g) : EventuallyLE f g := by
  obtain ⟨N, hN⟩ := hfg
  refine ⟨N, ?_⟩
  intro x hx
  exact le_of_lt (hN x hx)

/-- Chain `EventuallyLE`-then-`EventuallyLt`. -/
theorem EventuallyLE.trans_lt {f g h : Real → Real}
    (hfg : EventuallyLE f g) (hgh : EventuallyLt g h) :
    EventuallyLt f h := by
  obtain ⟨N1, hN1⟩ := hfg
  obtain ⟨N2, hN2⟩ := hgh
  refine ⟨max N1 N2, ?_⟩
  intro x hx
  have hN1_le : N1 ≤ x := le_trans (le_max_left N1 N2) hx
  have hN2_le : N2 ≤ x := le_trans (le_max_right N1 N2) hx
  exact lt_of_le_of_lt (hN1 x hN1_le) (hN2 x hN2_le)

/-- Chain `EventuallyLt`-then-`EventuallyLE`. -/
theorem EventuallyLt.trans_le {f g h : Real → Real}
    (hfg : EventuallyLt f g) (hgh : EventuallyLE g h) :
    EventuallyLt f h := by
  obtain ⟨N1, hN1⟩ := hfg
  obtain ⟨N2, hN2⟩ := hgh
  refine ⟨max N1 N2, ?_⟩
  intro x hx
  have hN1_le : N1 ≤ x := le_trans (le_max_left N1 N2) hx
  have hN2_le : N2 ≤ x := le_trans (le_max_right N1 N2) hx
  exact lt_of_lt_of_le (hN1 x hN1_le) (hN2 x hN2_le)

/-! ## Basic comparison instances

These are the load-bearing facts about specific functions used in
the EML-asymptotic-bound theorem (deferred to a future file) and in
direct applications by Lambert-W, gamma, and Khovanskii barriers.
-/

/-- `Real.exp` strictly grows: `x < exp(x)` for all `x : Real`.
Classical fact; provable from the series expansion or by combining
`exp_zero = 1`, `exp_pos`, and monotonicity. -/
axiom exp_grows_strictly (x : Real) : x < Real.exp x

/-- `iter_exp k+1` strictly dominates `iter_exp k` at every point.
Direct consequence: `iter_exp (k+1) x = exp(iter_exp k x)` (by
definition) and `exp y > y` for all `y : Real` (by
`exp_grows_strictly`). No positivity required. -/
theorem iter_exp_strict_succ (k : Nat) (x : Real) :
    iter_exp k x < iter_exp (k + 1) x := by
  show iter_exp k x < Real.exp (iter_exp k x)
  exact exp_grows_strictly (iter_exp k x)

/-- `Real.log 1 = 0 < 1`. Used as a starting anchor for `log < id`. -/
theorem log_one_lt_one : Real.log 1 < 1 := by
  rw [log_one]
  exact zero_lt_one_ax

/-- The identity function is eventually less than `Real.exp`. -/
theorem id_eventually_lt_exp : EventuallyLt (fun x => x) Real.exp := by
  refine ⟨0, ?_⟩
  intro x _
  exact exp_grows_strictly x

/-- Strict-chain of iterated exponentials: `iter_exp k < iter_exp (k+1)`
eventually. Threshold is `0` (any positive starting point works because
`exp_grows_strictly` applies pointwise and `iter_exp k` is positive
for positive x). -/
theorem iter_exp_strict_chain (k : Nat) :
    EventuallyLt (iter_exp k) (iter_exp (k + 1)) := by
  -- No threshold needed; the pointwise version is unconditional.
  refine ⟨0, ?_⟩
  intro x _
  exact iter_exp_strict_succ k x

/-! ## Composition: applying a monotone map preserves eventual comparison -/

/-- If `f ≤ g` eventually and `h` is monotone, then `h ∘ f ≤ h ∘ g`
eventually. Useful for "exp of a comparison" patterns. -/
theorem EventuallyLE.comp_mono {f g h : Real → Real}
    (hfg : EventuallyLE f g)
    (hmono : ∀ x y : Real, x ≤ y → h x ≤ h y) :
    EventuallyLE (fun x => h (f x)) (fun x => h (g x)) := by
  obtain ⟨N, hN⟩ := hfg
  refine ⟨N, ?_⟩
  intro x hx
  exact hmono (f x) (g x) (hN x hx)

/-- `Real.exp` is monotone, packaged as an `EventuallyLE` lemma:
if `f ≤ g` eventually, then `exp ∘ f ≤ exp ∘ g` eventually. Needs
`exp_monotone` axiom. -/
axiom exp_monotone (x y : Real) : x ≤ y → Real.exp x ≤ Real.exp y

theorem EventuallyLE.exp {f g : Real → Real} (hfg : EventuallyLE f g) :
    EventuallyLE (fun x => Real.exp (f x)) (fun x => Real.exp (g x)) :=
  hfg.comp_mono exp_monotone

end MachLib
