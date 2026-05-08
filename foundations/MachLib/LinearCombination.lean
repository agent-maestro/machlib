/-
MachLib.LinearCombination — `mach_linear_combination` tactic for
hypothesis-driven polynomial identities.

This is MachLib's pragmatic substitute for Mathlib's
`linear_combination`. The v1 implementation handles the canonical
Forge-emitted shape:

  Given a hypothesis `h : LHS = RHS` (typically the Pythagorean
  identity `sin x * sin x + cos x * cos x = 1` or a user-supplied
  algebraic fact), close a goal of the form `expr = expr'` where
  the goal is structurally `RHS - LHS` after rearrangement.

The cleanest entry shape:

    theorem foo (...) : a*a + b*b - 1 = 0 := by
      have h := pythagorean θ   -- sin² + cos² = 1
      mach_linear_combination h

The tactic rewrites the goal using `h` (treating `h` as a
substitution rule) and then attempts `mach_ring` to close any
residual polynomial identity.

In scope (v1)
-------------
  * Single-hypothesis substitution: `mach_linear_combination h`
    where `h : LHS = RHS` rewrites the goal LHS-for-RHS (or
    vice-versa) and dispatches to `mach_ring`.

Out of scope (v2 / future)
--------------------------
  * Coefficient-weighted combinations
    (`linear_combination 2 * h₁ - 3 * h₂` style)
  * Auto-discovery of which hypothesis to use
  * Genuine `linear_combination` parsing (the comma-separated
    coefficient * hypothesis syntax)

Coverage
--------
The Mat4 / Sphere / Cylinder / Torus orthonormal-witness cluster
uses `pythagorean` as the only hypothesis; `linear_combination`
v1 is sufficient there. The Quat from_rotation_z norm-witness is
also single-hypothesis. The cross-product Lagrange identity has
no usable hypothesis source — that's ring v2 territory.
-/

import MachLib.Basic
import MachLib.Trig
import MachLib.Forge
import MachLib.Ring

namespace MachLib
namespace Real

/-! ### `mach_linear_combination` tactic

Takes a hypothesis term and rewrites the goal using it (in either
direction), then closes by `mach_ring`. The `try rw [← h]` after
`try rw [h]` handles the case where the hypothesis needs to be
applied right-to-left for the rewrite to fire. -/

syntax (name := machLinearCombination)
  "mach_linear_combination" term : tactic

macro_rules
  | `(tactic| mach_linear_combination $h:term) => `(tactic|
      (-- Step 1: expand `let` bindings AND normalise the goal
       -- with the same lemma set `mach_ring` uses (zero / one
       -- collapse + distributivity + negation-multiplication).
       -- This puts the goal in a polynomial canonical form so the
       -- forward rewrite of `h` can see its pattern even when
       -- the engine's kernel uses `(a+b)*c` or `-K*x*x` shapes.
       try simp (config := { zeta := true }) only [
         one_mul_thm, mul_one_ax,
         zero_mul, mul_zero,
         zero_add, add_zero,
         neg_mul, mul_neg, neg_mul_neg, neg_neg_helper,
         mul_distrib, mul_distrib_right
       ]
       -- Step 2: rewrite the goal using the hypothesis.
       rw [$h:term]
       -- Step 3: close any residual polynomial identity.
       mach_ring))

end Real
end MachLib
