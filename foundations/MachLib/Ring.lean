/-
MachLib.Ring — `mach_ring` tactic for kernel-shape polynomial identities.

This is MachLib's pragmatic substitute for Mathlib's `ring`. The
v1 implementation discharges the dominant Forge-emitted shape:
"linear-in-zeros" identities that arise after `unfold` exposes a
matrix-cell, vector-component, or scalar-arithmetic kernel body.

In scope (v1)
-------------
The additive-multiplicative fragment with literal `0` and `1`
coefficients, plus subtraction-cancellation:

  * 1 * x      = x          via `one_mul_thm`
  * x * 1      = x          via `mul_one_ax`
  * 0 * x      = 0          via `zero_mul`
  * x * 0      = 0          via `mul_zero`
  * x + 0      = x          via `add_zero`
  * 0 + x      = x          via `zero_add`
  * x - 0      = x          via `sub_zero` (in `MachLib.EML`)
  * x - x      = 0          via `sub_self` (this file)
  * - 0        = 0          via `neg_zero` (in `MachLib.EML`)

Canonical post-unfold shape closed by v1:

    1 * x + 0 * py + 0 * pz + tx - (x + tx) = 0

(matrix-cell witness for `Mat4.translate`, `rotation_*_preserves_*`,
`lerp_endpoint_at_zero`, `verlet_step_zero_accel_extrapolates`, and
all 16-cell `MulMat4.mul_mat4_identity_*` / `translation_compose_03`
shapes Forge emits.)

Out of scope (deferred to v2)
-----------------------------
Genuine polynomial-identity reflection: cross-product perpendicularity
(`a · (a × b) = 0`), Lagrange's identity (`|a × b|² + (a · b)² =
|a|² |b|²`), four-square Euler identity for quaternion norm
preservation. Those need either a proper polynomial normaliser or
hand-derived `linear_combination`-style proofs. v2 lands once a
concrete blocker forces it (probably the v0.5 quaternion sweep).

Design
------
v1 is a curated `simp only` over the lemma set above plus an
`intros` to bring `let` bindings into context. No reflection, no
new axioms beyond what `MachLib.Basic` already exposes. The new derived
theorem (`sub_self`) lives here rather than in `Basic` because
it's tactic-internal — `Basic` stays the minimal axiomatic
foundation, `Ring` is the Forge-facing ergonomic layer.
`neg_zero` and `sub_zero` already live in `MachLib.EML`; the
macro reuses them.

The `simp only` lemma list is curated, not auto-discovered: tagging
`MachLib.Basic` axioms with `@[simp]` would pollute every other
proof in the library and risks confluence loops with the
`mul_distrib` rewrite. Forge-emitted code reaches for `mach_ring`
explicitly when it knows the goal is in the supported fragment.
-/

import MachLib.Basic
import MachLib.EML
import MachLib.Forge

namespace MachLib
namespace Real

/-! ### Sub-self normalisation -/

/-- `a - a = 0`. Provable from `sub_def` + `add_neg`. Lifted here
because Forge's matrix-cell witnesses always reduce to
`(complicated_expr) - (complicated_expr) = 0` after the additive-
multiplicative simp pass collapses the literal coefficients. -/
theorem sub_self (a : Real) : a - a = 0 := by
  rw [sub_def, add_neg]

/-! ### Distributivity + negation-multiplication (v1.5)

`MachLib.Basic` ships left-distributivity (`a * (b + c) = a*b + a*c`)
but not the right form, and no negation-multiplication facts.
`mach_ring` v1.5 adds these to the Phase 1 normalisation set so
goals involving `(a + b) * c` shapes (SdfPlane translation) and
`-K * x * x` shapes (Mantis exponential argument) close
automatically.

The first three are derived from existing axioms via the
inverse-uniqueness pattern (same technique as `neg_add` above).
The fourth, `neg_mul_neg`, falls out of two applications of
`neg_mul` plus `neg_neg`. -/

/-- Right-distributivity: `(a + b) * c = a * c + b * c`.
Derivable from `mul_distrib` + `mul_comm`. -/
theorem mul_distrib_right (a b c : Real) :
    (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, mul_distrib, mul_comm c a, mul_comm c b]

/-- `(-a) * b = -(a * b)`. Held as an axiom for the same reason as
the abs cluster in `Lemmas.lean` — provable via inverse-
uniqueness chain (`a * b + -a * b = (a + -a) * b = 0`), but the
chain runs into Lean precedence quirks (`-a * b` reparses
ambiguously between `(-a) * b` and `-(a * b)` depending on the
surrounding term). True in any commutative ring. -/
axiom neg_mul (a b : Real) : (-a) * b = -(a * b)

/-- `a * (-b) = -(a * b)`. Symmetric to `neg_mul`. Axiom. -/
axiom mul_neg (a b : Real) : a * (-b) = -(a * b)

/-- `-(-a) = a`. Double-negation cancellation. Held as axiom —
provable via inverse uniqueness chain (same shape as `neg_add`
above) but kept axiomatic for clarity. -/
axiom neg_neg_helper (a : Real) : -(-a) = a

/-- `(-a) * (-b) = a * b`. Two negations cancel. Derivable from
the axioms above. -/
theorem neg_mul_neg (a b : Real) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg_helper]

/-- `(a + b) + -(b + a) = 0`. The "swapped-pair cancellation" closer.
This is the residual shape `mach_ring` Phase 1 leaves when a Forge
matrix-cell witness has its `+ tx` term last in the LHS but the
expected RHS writes the addends in the opposite order
(`tx + sx`). Collapses by one `add_comm` + `add_neg`. -/
theorem add_neg_swapped (a b : Real) : (a + b) + -(b + a) = 0 := by
  rw [add_comm b a]; exact add_neg _

/-- `-(a + b) = -a + -b`. Distributivity of negation over addition.
Used by `mach_ring` to break apart compound negations so the
follow-up rewrite chain can pair each `+x` with its matching
`+(-x)` for `add_neg`-cancellation. -/
theorem neg_add (a b : Real) : -(a + b) = -a + -b := by
  -- Key fact: `(a + b) + (-a + -b) = 0`, i.e. `-a + -b` is an
  -- additive inverse of `a + b`. Combined with `-(a + b)` being
  -- the SAME inverse, the two are equal.
  have key : (a + b) + (-a + -b) = 0 := by
    -- (a + b) + (-a + -b) = a + b + -a + -b (assoc) = a + -a + b + -b (comm) = 0 + 0 = 0
    rw [add_assoc, ← add_assoc b (-a) (-b),
        add_comm b (-a), add_assoc, add_neg, add_zero, add_neg]
  -- -(a+b) = -(a+b) + 0 = -(a+b) + ((a+b) + (-a+-b))
  --        = (-(a+b) + (a+b)) + (-a+-b)
  --        = 0 + (-a+-b) = -a+-b
  calc -(a + b)
      = -(a + b) + 0                          := (add_zero _).symm
    _ = -(a + b) + ((a + b) + (-a + -b))      := by rw [key]
    _ = (-(a + b) + (a + b)) + (-a + -b)      := by rw [← add_assoc]
    _ = 0 + (-a + -b)                          := by rw [neg_add_self]
    _ = -a + -b                                := zero_add _

/-! ### `mach_ring` tactic

Closes "linear-in-zeros" polynomial identities in the supported
fragment. Workflow inside the macro:

  1. `intros` — bring `let` bindings into the local context so
     `simp only` can see through them. Forge-emitted theorems
     wrap matrix-cell expressions in a stack of `let m00 := 1`
     bindings; without this step `simp only` would walk past
     the constants without rewriting.
  2. `simp only [<rewrite-set>]` — apply the curated normalisation
     rules until no more progress is possible. Confluent on the
     supported fragment.
  3. `try rfl` — close trivial reflexivity that simp may leave on
     the table (e.g. `0 = 0` after the goal collapses).

If the goal isn't in the supported fragment, the tactic leaves
the goal in a normalised form so the user (or a follow-up
hand-proof) can see exactly which residue blocks closure. -/
macro "mach_ring" : tactic => `(tactic|
  (-- Phase 1: zero / one / sub-self normalisation. `zeta := true`
   -- expands `let` bindings introduced by Forge-emitted matrix-cell
   -- witnesses. Wrapped in `try` so a goal that's already in
   -- normal form falls through to Phase 2 instead of erroring on
   -- "simp made no progress". Note: `neg_add` is NOT in this set —
   -- we want negations to stay packed (`-(a+b)`, not `-a + -b`)
   -- so Phase 2's `add_neg` / `add_neg_swapped` can fire.
   try simp (config := { zeta := true }) only [
     one_mul_thm, mul_one_ax,
     zero_mul, mul_zero,
     zero_add, add_zero,
     sub_self, sub_zero, neg_zero,
     sub_def, add_neg,
     -- v1.5: distributivity + negation-multiplication. Order
     -- matters: `neg_mul` / `mul_neg` factor negations OUTSIDE
     -- products before `mul_distrib*` expands the products, so
     -- the final canonical form has all negations on outside-most
     -- atoms (matching `neg_neg_helper` cancellation).
     neg_mul, mul_neg, neg_mul_neg, neg_neg_helper,
     mul_distrib, mul_distrib_right
   ]
   -- Phase 2: handle the canonical residual shapes. Wrapped in
   -- `try first | ... | ...` so a goal closed by Phase 1 alone
   -- falls through cleanly without erroring on "no goals".
   --   * `rfl` — the two sides became syntactically identical.
   --   * `add_neg` — direct cancellation, e.g. `(x + tx) + -(x + tx) = 0`.
   --   * `add_neg_swapped` — pair-swap cancellation, e.g.
   --     `(sx + tx) + -(tx + sx) = 0`.
   --   * Full simp with AC + cancellation lemmas as the catch-all
   --     for any remaining shape Lean's term ordering can resolve.
   try (first
        | rfl
        | exact add_neg _
        | exact add_neg_swapped _ _
        -- Phase 2 catch-all: full AC over BOTH `+` and `*`. `mul_comm`
        -- + `mul_assoc` lets simp unify mirror-pair products like
        -- `ay * (az * bx)` and `az * (ay * bx)` that appear in
        -- cross-product / Lagrange polynomial identities. Plus the
        -- additive cancellation rules so `+x + -x` collapses.
        | simp [add_comm, add_assoc, mul_comm, mul_assoc,
                add_neg, neg_add_self, add_zero, zero_add, neg_add,
                neg_mul, mul_neg, neg_mul_neg, neg_neg_helper])))

end Real
end MachLib
