import MachLib.KhovanskiiReduction
import MachLib.IterExpChain
import MachLib.PfaffianFnBound
import MachLib.MultiPolyReconstruct

/-!
# MachLib.ChainExp2PathC — path (c) architecture for chain-level-2 Khovanskii

After investigation, my h-extended `InnerKhovanskiiExp` framework (commits
3889555 onward) is **structurally unable to close chain-level-2** for
iterated exponentials. The scalarMul with `mul (varY 0)` raises
`degreeY 0` by 1 on every coefficient at non-last positions, which no
Nat-valued inner measure can absorb. See `ChainExp2Instance.lean` for
the detailed failure analysis.

**This file documents the correct path forward**: use the EXISTING
`KhovanskiiReduction.lean` infrastructure (which I overlooked initially)
that takes the CLASSICAL Khovanskii approach with:

- `PfaffianFn.scaledReduction c f := f' - c · f` (a SCALAR multiplier
  `c · f`, NOT `c · y_n' · f` with the chain-relation factor).
- Lex measure `(degreeY_last f.poly, degreeX (leadingCoeffY_last f.poly))`
  on PfaffianFn directly.
- Well-founded induction on the lex measure (already proved well-founded
  via `lexLT_wf`).
- Witness construction via `IsKhovanskiiReducible` (already shipped).

The architecture is in place. The one missing piece is the **Step 3b
strict-decrease lemma** — multi-session future work per the docstrings
in KhovanskiiReduction.lean (lines 1174, 1340, 1389).

## The Step 3b strict-decrease lemma

For `p : MultiPoly 1` with `d := degreeY 0 p` and
`degreeX (leadingCoeffY 0 p) > 0`:

  degreeX (leadingCoeffY 0 (chainTotalDeriv SingleExpChain p - (natCast d) · p))
  < degreeX (leadingCoeffY 0 p)

### Why this is mathematically true

Write `p = a_d(x) · y_0^d + r` where `r` has `degreeY 0 r < d` and
`a_d = leadingCoeffY 0 p` (a polynomial in x only).

`chainTotalDeriv p` (using `y_0' = y_0` for SingleExpChain):
  = chainTotalDeriv (a_d · y_0^d) + chainTotalDeriv r
  = chainTotalDeriv a_d · y_0^d + a_d · chainTotalDeriv (y_0^d) + (lower)
  = polyDerivative_x a_d · y_0^d + a_d · (d · y_0^d) + (lower)
  = (polyDerivative_x a_d + d · a_d) · y_0^d + (lower in y_0)

(`chainTotalDeriv a_d = polyDerivative_x a_d` because `a_d` has
`degreeY 0 = 0` by `degreeY_leadingCoeffY`.)

`(natCast d) · p = d · a_d · y_0^d + d · r`. Leading: `d · a_d`.

Subtracting: leading y_0^d coefficient of `chainTotalDeriv p - d · p`
  = (polyDerivative_x a_d + d · a_d) - d · a_d
  = polyDerivative_x a_d.

**The `d · a_d` cancellation is the key**: it's exactly what makes the
`c = d` choice produce the strict descent.

`degreeX (polyDerivative_x a_d) < degreeX a_d` when `degreeX a_d > 0`
— that's the standard polynomial derivative property.

### What's needed to prove it constructively

Two intermediate lemmas (each ~50-100 lines):

1. **`leadingCoeffY_chainTotalDeriv_SingleExp`**:
   For `p : MultiPoly 1` with `d := degreeY 0 p > 0`:
   `leadingCoeffY 0 (chainTotalDeriv SingleExpChain p) =
    add (chainTotalDeriv SingleExpChain (leadingCoeffY 0 p))
        (mul (const (natCast d)) (leadingCoeffY 0 p))`

   Proven by structural induction on `p`'s AST. The `mul` case is the
   tricky one (Leibniz rule for total derivatives interacting with
   leading-coefficient extraction).

2. **`leadingCoeffY_scaledReduction_SingleExp`**: combines (1) with
   `leadingCoeffY_mul_const` + `leadingCoeffY_sub_of_eq` to get:
   `leadingCoeffY 0 (chainTotalDeriv p - (natCast d) · p) =
    chainTotalDeriv SingleExpChain (leadingCoeffY 0 p)`

   (The `d · leadingCoeffY` terms cancel.)

3. **Use existing `polyDerivative_strictly_decrease_degreeX`** (if it
   exists, or prove it) to close `degreeX (chainTotalDeriv (leadingCoeffY 0 p))
   < degreeX (leadingCoeffY 0 p)`.

   For `q : MultiPoly 1` with `degreeY 0 q = 0` (i.e., `q` is in x only),
   `chainTotalDeriv SingleExpChain q = polyDerivative_x q`. Its degreeX
   drops by 1 strictly when positive.

### Why my h-extended framework is the wrong abstraction

My h-extended framework `InnerKhovanskiiExp` was inspired by the
SingleExp argument's per-coefficient transform. But it ENCODES the
chain-rule factor INSIDE the scalarMul operation (so eval picks up
`h_deriv x` correctly). This puts `y_0` multiplication into every
coeffStep transform, breaking the measure descent.

The CLASSICAL approach (which the existing KhovanskiiReduction takes)
treats the chain-rule factor at the **polynomial level**, not the
inner-coefficient level. The `scaledReduction c f := f' - c · f`
operator applies at the PfaffianFn level (with `f'` being chainTotalDeriv
of the full polynomial). The lex measure tracks structural complexity
of the full polynomial, with strict descent at the leading coefficient.

**This is the canonically correct framework for chain-level Khovanskii.**
The h-extended framework was a misdirection on my part.

## What this commit ships

- This documentation file explaining:
  - Why the h-extended framework cannot close chain-level-2.
  - The correct architecture using existing KhovanskiiReduction
    infrastructure.
  - The specific intermediate lemmas needed (and their proof sketches)
    to discharge Step 3b strict-decrease.

- An import of both `KhovanskiiReduction` and `IterExpChain`, confirming
  the namespaces compose cleanly.

## What this commit does NOT ship

- Discharge of Step 3b strict-decrease. The three intermediate lemmas
  above are multi-session work, particularly (1) which requires careful
  structural induction handling the `mul`-case Leibniz interaction.

- The full chain-level-2 bound via Step 3d witness construction.
  KhovanskiiReduction.lean has the architecture (line 1376+) but
  parametrized over Step 3b. Once Step 3b lands, Step 3d closes.

## Honest assessment

The framework redesign (path c) doesn't require a NEW framework — the
correct framework is already shipped in `KhovanskiiReduction.lean`. My
h-extended framework was solving the wrong problem. The work that
remains is concrete proof work on a specific lemma, not architecture.

Next session's concrete goal: prove
`leadingCoeffY_chainTotalDeriv_SingleExp` (intermediate lemma 1). That's
the foundational structural identity; everything else assembles
mechanically from it. -/

namespace MachLib
namespace ChainExp2PathC

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-! ## Foundational lemma: chainTotalDeriv preserves y_0-freeness

For SingleExpChain, the chain relation is `relations 0 = varY 0`. So
chainTotalDeriv could introduce y_0 dependence via the varY case. But
if the input has `degreeY 0 = 0` (i.e., no y_0 in the AST), the varY 0
case never fires, and the result is y_0-free.

This is **intermediate lemma 3a** — a structural precondition for the
strict-decrease lemma. It lets us treat `leadingCoeffY 0 p` (which has
`degreeY 0 = 0` by `degreeY_leadingCoeffY`) as effectively a single-variable
polynomial when applying `chainTotalDeriv`. -/

theorem degreeY_chainTotalDeriv_zero_of_zero
    (p : MultiPoly 1) (h : MultiPoly.degreeY ⟨0, by omega⟩ p = 0) :
    MultiPoly.degreeY ⟨0, by omega⟩
      (chainTotalDeriv SingleExpChain p) = 0 := by
  induction p with
  | const c =>
    -- chainTotalDeriv (const c) = const 0. degreeY 0 (const 0) = 0.
    show MultiPoly.degreeY ⟨0, by omega⟩
          (MultiPoly.const (0 : MachLib.Real) : MultiPoly 1) = 0
    rfl
  | varX =>
    -- chainTotalDeriv varX = const 1. degreeY 0 (const 1) = 0.
    show MultiPoly.degreeY ⟨0, by omega⟩
          (MultiPoly.const (1 : MachLib.Real) : MultiPoly 1) = 0
    rfl
  | varY i =>
    -- hypothesis: degreeY 0 (varY i) = 0. But (varY 0) has degreeY 0 = 1.
    -- For i : Fin 1, i = ⟨0, _⟩. So degreeY 0 (varY 0) = 1. Hypothesis fails.
    exfalso
    have h_i : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [h_i] at h
    -- h : degreeY 0 (varY 0) = 0, which is `if 0 = 0 then 1 else 0 = 0`.
    show False
    have : (if (⟨0, by omega⟩ : Fin 1) = (⟨0, by omega⟩ : Fin 1) then (1 : Nat) else 0) = 0 := h
    rw [if_pos rfl] at this
    exact Nat.one_ne_zero this
  | add p q ihp ihq =>
    -- degreeY 0 (add p q) = max → both 0. IH gives both chainTotalDeriv 0.
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    have ih_p := ihp hp
    have ih_q := ihq hq
    -- chainTotalDeriv (add p q) = add (chainTotalDeriv p) (chainTotalDeriv q).
    -- degreeY 0 of this = max → both 0.
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain p))
                  (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain q)) = 0
    rw [ih_p, ih_q]
    rfl
  | sub p q ihp ihq =>
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    have ih_p := ihp hp
    have ih_q := ihq hq
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain p))
                  (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain q)) = 0
    rw [ih_p, ih_q]
    rfl
  | mul p q ihp ihq =>
    -- degreeY 0 (mul p q) = degreeY p + degreeY q = 0 → both 0.
    have hsum : MultiPoly.degreeY ⟨0, by omega⟩ p
              + MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := h
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := by omega
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := by omega
    have ih_p := ihp hp
    have ih_q := ihq hq
    -- chainTotalDeriv (mul p q) = add (mul (chainTotalDeriv p) q) (mul p (chainTotalDeriv q)).
    -- degreeY 0 of this = max(degreeY (mul (chainTotalDeriv p) q),
    --                          degreeY (mul p (chainTotalDeriv q)))
    --                  = max(degreeY chainTotalDeriv p + degreeY q,
    --                        degreeY p + degreeY chainTotalDeriv q)
    --                  = max(0 + 0, 0 + 0) = 0.
    show Nat.max
          (MultiPoly.degreeY ⟨0, by omega⟩
            (chainTotalDeriv SingleExpChain p)
           + MultiPoly.degreeY ⟨0, by omega⟩ q)
          (MultiPoly.degreeY ⟨0, by omega⟩ p
           + MultiPoly.degreeY ⟨0, by omega⟩
              (chainTotalDeriv SingleExpChain q)) = 0
    rw [ih_p, ih_q, hp, hq]
    rfl

/-! ## Lemma 3b — multiPolyToPoly bridges chainTotalDeriv to polyDerivative

For y_0-free `p : MultiPoly 1`, the existing `multiPolyToPoly` bridge
(from `PfaffianFnBound.lean`) sends `chainTotalDeriv SingleExpChain p`
to `polyDerivative (multiPolyToPoly p)`. This is the structural
correspondence that lets us lift the existing Poly strict-decrease
theorem (`polyDerivative_degreeUpper_lt_after_simplify`) to MultiPoly 1. -/

open MachLib.PfaffianFnBound
open MachLib.PolynomialRootCount
open MachLib.PolynomialEvidence (Poly)

theorem multiPolyToPoly_chainTotalDeriv_eq_polyDerivative
    (p : MultiPoly 1) (h : MultiPoly.degreeY ⟨0, by omega⟩ p = 0) :
    multiPolyToPoly (chainTotalDeriv SingleExpChain p) =
    polyDerivative (multiPolyToPoly p) := by
  induction p with
  | const c =>
    -- chainTotalDeriv (const c) = const 0. multiPolyToPoly (const 0) = Poly.const 0.
    -- polyDerivative (multiPolyToPoly (const c)) = polyDerivative (Poly.const c) = Poly.const 0.
    rfl
  | varX =>
    -- chainTotalDeriv varX = const 1. multiPolyToPoly (const 1) = Poly.const 1.
    -- polyDerivative (multiPolyToPoly varX) = polyDerivative Poly.var = Poly.const 1.
    rfl
  | varY i =>
    -- y_0-free forces no varY, but varY i in Fin 1 must be varY ⟨0, _⟩ with degreeY 0 = 1.
    exfalso
    have h_i : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [h_i] at h
    have : (if (⟨0, by omega⟩ : Fin 1) = (⟨0, by omega⟩ : Fin 1) then (1 : Nat) else 0) = 0 := h
    rw [if_pos rfl] at this
    exact Nat.one_ne_zero this
  | add p q ihp ihq =>
    -- y_0-free (add p q) gives both p and q y_0-free.
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    have ih_p := ihp hp
    have ih_q := ihq hq
    show multiPolyToPoly (chainTotalDeriv SingleExpChain (MultiPoly.add p q)) =
         polyDerivative (multiPolyToPoly (MultiPoly.add p q))
    -- LHS unfolds: multiPolyToPoly (add (chainTotalDeriv p) (chainTotalDeriv q))
    --            = Poly.add (multiPolyToPoly (chainTotalDeriv p))
    --                       (multiPolyToPoly (chainTotalDeriv q)).
    -- RHS unfolds: polyDerivative (Poly.add (multiPolyToPoly p) (multiPolyToPoly q))
    --            = Poly.add (polyDerivative (multiPolyToPoly p))
    --                       (polyDerivative (multiPolyToPoly q)).
    show Poly.add (multiPolyToPoly (chainTotalDeriv SingleExpChain p))
                  (multiPolyToPoly (chainTotalDeriv SingleExpChain q))
       = Poly.add (polyDerivative (multiPolyToPoly p))
                  (polyDerivative (multiPolyToPoly q))
    rw [ih_p, ih_q]
  | sub p q ihp ihq =>
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    have ih_p := ihp hp
    have ih_q := ihq hq
    show Poly.sub (multiPolyToPoly (chainTotalDeriv SingleExpChain p))
                  (multiPolyToPoly (chainTotalDeriv SingleExpChain q))
       = Poly.sub (polyDerivative (multiPolyToPoly p))
                  (polyDerivative (multiPolyToPoly q))
    rw [ih_p, ih_q]
  | mul p q ihp ihq =>
    have hsum : MultiPoly.degreeY ⟨0, by omega⟩ p
              + MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := h
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := by omega
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := by omega
    have ih_p := ihp hp
    have ih_q := ihq hq
    -- chainTotalDeriv (mul p q) = add (mul (chainTotalDeriv p) q) (mul p (chainTotalDeriv q)).
    -- multiPolyToPoly of this = Poly.add (Poly.mul ... ...) (Poly.mul ... ...).
    -- polyDerivative (multiPolyToPoly (mul p q)) = polyDerivative (Poly.mul (mpp p) (mpp q))
    --                                            = Poly.add (Poly.mul (polyDerivative mpp p) (mpp q))
    --                                                       (Poly.mul (mpp p) (polyDerivative mpp q)).
    show Poly.add (Poly.mul (multiPolyToPoly (chainTotalDeriv SingleExpChain p))
                             (multiPolyToPoly q))
                  (Poly.mul (multiPolyToPoly p)
                             (multiPolyToPoly (chainTotalDeriv SingleExpChain q)))
       = Poly.add (Poly.mul (polyDerivative (multiPolyToPoly p))
                             (multiPolyToPoly q))
                  (Poly.mul (multiPolyToPoly p)
                             (polyDerivative (multiPolyToPoly q)))
    rw [ih_p, ih_q]

/-! ## Lemma 3 proper — strict-decrease of degreeUpper via the bridge

The strict-decrease lemma needed for path (c)'s Step 3b: for y_0-free
`p : MultiPoly 1` with `degreeUpper (polySimplify (multiPolyToPoly p)) > 0`,

  `degreeUpper (polySimplify (multiPolyToPoly (chainTotalDeriv SingleExpChain p)))
   < degreeUpper (polySimplify (multiPolyToPoly p))`.

Direct consequence of `multiPolyToPoly_chainTotalDeriv_eq_polyDerivative`
(lemma 3b above) combined with the existing
`polyDerivative_degreeUpper_lt_after_simplify` from
`PolynomialRootCount.lean`. -/

theorem degreeUpper_polySimplify_multiPolyToPoly_chainTotalDeriv_lt
    (p : MultiPoly 1) (h_yfree : MultiPoly.degreeY ⟨0, by omega⟩ p = 0)
    (h_pos : degreeUpper (polySimplify (multiPolyToPoly p)) > 0) :
    degreeUpper (polySimplify (multiPolyToPoly
                  (chainTotalDeriv SingleExpChain p)))
    < degreeUpper (polySimplify (multiPolyToPoly p)) := by
  -- Bridge: multiPolyToPoly (chainTotalDeriv p) = polyDerivative (multiPolyToPoly p).
  rw [multiPolyToPoly_chainTotalDeriv_eq_polyDerivative p h_yfree]
  -- Now: degreeUpper (polySimplify (polyDerivative (multiPolyToPoly p)))
  --    < degreeUpper (polySimplify (multiPolyToPoly p))
  exact polyDerivative_degreeUpper_lt_after_simplify (multiPolyToPoly p) h_pos

/-! ## Lemma 1 prerequisite — chainTotalDeriv preserves degreeY exactly

The existing `degreeY_chainTotalDeriv_le` gives a NON-strict bound. For
lemma 1, we need the STRONG equality: chainTotalDeriv preserves degreeY
exactly on SingleExpChain (because `chain.relations 0 = varY 0` has
`degreeY 0 = 1`, same as `varY 0` itself).

This equality means: after chainTotalDeriv, the formal y_0-degree of
the result EQUALS that of the input. The leading-coefficient slots
line up. -/

theorem degreeY_chainTotalDeriv_eq_SingleExp (p : MultiPoly 1) :
    MultiPoly.degreeY ⟨0, by omega⟩
      (chainTotalDeriv SingleExpChain p) =
    MultiPoly.degreeY ⟨0, by omega⟩ p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i =>
    -- chainTotalDeriv (varY i) = chain.relations i = varY 0 (SingleExp).
    -- For Fin 1, i = ⟨0, _⟩. degreeY 0 (varY 0) = 1 on both sides.
    have h_i : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [h_i]
    rfl
  | add p q ihp ihq =>
    -- degreeY 0 (chainTotalDeriv (add p q)) = max → use IH on each side.
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain p))
                  (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain q))
       = Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain p))
                  (MultiPoly.degreeY ⟨0, by omega⟩
                    (chainTotalDeriv SingleExpChain q))
       = Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    -- chainTotalDeriv (mul p q) = add (mul deriv_p q) (mul p deriv_q).
    -- degreeY 0 = max(deg_p_after + deg_q, deg_p + deg_q_after)
    --           = max(deg_p + deg_q, deg_p + deg_q)  [by IH]
    --           = deg_p + deg_q.
    show Nat.max
          (MultiPoly.degreeY ⟨0, by omega⟩
            (chainTotalDeriv SingleExpChain p)
           + MultiPoly.degreeY ⟨0, by omega⟩ q)
          (MultiPoly.degreeY ⟨0, by omega⟩ p
           + MultiPoly.degreeY ⟨0, by omega⟩
              (chainTotalDeriv SingleExpChain q))
       = MultiPoly.degreeY ⟨0, by omega⟩ p
       + MultiPoly.degreeY ⟨0, by omega⟩ q
    rw [ihp, ihq]
    exact Nat.max_self _

/-! ## Lemma 1 proper — leadingCoeffY of chainTotalDeriv (eval-level)

The eval-level identity: for any `p : MultiPoly 1` with `d := degreeY 0 p`,

  `eval (leadingCoeffY 0 (chainTotalDeriv SingleExpChain p)) x env =
   eval (chainTotalDeriv SingleExpChain (leadingCoeffY 0 p)) x env +
   (natCast d) * eval (leadingCoeffY 0 p) x env`

(Holds for d ≥ 0 — when d = 0 the identity collapses to
`chainTotalDeriv p = chainTotalDeriv p`.)

Proof by structural induction on `p`. The mul case is the technical
heart: expand both sides via eval_add / eval_mul, apply IHs on each
factor, ring-rearrange so the (d_p + d_q) factor matches the RHS.

The `add` case with non-equal degrees uses
`degreeY_chainTotalDeriv_eq_SingleExp` (above) to know which side
contributes the leading coefficient. -/

/-- Lemma 1 BASE CASES: the eval-level identity holds for const, varX,
and varY. The full structural induction (add, sub, mul cases) is the
remaining work for Step 3b. -/
theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_base
    (x : MachLib.Real) (env : Fin 1 → MachLib.Real) :
    -- const c case
    (∀ c : MachLib.Real,
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain
                         (MultiPoly.const c : MultiPoly 1))) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (MultiPoly.const c : MultiPoly 1))) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                 (MultiPoly.const c : MultiPoly 1))) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (MultiPoly.const c : MultiPoly 1)) x env)
  ∧ -- varX case
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain
                       (MultiPoly.varX : MultiPoly 1))) x env =
     MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.varX : MultiPoly 1))) x env +
     (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                (MultiPoly.varX : MultiPoly 1))) *
       MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.varX : MultiPoly 1)) x env)
  ∧ -- varY 0 case
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain
                       (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 1))) x env =
     MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 1))) x env +
     (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 1))) *
       MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 1)) x env) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    show (0 : MachLib.Real) = 0 + MachLib.Real.natCast 0 * c
    rw [MachLib.Real.natCast_zero]; mach_ring
  · show (1 : MachLib.Real) = 1 + MachLib.Real.natCast 0 * x
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- chainTotalDeriv (varY 0) = relations 0 = varY 0.
    -- leadingCoeffY 0 (varY 0) = const 1.
    -- LHS = eval (const 1) = 1.
    -- chainTotalDeriv (const 1) = const 0.
    -- RHS = eval (const 0) + (natCast 1) * eval (const 1)
    --     = 0 + 1 * 1 = 1.
    show (1 : MachLib.Real) = 0 + MachLib.Real.natCast 1 * 1
    rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]
    mach_ring

/-! ## Lemma 1 proper — full structural induction (work in progress)

The add case requires the dp < dq, dp = dq, dp > dq trichotomy. The
dp < dq branch — proved below — works cleanly using
`degreeY_chainTotalDeriv_eq_SingleExp` to know the same comparison
holds after chainTotalDeriv. The dp = dq and dp > dq branches, plus
the sub case (symmetric) and mul case (Leibniz expansion + IH on both
factors), follow the same skeleton.

Shipping the add `dp < dq` sub-case proves the proof structure works
end-to-end through to a leaf, including the leadingCoeffY-of-add
case-analysis on degrees (the structural identity at the heart of
Step 3b). The remaining sub-cases follow the same pattern. -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_lt
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (hlt : MultiPoly.degreeY ⟨0, by omega⟩ p
         < MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.add p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.add p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  -- leadingCoeffY of (chainTotalDeriv (add p q)): degreeY q > degreeY p
  -- (preserved by chainTotalDeriv), so right side wins.
  have h_lhs : MultiPoly.leadingCoeffY ⟨0, by omega⟩
                (chainTotalDeriv SingleExpChain (MultiPoly.add p q))
              = MultiPoly.leadingCoeffY ⟨0, by omega⟩
                  (chainTotalDeriv SingleExpChain q) := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
             > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                (chainTotalDeriv SingleExpChain p)
          else if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
                  > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                      (chainTotalDeriv SingleExpChain q)
               else MultiPoly.add
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain q)))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩
              (chainTotalDeriv SingleExpChain q)
    rw [hp_eq, hq_eq]
    have h_outer_neg : ¬ MultiPoly.degreeY ⟨0, by omega⟩ p
                       > MultiPoly.degreeY ⟨0, by omega⟩ q :=
      Nat.not_lt.mpr (Nat.le_of_lt hlt)
    rw [if_neg h_outer_neg, if_pos hlt]
  have h_rhs_leading : MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (MultiPoly.add p q)
                      = MultiPoly.leadingCoeffY ⟨0, by omega⟩ q := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ p > MultiPoly.degreeY ⟨0, by omega⟩ q
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
          else if MultiPoly.degreeY ⟨0, by omega⟩ q > MultiPoly.degreeY ⟨0, by omega⟩ p
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩ q
               else MultiPoly.add (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                   (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩ q
    have h_outer_neg : ¬ MultiPoly.degreeY ⟨0, by omega⟩ p
                       > MultiPoly.degreeY ⟨0, by omega⟩ q :=
      Nat.not_lt.mpr (Nat.le_of_lt hlt)
    rw [if_neg h_outer_neg, if_pos hlt]
  have h_rhs_deg : MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.add p q)
                 = MultiPoly.degreeY ⟨0, by omega⟩ q := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ q
    exact Nat.max_eq_right (Nat.le_of_lt hlt)
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  exact ihq

/-! ## Helper: natCast over add

MachLib.Basic ships `natCast_zero` and `natCast_succ` but no
`natCast_add`. Prove it by induction on the right summand. -/

theorem natCast_add_helper (a b : Nat) :
    MachLib.Real.natCast (a + b)
    = MachLib.Real.natCast a + MachLib.Real.natCast b := by
  induction b with
  | zero =>
    show MachLib.Real.natCast (a + 0) = MachLib.Real.natCast a + MachLib.Real.natCast 0
    rw [MachLib.Real.natCast_zero, Nat.add_zero]
    mach_ring
  | succ b' ih =>
    show MachLib.Real.natCast (a + (b' + 1))
       = MachLib.Real.natCast a + MachLib.Real.natCast (b' + 1)
    rw [show a + (b' + 1) = (a + b') + 1 from by omega]
    rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_succ]
    rw [ih]
    mach_ring

/-! ## Pure-Real ring identity for lemma 1's mul case

The mul case's algebra reduces to one abstract identity:
  (A + na·B)·D + B·(C + nb·D) = A·D + B·C + (na + nb)·(B·D)

Expanding both sides: A·D + na·B·D + B·C + B·nb·D = A·D + B·C + na·B·D + nb·B·D.
These are equal by AC on +/*. mach_ring v2.5 closes this when the
variables are abstract (no nested AST sub-terms confusing the
distributivity simp). -/

theorem mul_case_ring_identity (A B C D na nb : MachLib.Real) :
    (A + na * B) * D + B * (C + nb * D)
    = A * D + B * C + (na + nb) * (B * D) := by
  mach_ring

/-- Pure-Real identity for lemma 1's sub_eq sub-case. Both sides equal
`A + n·B - C - n·D`. -/
theorem sub_eq_ring_identity (A B C D n : MachLib.Real) :
    (A + n * B) - (C + n * D) = (A - C) + n * (B - D) := by
  rw [MachLib.Real.sub_def, MachLib.Real.sub_def, MachLib.Real.sub_def]
  rw [MachLib.Real.mul_distrib n B (-D)]
  rw [MachLib.Real.neg_add C (n * D)]
  rw [MachLib.Real.mul_neg n D]
  ac_rfl

/-- Pure-Real identity for lemma 1's add_eq sub-case. -/
theorem add_eq_ring_identity (A B C D n : MachLib.Real) :
    (A + n * B) + (C + n * D) = (A + C) + n * (B + D) := by
  rw [MachLib.Real.mul_distrib n B D]
  ac_rfl

/-- Pure-Real identity for lemma 2's cancellation step:
`(A + B) - B = A`. -/
theorem sub_cancel_ring_identity (A B : MachLib.Real) :
    A + B - B = A := by
  rw [MachLib.Real.sub_def, MachLib.Real.add_assoc]
  rw [MachLib.Real.add_neg]
  rw [MachLib.Real.add_zero]

/-! ## Lemma 1 mul case — the technical heart of Step 3b

The mul case has special structure: both summands of the Leibniz
expansion `add (mul (cTD p) q) (mul p (cTD q))` have the SAME
`degreeY 0 = degreeY 0 p + degreeY 0 q` (using
`degreeY_chainTotalDeriv_eq_SingleExp`). So leadingCoeffY of the add
distributes into add of leadingCoeffYs (no trichotomy needed — degrees
are always equal).

Then `leadingCoeffY (mul X Y) = mul (leadingCoeffY X) (leadingCoeffY Y)`
factors each summand into a product of leadingCoeffYs. Apply IH on p
and q separately. mach_ring v2.5 closes the final algebra: the
`(d_p + d_q)` factor on the RHS emerges as `d_p · X + d_q · X` where
`X = eval (lcY p) · eval (lcY q)`. -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_mul
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.mul p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.mul p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.mul p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.mul p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  -- chainTotalDeriv (mul p q) = add (mul (cTD p) q) (mul p (cTD q)).
  -- Both summands have degreeY 0 = dp + dq. The leadingCoeffY of the
  -- equal-degree add distributes into add of leadingCoeffYs. Each
  -- inner leadingCoeffY of a mul is mul of leadingCoeffYs.
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.mul p q))
      = MultiPoly.add
          (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                            (chainTotalDeriv SingleExpChain p))
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
          (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                            (chainTotalDeriv SingleExpChain q))) := by
    -- Unfold the chainTotalDeriv expansion and the add's leadingCoeffY.
    show (if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
               + MultiPoly.degreeY ⟨0, by omega⟩ q
             > MultiPoly.degreeY ⟨0, by omega⟩ p
               + MultiPoly.degreeY ⟨0, by omega⟩
                  (chainTotalDeriv SingleExpChain q)
          then MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                               (chainTotalDeriv SingleExpChain p))
                             (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)
          else if MultiPoly.degreeY ⟨0, by omega⟩ p
                    + MultiPoly.degreeY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)
                  > MultiPoly.degreeY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)
                    + MultiPoly.degreeY ⟨0, by omega⟩ q
               then MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                  (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                     (chainTotalDeriv SingleExpChain q))
               else MultiPoly.add
                      (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                        (chainTotalDeriv SingleExpChain p))
                                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
                      (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                        (chainTotalDeriv SingleExpChain q))))
          = MultiPoly.add
              (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                (chainTotalDeriv SingleExpChain p))
                             (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
              (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                             (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                (chainTotalDeriv SingleExpChain q)))
    rw [hp_eq, hq_eq]
    have h_eq_deg :
        MultiPoly.degreeY ⟨0, by omega⟩ p + MultiPoly.degreeY ⟨0, by omega⟩ q
        = MultiPoly.degreeY ⟨0, by omega⟩ p
          + MultiPoly.degreeY ⟨0, by omega⟩ q := rfl
    have h_not_gt : ¬ MultiPoly.degreeY ⟨0, by omega⟩ p
                      + MultiPoly.degreeY ⟨0, by omega⟩ q
                    > MultiPoly.degreeY ⟨0, by omega⟩ p
                      + MultiPoly.degreeY ⟨0, by omega⟩ q :=
      Nat.lt_irrefl _
    rw [if_neg h_not_gt, if_neg h_not_gt]
  -- leadingCoeffY (mul p q) = mul (leadingCoeffY p) (leadingCoeffY q): rfl.
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.mul p q)
      = MultiPoly.mul (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) := rfl
  -- degreeY (mul p q) = dp + dq: rfl.
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.mul p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ p
        + MultiPoly.degreeY ⟨0, by omega⟩ q := rfl
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  -- chainTotalDeriv (mul (leadingCoeffY p) (leadingCoeffY q))
  --   = add (mul (cTD (lc p)) (lc q)) (mul (lc p) (cTD (lc q))) by rfl.
  -- (Leibniz expansion of chainTotalDeriv on a mul AST node.)
  show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain p)) x env
       * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env
     + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
       * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                          (chainTotalDeriv SingleExpChain q)) x env
     = (MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
        * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env
      + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
        * MultiPoly.eval (chainTotalDeriv SingleExpChain
                           (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
     + MachLib.Real.natCast
         (MultiPoly.degreeY ⟨0, by omega⟩ p
          + MultiPoly.degreeY ⟨0, by omega⟩ q)
       * (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
        * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
  -- Apply IHs on p and q.
  rw [ihp, ihq]
  -- natCast distributes over add.
  rw [show MachLib.Real.natCast
              (MultiPoly.degreeY ⟨0, by omega⟩ p
               + MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
         + MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)
      from natCast_add_helper _ _]
  -- The algebra is the abstract identity
  --   (A + na * B) * D + B * (C + nb * D) = A * D + B * C + (na + nb) * (B * D)
  -- mach_ring v2.5 leaves residue when the nested * structure inside +
  -- atoms differs across sides. Abstracting into the helper below clears
  -- the names so mach_ring sees a flat polynomial identity it can close.
  exact mul_case_ring_identity
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p))
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q))

/-! ## Lemma 1 add_eq sub-case — when degreeY 0 p = degreeY 0 q

leadingCoeffY of (add p q) with equal degrees distributes into
add of leadingCoeffYs (the else branch of the if-chain). Both IHs
apply directly. The algebra distributes naturally. -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_eq
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (heq : MultiPoly.degreeY ⟨0, by omega⟩ p
         = MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.add p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.add p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  -- leadingCoeffY of (chainTotalDeriv (add p q)): both chainTotalDeriv'd
  -- summands have equal degreeY 0 (= dp = dq), so leadingCoeffY of the
  -- add distributes into add of leadingCoeffYs.
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.add p q))
      = MultiPoly.add
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩
             (chainTotalDeriv SingleExpChain p))
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩
             (chainTotalDeriv SingleExpChain q)) := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
             > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                (chainTotalDeriv SingleExpChain p)
          else if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
                  > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                      (chainTotalDeriv SingleExpChain q)
               else MultiPoly.add
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain q)))
          = MultiPoly.add
              (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                 (chainTotalDeriv SingleExpChain p))
              (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                 (chainTotalDeriv SingleExpChain q))
    rw [hp_eq, hq_eq, heq]
    have h_not_gt : ¬ MultiPoly.degreeY ⟨0, by omega⟩ q
                    > MultiPoly.degreeY ⟨0, by omega⟩ q :=
      Nat.lt_irrefl _
    rw [if_neg h_not_gt, if_neg h_not_gt]
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.add p q)
      = MultiPoly.add (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ p > MultiPoly.degreeY ⟨0, by omega⟩ q
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
          else if MultiPoly.degreeY ⟨0, by omega⟩ q > MultiPoly.degreeY ⟨0, by omega⟩ p
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩ q
               else MultiPoly.add (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                   (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
          = MultiPoly.add (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)
    rw [heq]
    have h_not_gt : ¬ MultiPoly.degreeY ⟨0, by omega⟩ q
                    > MultiPoly.degreeY ⟨0, by omega⟩ q :=
      Nat.lt_irrefl _
    rw [if_neg h_not_gt, if_neg h_not_gt]
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.add p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ p := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ p
    rw [heq]; exact Nat.max_self _
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  -- Goal: eval(add LCp_d LCq_d) = eval(cTD (add LCp LCq)) + dp * eval(add LCp LCq)
  -- Expand eval(add) = sum, apply IHs, then mach_ring.
  show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain p)) x env
     + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain q)) x env
     = (MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
      + MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
     + MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
       * (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
        + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
  rw [ihp, ihq]
  rw [show MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
      from by rw [heq]]
  exact add_eq_ring_identity
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p))

/-! ## Lemma 1 add_gt sub-case — symmetric to add_lt -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_gt
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (hgt : MultiPoly.degreeY ⟨0, by omega⟩ p
         > MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.add p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.add p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.add p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  -- p dominates: leadingCoeffY of (add p q) on both sides reduces to leadingCoeffY p.
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.add p q))
      = MultiPoly.leadingCoeffY ⟨0, by omega⟩
          (chainTotalDeriv SingleExpChain p) := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
             > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                (chainTotalDeriv SingleExpChain p)
          else if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
                  > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                      (chainTotalDeriv SingleExpChain q)
               else MultiPoly.add
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain q)))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩
              (chainTotalDeriv SingleExpChain p)
    rw [hp_eq, hq_eq, if_pos hgt]
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.add p q)
      = MultiPoly.leadingCoeffY ⟨0, by omega⟩ p := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ p > MultiPoly.degreeY ⟨0, by omega⟩ q
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
          else if MultiPoly.degreeY ⟨0, by omega⟩ q > MultiPoly.degreeY ⟨0, by omega⟩ p
               then MultiPoly.leadingCoeffY ⟨0, by omega⟩ q
               else MultiPoly.add (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                   (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
    rw [if_pos hgt]
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.add p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ p := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ p
    exact Nat.max_eq_left (Nat.le_of_lt hgt)
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  exact ihp

/-! ## Lemma 1 sub_lt sub-case — degreeY 0 p < degreeY 0 q

For sub with q dominating, leadingCoeffY uses sub (const 0) (lcY q)
(by `leadingCoeffY_sub_of_lt`). The chainTotalDeriv of the sub-of-add
expansion needs careful tracking — the constant 0 chainTotalDeriv's
to 0, leaving -chainTotalDeriv (lcY q) on both sides. -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_lt
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (hlt : MultiPoly.degreeY ⟨0, by omega⟩ p
         < MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.sub p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  have h_deg_lt :
      MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
      < MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q) := by
    rw [hp_eq, hq_eq]; exact hlt
  -- leadingCoeffY of (chainTotalDeriv (sub p q)) = sub (const 0) (lcY (cTD q))
  -- via the existing lemma.
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))
      = MultiPoly.sub (MultiPoly.const 0)
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩
             (chainTotalDeriv SingleExpChain q)) := by
    show MultiPoly.leadingCoeffY ⟨0, by omega⟩
          (MultiPoly.sub (chainTotalDeriv SingleExpChain p)
                          (chainTotalDeriv SingleExpChain q))
        = MultiPoly.sub (MultiPoly.const 0)
            (MultiPoly.leadingCoeffY ⟨0, by omega⟩
               (chainTotalDeriv SingleExpChain q))
    exact MultiPoly.leadingCoeffY_sub_of_lt ⟨0, by omega⟩ _ _ h_deg_lt
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.sub (MultiPoly.const 0)
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) :=
    MultiPoly.leadingCoeffY_sub_of_lt ⟨0, by omega⟩ p q hlt
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ q := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ q
    exact Nat.max_eq_right (Nat.le_of_lt hlt)
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  -- LHS: eval (sub (const 0) (lcY (cTD q))) = 0 - eval (lcY (cTD q)) = -eval (lcY (cTD q))
  -- RHS: eval (cTD (sub 0 (lcY q))) + dq * eval (sub 0 (lcY q))
  --    = (0 - eval (cTD (lcY q))) + dq * (0 - eval (lcY q))
  --    = -eval (cTD (lcY q)) - dq * eval (lcY q)
  -- Apply ihq: eval (lcY (cTD q)) = eval (cTD (lcY q)) + dq * eval (lcY q)
  -- Then LHS = -(eval (cTD (lcY q)) + dq * eval (lcY q)) = -eval (cTD (lcY q)) - dq * eval (lcY q) = RHS ✓
  show (0 : MachLib.Real) - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                                            (chainTotalDeriv SingleExpChain q)) x env
     = (0 - MultiPoly.eval (chainTotalDeriv SingleExpChain
                             (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
     + MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)
       * (0 - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
  rw [ihq]
  mach_ring

/-! ## Lemma 1 sub_eq sub-case — when degreeY 0 p = degreeY 0 q -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_eq
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (heq : MultiPoly.degreeY ⟨0, by omega⟩ p
         = MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain q)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.sub p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  have h_deg_eq :
      MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
      = MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q) := by
    rw [hp_eq, hq_eq]; exact heq
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))
      = MultiPoly.sub (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                          (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                          (chainTotalDeriv SingleExpChain q)) :=
    MultiPoly.leadingCoeffY_sub_of_eq ⟨0, by omega⟩ _ _ h_deg_eq
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.sub (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) :=
    MultiPoly.leadingCoeffY_sub_of_eq ⟨0, by omega⟩ p q heq
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ p := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ p
    rw [heq]; exact Nat.max_self _
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain p)) x env
     - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain q)) x env
     = (MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
      - MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
     + MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
       * (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
        - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
  rw [ihp, ihq]
  rw [show MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
      from by rw [heq]]
  exact sub_eq_ring_identity
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)) x env)
    (MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q) x env)
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p))

/-! ## Lemma 1 sub_gt sub-case — degreeY 0 p > degreeY 0 q -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_gt
    (p q : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real)
    (hgt : MultiPoly.degreeY ⟨0, by omega⟩ p
         > MultiPoly.degreeY ⟨0, by omega⟩ q)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (chainTotalDeriv SingleExpChain p)) x env =
      MultiPoly.eval (chainTotalDeriv SingleExpChain
                       (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
      (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
        MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q))) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩
                            (MultiPoly.sub p q))) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                       (MultiPoly.sub p q)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  have hq_eq := degreeY_chainTotalDeriv_eq_SingleExp q
  have h_lhs :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (chainTotalDeriv SingleExpChain (MultiPoly.sub p q))
      = MultiPoly.leadingCoeffY ⟨0, by omega⟩
          (chainTotalDeriv SingleExpChain p) := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
             > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩
                (chainTotalDeriv SingleExpChain p)
          else if MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain q)
                  > MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
               then MultiPoly.sub (MultiPoly.const 0)
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain q))
               else MultiPoly.sub
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain q)))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩
              (chainTotalDeriv SingleExpChain p)
    rw [hp_eq, hq_eq, if_pos hgt]
  have h_rhs_leading :
      MultiPoly.leadingCoeffY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.leadingCoeffY ⟨0, by omega⟩ p := by
    show (if MultiPoly.degreeY ⟨0, by omega⟩ p > MultiPoly.degreeY ⟨0, by omega⟩ q
          then MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
          else if MultiPoly.degreeY ⟨0, by omega⟩ q > MultiPoly.degreeY ⟨0, by omega⟩ p
               then MultiPoly.sub (MultiPoly.const 0)
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q)
               else MultiPoly.sub (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)
                                   (MultiPoly.leadingCoeffY ⟨0, by omega⟩ q))
          = MultiPoly.leadingCoeffY ⟨0, by omega⟩ p
    rw [if_pos hgt]
  have h_rhs_deg :
      MultiPoly.degreeY ⟨0, by omega⟩ (MultiPoly.sub p q)
      = MultiPoly.degreeY ⟨0, by omega⟩ p := by
    show Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                  (MultiPoly.degreeY ⟨0, by omega⟩ q)
         = MultiPoly.degreeY ⟨0, by omega⟩ p
    exact Nat.max_eq_left (Nat.le_of_lt hgt)
  rw [h_lhs, h_rhs_leading, h_rhs_deg]
  exact ihp

/-! ## Lemma 1 full — the assembly

The full structural induction dispatches each AST case to the
corresponding helper. const / varX / varY close inline (the base
cases). add / sub trichotomize on degreeY 0 p vs degreeY 0 q and
dispatch to _add_lt / _add_eq / _add_gt or _sub_lt / _sub_eq / _sub_gt.
mul dispatches to the mul helper. -/

theorem leadingCoeffY_chainTotalDeriv_eval_SingleExp
    (p : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                     (chainTotalDeriv SingleExpChain p)) x env =
    MultiPoly.eval (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env +
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) *
      MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env := by
  induction p with
  | const c =>
    show (0 : MachLib.Real) = 0 + MachLib.Real.natCast 0 * c
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varX =>
    show (1 : MachLib.Real) = 1 + MachLib.Real.natCast 0 * x
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varY i =>
    have h_i : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [h_i]
    show (1 : MachLib.Real) = 0 + MachLib.Real.natCast 1 * 1
    rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]
    mach_ring
  | add p q ihp ihq =>
    rcases Nat.lt_trichotomy (MultiPoly.degreeY ⟨0, by omega⟩ p)
                              (MultiPoly.degreeY ⟨0, by omega⟩ q) with hlt | heq | hgt
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_lt p q x env hlt ihq
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_eq p q x env heq ihp ihq
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_add_gt p q x env hgt ihp
  | sub p q ihp ihq =>
    rcases Nat.lt_trichotomy (MultiPoly.degreeY ⟨0, by omega⟩ p)
                              (MultiPoly.degreeY ⟨0, by omega⟩ q) with hlt | heq | hgt
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_lt p q x env hlt ihq
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_eq p q x env heq ihp ihq
    · exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_sub_gt p q x env hgt ihp
  | mul p q ihp ihq =>
    exact leadingCoeffY_chainTotalDeriv_eval_SingleExp_mul p q x env ihp ihq

/-! ## Lemma 2 — the d·a_d cancellation identity

The "scaled-reduction" leading coefficient identity. For any
p : MultiPoly 1 with d := degreeY 0 p:

  eval (leadingCoeffY 0 (chainTotalDeriv p - (natCast d) · p)) x env
  = eval (chainTotalDeriv (leadingCoeffY 0 p)) x env

This is the algebraic consequence of lemma 1 + the leadingCoeffY-of-sub
case-analysis when degrees match. The `d · leadingCoeffY p` term from
lemma 1 cancels with the `d · leadingCoeffY p` from the second
summand's leading. What remains is `chainTotalDeriv (leadingCoeffY p)`,
which (since `leadingCoeffY p` has `degreeY 0 = 0`) acts as a
polynomial derivative in x. -/

theorem leadingCoeffY_scaledReduction_eval_SingleExp
    (p : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real) :
    MultiPoly.eval
      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (MultiPoly.sub
          (chainTotalDeriv SingleExpChain p)
          (MultiPoly.mul (MultiPoly.const
                            (MachLib.Real.natCast
                               (MultiPoly.degreeY ⟨0, by omega⟩ p))) p))) x env =
    MultiPoly.eval
      (chainTotalDeriv SingleExpChain
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env := by
  have hp_eq := degreeY_chainTotalDeriv_eq_SingleExp p
  -- Degrees of the two sub summands match (both = degreeY 0 p).
  have h_deg_eq :
      MultiPoly.degreeY ⟨0, by omega⟩ (chainTotalDeriv SingleExpChain p)
      = MultiPoly.degreeY ⟨0, by omega⟩
          (MultiPoly.mul (MultiPoly.const
                            (MachLib.Real.natCast
                               (MultiPoly.degreeY ⟨0, by omega⟩ p))) p) := by
    rw [hp_eq]
    show MultiPoly.degreeY ⟨0, by omega⟩ p
         = MultiPoly.degreeY ⟨0, by omega⟩
             (MultiPoly.const (MachLib.Real.natCast
                                  (MultiPoly.degreeY ⟨0, by omega⟩ p)))
           + MultiPoly.degreeY ⟨0, by omega⟩ p
    show MultiPoly.degreeY ⟨0, by omega⟩ p = 0 + MultiPoly.degreeY ⟨0, by omega⟩ p
    omega
  -- leadingCoeffY of (sub with equal degrees) = sub of leadingCoeffYs.
  have h_lc_sub : MultiPoly.leadingCoeffY ⟨0, by omega⟩
                    (MultiPoly.sub
                      (chainTotalDeriv SingleExpChain p)
                      (MultiPoly.mul (MultiPoly.const
                                        (MachLib.Real.natCast
                                           (MultiPoly.degreeY ⟨0, by omega⟩ p))) p))
                  = MultiPoly.sub
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (chainTotalDeriv SingleExpChain p))
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                         (MultiPoly.mul (MultiPoly.const
                                            (MachLib.Real.natCast
                                               (MultiPoly.degreeY ⟨0, by omega⟩ p))) p)) :=
    MultiPoly.leadingCoeffY_sub_of_eq ⟨0, by omega⟩ _ _ h_deg_eq
  -- leadingCoeffY (mul (const d) p) = mul (const d) (leadingCoeffY p).
  have h_lc_mul := MultiPoly.leadingCoeffY_mul_const ⟨0, by omega⟩
                     (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)) p
  rw [h_lc_sub, h_lc_mul]
  -- eval expands: eval(sub a b) = eval a - eval b. Substitute lemma 1
  -- for the chainTotalDeriv leading. The `d · leadingCoeffY p` terms
  -- cancel between lemma 1's RHS and the second summand.
  show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩
                        (chainTotalDeriv SingleExpChain p)) x env
     - MultiPoly.eval (MultiPoly.mul
                         (MultiPoly.const
                            (MachLib.Real.natCast
                               (MultiPoly.degreeY ⟨0, by omega⟩ p)))
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
     = MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
  rw [leadingCoeffY_chainTotalDeriv_eval_SingleExp p x env]
  show MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
     + MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
       * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
     - MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
       * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env
     = MultiPoly.eval (chainTotalDeriv SingleExpChain
                         (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env
  exact sub_cancel_ring_identity
    (MultiPoly.eval (chainTotalDeriv SingleExpChain
                      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p)) x env)
    (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)
     * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) x env)

/-! ## Auxiliary: multiPolyToPoly preserves eval for y-free MultiPoly 1

multiPolyToPoly was defined for n = 0 in PfaffianFnBound, but the
construction also gives the right eval when the input is y-free
(the varY case never fires structurally). This auxiliary version
makes that explicit. -/

theorem multiPolyToPoly_eval_y_free :
    ∀ (p : MultiPoly 1) (_h : MultiPoly.degreeY ⟨0, by omega⟩ p = 0)
      (x : MachLib.Real) (env : Fin 1 → MachLib.Real),
    Poly.eval (multiPolyToPoly p) x = MultiPoly.eval p x env
  | MultiPoly.const _, _, _, _ => rfl
  | MultiPoly.varX, _, _, _ => rfl
  | MultiPoly.varY i, h, _, _ => by
    exfalso
    have h_i : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [h_i] at h
    have : (if (⟨0, by omega⟩ : Fin 1) = (⟨0, by omega⟩ : Fin 1) then (1 : Nat) else 0) = 0 := h
    rw [if_pos rfl] at this
    exact Nat.one_ne_zero this
  | MultiPoly.add p q, h, x, env => by
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    show Poly.eval (multiPolyToPoly p) x + Poly.eval (multiPolyToPoly q) x
       = MultiPoly.eval p x env + MultiPoly.eval q x env
    rw [multiPolyToPoly_eval_y_free p hp x env,
        multiPolyToPoly_eval_y_free q hq x env]
  | MultiPoly.sub p q, h, x, env => by
    have hmax : Nat.max (MultiPoly.degreeY ⟨0, by omega⟩ p)
                        (MultiPoly.degreeY ⟨0, by omega⟩ q) = 0 := h
    have ⟨hp_le, hq_le⟩ : MultiPoly.degreeY ⟨0, by omega⟩ p ≤ 0 ∧
                          MultiPoly.degreeY ⟨0, by omega⟩ q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := Nat.le_zero.mp hp_le
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := Nat.le_zero.mp hq_le
    show Poly.eval (multiPolyToPoly p) x - Poly.eval (multiPolyToPoly q) x
       = MultiPoly.eval p x env - MultiPoly.eval q x env
    rw [multiPolyToPoly_eval_y_free p hp x env,
        multiPolyToPoly_eval_y_free q hq x env]
  | MultiPoly.mul p q, h, x, env => by
    have hsum : MultiPoly.degreeY ⟨0, by omega⟩ p
              + MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := h
    have hp : MultiPoly.degreeY ⟨0, by omega⟩ p = 0 := by omega
    have hq : MultiPoly.degreeY ⟨0, by omega⟩ q = 0 := by omega
    show Poly.eval (multiPolyToPoly p) x * Poly.eval (multiPolyToPoly q) x
       = MultiPoly.eval p x env * MultiPoly.eval q x env
    rw [multiPolyToPoly_eval_y_free p hp x env,
        multiPolyToPoly_eval_y_free q hq x env]

/-! ## Step 3b — strict-decrease of the lex measure's second component

Combines lemma 2 (the d·a_d cancellation) with lemma 3 (strict-decrease
of chainTotalDeriv on y-free polynomials via the multiPolyToPoly bridge).

The chain: under scaledReduction at c = degreeY_last,
1. **Lemma 2**: leadingCoeffY of the result eval-equals
   chainTotalDeriv(leadingCoeffY p).
2. **Lemma 3a**: leadingCoeffY p is y-free (degreeY 0 = 0).
3. **Lemma 3b**: chainTotalDeriv on y-free = polyDerivative via the
   multiPolyToPoly bridge.
4. **Lemma 3 proper**: polyDerivative strictly decreases degreeUpper
   after polySimplify.

The eval-level claim of Step 3b:

  eval (leadingCoeffY 0 (chainTotalDeriv p - d · p)) x env
  = polyEval (polyDerivative (multiPolyToPoly (leadingCoeffY 0 p))) x

combined with the strict-decrease lemma gives the eval-level
strict-decrease for the lex measure's second component on the
multiPolyToPoly-bridged form. -/

open MachLib.PolynomialEvidence (Poly)

theorem step3b_eval_bridge
    (p : MultiPoly 1) (x : MachLib.Real) (env : Fin 1 → MachLib.Real) :
    MultiPoly.eval
      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (MultiPoly.sub
          (chainTotalDeriv SingleExpChain p)
          (MultiPoly.mul (MultiPoly.const
                            (MachLib.Real.natCast
                               (MultiPoly.degreeY ⟨0, by omega⟩ p))) p))) x env =
    Poly.eval (polyDerivative
                 (multiPolyToPoly
                    (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) x := by
  -- Step 1: apply lemma 2 to reduce LHS to eval(cTD(leadingCoeffY p)).
  rw [leadingCoeffY_scaledReduction_eval_SingleExp p x env]
  -- Step 2: leadingCoeffY p is y-free (degreeY 0 = 0 by degreeY_leadingCoeffY).
  have h_yfree :
      MultiPoly.degreeY ⟨0, by omega⟩
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY ⟨0, by omega⟩ p
  -- Step 3: chainTotalDeriv preserves y-freeness (lemma 3a).
  have h_cTD_yfree :=
    degreeY_chainTotalDeriv_zero_of_zero
      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) h_yfree
  -- Step 4: chainTotalDeriv on y-free MultiPoly 1 = polyDerivative via
  -- the multiPolyToPoly bridge (lemma 3b).
  have h_bridge :=
    multiPolyToPoly_chainTotalDeriv_eq_polyDerivative
      (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) h_yfree
  -- eval (cTD (leadingCoeffY p)) x env
  --   = polyEval (multiPolyToPoly (cTD (leadingCoeffY p))) x  (y-free preserves eval)
  --   = polyEval (polyDerivative (multiPolyToPoly (leadingCoeffY p))) x  (h_bridge)
  rw [← multiPolyToPoly_eval_y_free
        (chainTotalDeriv SingleExpChain (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))
        h_cTD_yfree x env]
  rw [h_bridge]

/-! ## Step 3b strict-decrease conclusion

Combining `step3b_eval_bridge` with the existing
`polyDerivative_degreeUpper_lt_after_simplify` gives the formal-degree
strict-decrease bound used in path (c)'s lex measure. -/

theorem step3b_degreeUpper_strict_decrease
    (p : MultiPoly 1)
    (h_pos : degreeUpper (polySimplify (multiPolyToPoly
                            (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    degreeUpper (polySimplify (multiPolyToPoly
                  (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))))
    < degreeUpper (polySimplify (multiPolyToPoly
                  (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) := by
  have h_yfree :
      MultiPoly.degreeY ⟨0, by omega⟩
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY ⟨0, by omega⟩ p
  exact degreeUpper_polySimplify_multiPolyToPoly_chainTotalDeriv_lt
    (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p) h_yfree h_pos

/-! ## Status

**Shipped**:
- `degreeY_chainTotalDeriv_zero_of_zero` (lemma 3a) — y_0-freeness
  preservation under chainTotalDeriv.
- `multiPolyToPoly_chainTotalDeriv_eq_polyDerivative` (lemma 3b) — the
  bridge: multiPolyToPoly converts chainTotalDeriv on y_0-free MultiPoly 1
  into polyDerivative on Poly.
- `degreeUpper_polySimplify_multiPolyToPoly_chainTotalDeriv_lt`
  (lemma 3 proper) — strict-decrease of degreeUpper-after-polySimplify,
  via the bridge.
- `degreeY_chainTotalDeriv_eq_SingleExp` (lemma 1 prerequisite) — the
  STRONG equality: chainTotalDeriv preserves degreeY exactly on
  SingleExpChain. Crucial for ensuring leadingCoeffY positions line up
  before and after chainTotalDeriv.

**Step 3b — complete**. The eval-bridge plus the formal-degree
strict-decrease are both shipped above. The PfaffianFn-level wrapper
is shipped below. -/

/-! ## PfaffianFn-level wrapper for Step 3b

Wraps the eval-bridge (`step3b_eval_bridge`) into the
`PfaffianFn.scaledReduction` API used by the existing
`KhovanskiiReduction.lean` Step 3d structural recursion. The wrapper
takes a chain-length-1 PfaffianFn over SingleExpChain (the most
common path-c starting point) and proves the strict-decrease in the
lex measure's second component, via the bridge measure
`degreeUpper ∘ polySimplify ∘ multiPolyToPoly`.

The user-facing entry point Step 3d needs is
`step3b_pfaffianFn_singleExp_strict_decrease`. -/

/-- **Unfolded `PfaffianFn.scaledReduction.poly` for the SingleExp case.**
The poly of `f.scaledReduction c` for `f = { n := 1, chain := SingleExpChain,
poly := p }` reduces structurally to `sub (cTD SingleExpChain p) (mul (const c) p)`.
This lemma makes the unfolding explicit so subsequent theorems can pattern
match without unfolding through the structure access. -/
theorem singleExp_scaledReduction_poly (p : MultiPoly 1) (c : MachLib.Real) :
    (PfaffianFn.scaledReduction c
        { n := 1, chain := SingleExpChain, poly := p }).poly
    = MultiPoly.sub (chainTotalDeriv SingleExpChain p)
                    (MultiPoly.mul (MultiPoly.const c) p) := rfl

/-- The chain-length-1 PfaffianFn wrapper for `step3b_eval_bridge`.
For `p : MultiPoly 1` interpreted as a PfaffianFn over SingleExpChain,
the leadingCoeffY of the scaledReduction (at `c = degreeY 0 p`)
eval-equals the polyDerivative of the multiPolyToPoly-bridged
leadingCoeffY. -/
theorem step3b_pfaffianFn_singleExp_eval_bridge
    (p : MultiPoly 1) (x : MachLib.Real) :
    MultiPoly.eval
      (MultiPoly.leadingCoeffY ⟨0, by omega⟩
        (MultiPoly.sub
          (chainTotalDeriv SingleExpChain p)
          (MultiPoly.mul (MultiPoly.const
                            (MachLib.Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)))
                         p)))
      x
      (SingleExpChain.chainValues x) =
    Poly.eval (polyDerivative
                 (multiPolyToPoly
                    (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) x :=
  step3b_eval_bridge p x _

/-- **Step 3b PfaffianFn-level strict-decrease** (intermediate form).

The bridged measure `degreeUpper ∘ polySimplify ∘ multiPolyToPoly`
applied to `chainTotalDeriv (leadingCoeffY 0 p)` is strictly less
than the same measure applied to `leadingCoeffY 0 p` — directly from
`step3b_degreeUpper_strict_decrease` (shipped above).

The connection from this form to `leadingCoeffY 0
(f.scaledReduction c).poly` requires composing lemma 2 (the d·a_d
cancellation) with `multiPolyToPoly`'s distribution over `sub` + the
polySimplify of mul-by-const. Both are mechanical but non-trivial
~30-50 lines of plumbing; deferred to where the Step 3d structural
recursion actually consumes it (the lex measure check at the
PfaffianFn level). -/
theorem step3b_pfaffianFn_singleExp_strict_decrease_via_leadingCoeffY
    (p : MultiPoly 1)
    (h_pos : degreeUpper (polySimplify (multiPolyToPoly
                            (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    degreeUpper (polySimplify (multiPolyToPoly
                  (chainTotalDeriv SingleExpChain
                     (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))))
    < degreeUpper (polySimplify (multiPolyToPoly
                  (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) :=
  step3b_degreeUpper_strict_decrease p h_pos

/-! ## Phase H closure — `h_bridge` for `singleExp_reduceStep`

Wires lemma 2 + the eval / cTD-structural / derivative-canonical
bridges + Phase G strict-decrease into the lex strict-decrease under
SingleExp `scaledReduction` at `c = degreeY_last`. Provides a
ReduceStep constructor (`singleExp_reduceStep_closed`) without an
external `h_bridge` hypothesis.

The closure works at the chain-length-1 / `MultiPoly 1` level. The
PfaffianFn-level wrapper specializes via `hN : f.n = 1` plus
`h_chain : f.chain = SingleExpChain`.

The proof routes through:

  polyTrueDegree (polyCoeffs (mP2PFL (lcY 0 scaledReduction.poly)))
    = polyTrueDegree (polyCoeffs (mP2PFL (cTD (lcY 0 p))))   -- via lemma 2 + bridge (1) + PIT
    = polyTrueDegree (polyCoeffs (polyDerivative (mP2PFL (lcY 0 p))))     -- via bridge (2)
    = polyTrueDegree (polyDerivativeCoeffs (polyCoeffs (mP2PFL (lcY 0 p)))) -- via bridge (3)
    < polyTrueDegree (polyCoeffs (mP2PFL (lcY 0 p)))                       -- via Phase G strict-decrease

The `h_canon_pos` precondition (canonical leading-coefficient
x-degree > 0) is what feeds Phase G; the `polyTrueDegree = 0` case
needs separate framework handling (the lex measure as currently
defined cannot distinguish a canonically-constant leading
coefficient from a canonically-zero one, since both yield
polyTrueDegree = 0). -/

open MachLib.PolynomialCanonical in
/-- The MultiPoly-1-level strict-decrease theorem: the chain of
bridges. Given the canonical leading-coefficient x-degree precondition,
the polyTrueDegree of the scaledReduction's leading coefficient (via
mP2PFL + polyCoeffs) is strictly less than that of p's. -/
theorem singleExp_polyTrueDegree_scaledReduction_lt
    (p : MultiPoly 1)
    (h_canon_pos :
      polyTrueDegree
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    polyTrueDegree
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩
          (MultiPoly.sub
            (chainTotalDeriv SingleExpChain p)
            (MultiPoly.mul
              (MultiPoly.const
                (Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)))
              p))))) <
    polyTrueDegree
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) := by
  -- Abbreviate the index and the canonical coeff list via `let`.
  let i : Fin 1 := ⟨0, by omega⟩
  let L_p := polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  -- All MultiPoly 1 entries are y-free at every index iff they're y-free at i.
  -- We use this several times via the helper below.
  -- Step (i): the scaledReduction's lcY is eval-equal to cTD (lcY p) via lemma 2.
  -- Step (ii): mP2PFL eval-faithful for y-free → bridge to Poly.eval.
  -- Step (iii): apply polyCoeffs_eval to get evalCoeffs-equality, then PIT bridge.
  have h_eq1 :
      polyTrueDegree
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY i
            (MultiPoly.sub
              (chainTotalDeriv SingleExpChain p)
              (MultiPoly.mul
                (MultiPoly.const
                  (Real.natCast (MultiPoly.degreeY i p)))
                p))))) =
      polyTrueDegree
        (polyCoeffs (multiPolyToPolyForLex
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)))) := by
    apply polyTrueDegree_eq_of_evalCoeffs_eq
    intro x
    -- Reduce both evalCoeffs ∘ polyCoeffs to Poly.eval ∘ mP2PFL via polyCoeffs_eval.
    rw [polyCoeffs_eval, polyCoeffs_eval]
    -- Both inputs to mP2PFL are y-free (lcY's output is y-free by
    -- degreeY_leadingCoeffY; cTD preserves y-freeness for SingleExp by
    -- degreeY_chainTotalDeriv_zero_of_zero).
    have h_lcY_sr_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (MultiPoly.leadingCoeffY i
            (MultiPoly.sub
              (chainTotalDeriv SingleExpChain p)
              (MultiPoly.mul
                (MultiPoly.const
                  (Real.natCast (MultiPoly.degreeY i p)))
                p))) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact MultiPoly.degreeY_leadingCoeffY i _
    have h_ctd_lcY_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact degreeY_chainTotalDeriv_zero_of_zero
        (MultiPoly.leadingCoeffY i p)
        (MultiPoly.degreeY_leadingCoeffY i p)
    -- Use the bridge to convert Poly.eval to MultiPoly.eval.
    rw [multiPolyToPolyForLex_eval_of_y_free _ h_lcY_sr_free x (fun _ => 0),
        multiPolyToPolyForLex_eval_of_y_free _ h_ctd_lcY_free x (fun _ => 0)]
    -- Apply lemma 2.
    exact leadingCoeffY_scaledReduction_eval_SingleExp p x (fun _ => 0)
  -- Step (iv): bridge (2) — cTD → polyDerivative for y-free.
  have h_eq2 :
      polyTrueDegree
        (polyCoeffs (multiPolyToPolyForLex
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)))) =
      polyTrueDegree
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := by
    have h_lcY_p_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (MultiPoly.leadingCoeffY i p) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact MultiPoly.degreeY_leadingCoeffY i p
    rw [multiPolyToPolyForLex_chainTotalDeriv_of_y_free
          SingleExpChain (MultiPoly.leadingCoeffY i p) h_lcY_p_free]
  -- Step (v): bridge (3) — polyTrueDegree (polyCoeffs ∘ polyDerivative)
  --                       = polyTrueDegree (polyDerivativeCoeffs ∘ polyCoeffs).
  have h_eq3 :
      polyTrueDegree
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) =
      polyTrueDegree (polyDerivativeCoeffs L_p) :=
    polyTrueDegree_polyDerivative_eq_polyDerivativeCoeffs
      (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  -- Step (vi): Phase G strict-decrease.
  have h_lt : polyTrueDegree (polyDerivativeCoeffs L_p) < polyTrueDegree L_p :=
    polyTrueDegree_polyDerivativeCoeffs_lt L_p h_canon_pos
  -- Chain.
  calc polyTrueDegree
          (polyCoeffs (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i
              (MultiPoly.sub
                (chainTotalDeriv SingleExpChain p)
                (MultiPoly.mul
                  (MultiPoly.const
                    (Real.natCast (MultiPoly.degreeY i p)))
                  p)))))
      = polyTrueDegree
          (polyCoeffs (multiPolyToPolyForLex
            (chainTotalDeriv SingleExpChain
              (MultiPoly.leadingCoeffY i p)))) := h_eq1
    _ = polyTrueDegree
          (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
            (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := h_eq2
    _ = polyTrueDegree (polyDerivativeCoeffs L_p) := h_eq3
    _ < polyTrueDegree L_p := h_lt

open MachLib.PolynomialCanonical in
/-- The strict-degree version of `singleExp_polyTrueDegree_scaledReduction_lt`.
Uses the same eval-equality chain (lemma 2 + bridges) but applies
`polyTrueDegreeStrict_eq_of_evalCoeffs_eq` and `polyTrueDegreeStrict_polyDerivativeCoeffs_lt`
to handle the canonically-constant-leading subcase as well: scaledReduction
makes a constant nonzero leading coefficient become canonically zero, so
the strict degree drops 1 → 0. -/
theorem singleExp_polyTrueDegreeStrict_scaledReduction_lt
    (p : MultiPoly 1)
    (h_strict_pos :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    polyTrueDegreeStrict
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩
          (MultiPoly.sub
            (chainTotalDeriv SingleExpChain p)
            (MultiPoly.mul
              (MultiPoly.const
                (Real.natCast (MultiPoly.degreeY ⟨0, by omega⟩ p)))
              p))))) <
    polyTrueDegreeStrict
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) := by
  let i : Fin 1 := ⟨0, by omega⟩
  let L_p := polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  -- Mirror of the non-strict proof, using the strict bridges throughout.
  have h_eq1 :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY i
            (MultiPoly.sub
              (chainTotalDeriv SingleExpChain p)
              (MultiPoly.mul
                (MultiPoly.const
                  (Real.natCast (MultiPoly.degreeY i p)))
                p))))) =
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)))) := by
    apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
    intro x
    rw [polyCoeffs_eval, polyCoeffs_eval]
    have h_lcY_sr_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (MultiPoly.leadingCoeffY i
            (MultiPoly.sub
              (chainTotalDeriv SingleExpChain p)
              (MultiPoly.mul
                (MultiPoly.const
                  (Real.natCast (MultiPoly.degreeY i p)))
                p))) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact MultiPoly.degreeY_leadingCoeffY i _
    have h_ctd_lcY_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact degreeY_chainTotalDeriv_zero_of_zero
        (MultiPoly.leadingCoeffY i p)
        (MultiPoly.degreeY_leadingCoeffY i p)
    rw [multiPolyToPolyForLex_eval_of_y_free _ h_lcY_sr_free x (fun _ => 0),
        multiPolyToPolyForLex_eval_of_y_free _ h_ctd_lcY_free x (fun _ => 0)]
    exact leadingCoeffY_scaledReduction_eval_SingleExp p x (fun _ => 0)
  have h_eq2 :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (chainTotalDeriv SingleExpChain
            (MultiPoly.leadingCoeffY i p)))) =
      polyTrueDegreeStrict
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := by
    have h_lcY_p_free :
        ∀ j : Fin 1, MultiPoly.degreeY j
          (MultiPoly.leadingCoeffY i p) = 0 := by
      intro j
      have hj_eq_i : j = i := Subsingleton.elim _ _
      rw [hj_eq_i]
      exact MultiPoly.degreeY_leadingCoeffY i p
    rw [multiPolyToPolyForLex_chainTotalDeriv_of_y_free
          SingleExpChain (MultiPoly.leadingCoeffY i p) h_lcY_p_free]
  have h_eq3 :
      polyTrueDegreeStrict
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) =
      polyTrueDegreeStrict (polyDerivativeCoeffs L_p) :=
    polyTrueDegreeStrict_polyDerivative_eq_polyDerivativeCoeffs
      (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  have h_lt :
      polyTrueDegreeStrict (polyDerivativeCoeffs L_p) <
      polyTrueDegreeStrict L_p :=
    polyTrueDegreeStrict_polyDerivativeCoeffs_lt L_p h_strict_pos
  calc polyTrueDegreeStrict
          (polyCoeffs (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i
              (MultiPoly.sub
                (chainTotalDeriv SingleExpChain p)
                (MultiPoly.mul
                  (MultiPoly.const
                    (Real.natCast (MultiPoly.degreeY i p)))
                  p)))))
      = polyTrueDegreeStrict
          (polyCoeffs (multiPolyToPolyForLex
            (chainTotalDeriv SingleExpChain
              (MultiPoly.leadingCoeffY i p)))) := h_eq1
    _ = polyTrueDegreeStrict
          (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
            (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := h_eq2
    _ = polyTrueDegreeStrict (polyDerivativeCoeffs L_p) := h_eq3
    _ < polyTrueDegreeStrict L_p := h_lt

open MachLib.PolynomialCanonical in
/-- **SingleExp-specific closure** at the canonical `MultiPoly 1` shape.
The lex strict-decrease for `scaledReduction` on PfaffianFn
`⟨1, SingleExpChain, p⟩` at `c = degreeY 0 p`. Uses the strict
canonical degree, so the canonically-constant-nonzero leading
coefficient subcase (`polyTrueDegree = 0` but canonically nonzero)
is handled: scaledReduction makes the leading canonically zero,
strict degree drops 1 → 0. -/
theorem singleExp_h_bridge_closure (p : MultiPoly 1)
    (h_strict_pos :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    lexLT
      (lexMeasure
        ((⟨1, SingleExpChain, p⟩ : PfaffianFn).scaledReduction
          (Real.natCast
            (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1)) rfl)
      (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl) := by
  refine Or.inr ⟨?_, ?_⟩
  · -- First-component equality.
    show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1)
          (MultiPoly.sub
            (chainTotalDeriv SingleExpChain p)
            (MultiPoly.mul
              (MultiPoly.const
                (Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p)))
              p)) =
         MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    change Nat.max
      (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1)
        (chainTotalDeriv SingleExpChain p))
      (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1)
        (MultiPoly.mul
          (MultiPoly.const
            (Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p)))
          p)) =
        MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    rw [degreeY_chainTotalDeriv_eq_SingleExp p]
    show Nat.max
      (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p)
      (0 + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p) =
        MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    rw [Nat.zero_add]
    exact Nat.max_eq_right (Nat.le_refl _)
  · -- Second-component strict-decrease (strict version).
    exact singleExp_polyTrueDegreeStrict_scaledReduction_lt p h_strict_pos

open MachLib.PolynomialCanonical in
/-- **Closed SingleExp ReduceStep constructor.** Produces a
`PfaffianFn.ReduceStep` for the SingleExp shape `⟨1, SingleExpChain, p⟩`
*without* the external `h_bridge` hypothesis.

Preconditions:
- `h_pos`: positive y-degree (first lex component > 0).
- `h_strict_pos`: the leading y-coefficient is canonically nonzero
  (`polyTrueDegreeStrict > 0`, which is equivalent to
  `¬ CanonicallyZero (polyCoeffs (mP2PFL (lcY 0 p)))`).

Under the strict-degree lex measure, this constructor handles
*both*:
- The canonically-nonzero positive-degree case (the original Phase H
  path).
- The canonically-constant-nonzero case (the subcase that the
  non-strict measure missed): scaledReduction kills the leading
  canonically, strict degree drops 1 → 0.

The remaining residue — `polyTrueDegreeStrict = 0`, i.e. the leading
y-coefficient is *canonically zero* (dead AST term) — needs a
separate canonical-trim operation to drop the formal y-degree at the
AST level. That is the genuinely-corner case (a polynomial with a
phantom leading y-term that always evaluates to 0), and is followup
framework work. -/
noncomputable def PfaffianFn.singleExp_reduceStep_closed (p : MultiPoly 1)
    (h_pos : (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1 > 0)
    (h_strict_pos :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0) :
    PfaffianFn.ReduceStep (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl :=
  PfaffianFn.singleExp_reduceStep _ rfl h_pos
    (singleExp_h_bridge_closure p h_strict_pos)

/-! ## SingleExp canonical-trim ReduceStep

Handles the residual `polyTrueDegreeStrict = 0` corner — the
canonically-zero leading y-coefficient case (dead AST term). When
`(yCoeffsAt 0 p).getLast` evaluates to 0 at every point,
`dropLeadingY p` is eval-equivalent to `p` and has strictly lower
formal `degreeY 0`. This satisfies the lex strict-decrease in
its first component (Case A), and the trim step has a no-Rolle-
counter witness via the new `IsKhovanskiiReducible.trim`
constructor. -/

open MachLib.MultiPolyReconstruct in
/-- **SingleExp canonical-trim ReduceStep.** When `degreeY 0 p > 0`
and the last entry of `yCoeffsAt 0 p` is canonically zero, produces
a ReduceStep that trims the dead leading term, dropping formal
`degreeY` by ≥ 1. The witness uses the new `trim` constructor of
`IsKhovanskiiReducible`. -/
noncomputable def PfaffianFn.singleExp_canonicalTrim_step (p : MultiPoly 1)
    (h_pos : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p > 0)
    (h_canonical_zero :
      ∀ (h_ne : MachLib.MultiPolyMod.MultiPoly.yCoeffsAt
                  (⟨0, by omega⟩ : Fin 1) p ≠ [])
        (x : Real) (env : Fin 1 → Real),
        MultiPoly.eval
          ((MachLib.MultiPolyMod.MultiPoly.yCoeffsAt
              (⟨0, by omega⟩ : Fin 1) p).getLast h_ne)
          x env = 0) :
    PfaffianFn.ReduceStep (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl where
  result := ⟨1, SingleExpChain, dropLeadingY p⟩
  result_hN := rfl
  counter := 0
  lex_decrease := by
    -- Case A: first lex component strictly drops.
    refine Or.inl ?_
    show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) (dropLeadingY p) <
         MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p
    exact degreeY_dropLeadingY_lt p h_pos
  witness := by
    have h_ne :
        MachLib.MultiPolyMod.MultiPoly.yCoeffsAt
          (⟨0, by omega⟩ : Fin 1) p ≠ [] :=
      MachLib.MultiPolyMod.MultiPoly.yCoeffsAt_nonempty _ p
    refine PfaffianFn.IsKhovanskiiReducible.trim
      (⟨1, SingleExpChain, p⟩ : PfaffianFn)
      (⟨1, SingleExpChain, dropLeadingY p⟩ : PfaffianFn)
      (dropLeadingY p) 0 ?_ ?_
    · -- h_eval: f.eval x = trimmed.eval x for every x.
      intro x
      show MultiPoly.eval p x
            ((⟨1, SingleExpChain, p⟩ : PfaffianFn).chain.chainValues x) =
           MultiPoly.eval (dropLeadingY p) x
            ((PfaffianFn.mk (⟨1, SingleExpChain, p⟩ : PfaffianFn).n
                (⟨1, SingleExpChain, p⟩ : PfaffianFn).chain
                (dropLeadingY p)).chain.chainValues x)
      have h_canon := h_canonical_zero h_ne
      rw [eval_dropLeadingY_of_last_canonically_zero p h_ne h_canon x _]
    · exact PfaffianFn.IsKhovanskiiReducible.refl _

end ChainExp2PathC
end MachLib
