import MachLib.KhovanskiiReduction
import MachLib.IterExpChain
import MachLib.PfaffianFnBound

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

/-! ## Status of full lemma 1

The `_add_lt` sub-case above shows the proof structure works end-to-end:
- `degreeY_chainTotalDeriv_eq_SingleExp` lets us know the same degree
  comparison holds after chainTotalDeriv.
- The leadingCoeffY definition's if-chain reduces via `simp` once the
  comparison is established.
- The remaining algebra is one rewrite + IH.

The remaining sub-cases (add `dp = dq`, add `dp > dq`, sub mirror, mul
Leibniz) follow the same skeleton. Each is ~40 lines of structurally
similar work; the mul case is the most intricate because both
chainTotalDeriv summands have the same degree, so leadingCoeffY
distributes over their add and IH applies to each factor — but it's
mechanical given the `_add_lt` template.

The new `mach_leading_coeff_y` tactic (in `Tactic/LeadingCoeffY.lean`)
will close the leadingCoeffY case-analysis steps inside these sub-cases
in one call, so completing the proof is the next session's specific
work. mach_ring v2.5 (with omega + ac_rfl phases) closes the algebra
once the leadingCoeffY reduction has happened.

## Status

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

**Remaining for Step 3b**:
- **Lemma 1** proper — `leadingCoeffY_chainTotalDeriv_SingleExp`: the
  d·a_d emergence identity at the leading coefficient. ~100-150 lines
  of structural induction with mul-case Leibniz interaction.
- **Lemma 2** — `leadingCoeffY_scaledReduction_SingleExp`: the d·a_d
  cancellation, mechanical given lemma 1. ~30-50 lines.
- **Step 3b assembly**: combine lemmas 1, 2, 3 to get strict-decrease
  at the leading coefficient (for the lex measure's second component). -/

end ChainExp2PathC
end MachLib
