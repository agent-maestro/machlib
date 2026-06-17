import MachLib.KhovanskiiReduction
import MachLib.IterExpChain

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

/-! ## Status

**Shipped in this commit**: `degreeY_chainTotalDeriv_zero_of_zero` —
chainTotalDeriv preserves y_0-freeness on SingleExpChain (lemma 3a).

**Next concrete steps**:
- `chainTotalDeriv_y_free_eq_polyDerivative_x`: for y_0-free p,
  chainTotalDeriv equals partial_x p (eval-level).
- `degreeX_chainTotalDeriv_lt_after_simplify_y_free`: lemma 3 proper.
- Then lemmas 1 (leadingCoeffY of chainTotalDeriv) and 2 (cancellation
  at scaledReduction).

Each is concrete proof work, ~50-100 lines each. -/

end ChainExp2PathC
end MachLib
