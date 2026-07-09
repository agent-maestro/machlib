import MachLib.ChainExp2ExplicitFinal

/-!
# The explicit chain-2 Khovanskii bound as a TOOL

`chain2_khovanskii_bound_explicit` (`ChainExp2ExplicitFinal`) states the bound in terms of `innerRank`,
which is *noncomputable* (it decides canonical-zero of coefficients). This file turns the theorem into a
usable instrument: a bound stated purely in the **computable syntactic degrees** `degreeX`, `degreeY₀`,
`degreeY₁`, so a concrete chain-2 EML kernel gets a concrete, machine-checked zero/oscillation bound.

  * `innerRank_le_syntactic`       — `innerRank (degreeX p+2) p ≤ degreeY₀·(degreeX+3) + (degreeX+2)`,
                                     over-bounding the exact inner rank by the syntactic degrees
                                     (`cdegY0 ≤ degreeY₀`, `b ≤ degreeX+2`).
  * `khovBound p`                  — the computable bound functional (`invPhi` at the syntactic degrees).
  * `chain2_khovanskii_bound_syntactic` — `zeros.length ≤ khovBound p` (via `invPhi_mono_ir`).
  * worked kernels                 — concrete `khovBound = N` by `decide`, and the `zeros.length ≤ N`
                                     corollary for a real transcendental like `e^(e^x) − x·e^x`.

**What this delivers.** For a chain-2 kernel (interpreting `y₀ = e^x`, `y₁ = e^(e^x)` — the iterated-exp
tower), `khovBound p` is an explicit, verified ceiling on how many times the transcendental crosses zero
on any interval where it is not identically zero. That is a bound on the number of sign changes /
oscillations of the expression — directly a safety-relevant quantity for a control or response signal.

The bound is honest: it is exponential in `degreeY₁` (the descent yields no better), so the numbers are
crude — but they are *explicit* and *proven*, which nothing before this session's chain-2 result could
produce for an iterated-exponential expression.
-/

namespace MachLib.ChainExp2NoZeros

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2PolyMultRolle
open MachLib.ChainExp2Bound
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2PhantomDescent
open MachLib.ChainExp2Capstone
open MachLib.ChainExp2Explicit MachLib.ExplicitBound

/-- **Syntactic over-bound of the inner rank.** `innerRank (degreeX p + 2) p` is bounded by a function of
the computable degrees only: `cdegY0(lcY₁ p) ≤ degreeY₀ p` (`cdegY0_lcY1_le_degreeY0`) and
`b(p) ≤ degreeX p + 2` (the bridge `singleExpMeasureCanon_snd_le`). -/
theorem innerRank_le_syntactic (p : MultiPoly 2) :
    innerRank (MultiPoly.degreeX p + 2) p
      ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p * (MultiPoly.degreeX p + 2 + 1)
          + (MultiPoly.degreeX p + 2) := by
  unfold innerRank
  exact Nat.add_le_add
    (Nat.mul_le_mul (cdegY0_lcY1_le_degreeY0 p) (Nat.le_refl _))
    (singleExpMeasureCanon_snd_le p)

/-- The **computable** explicit-bound functional: `invPhi` at the syntactic degrees of `p`. Every
argument is a structural recursion on the AST / `Nat`, so `khovBound p` reduces to a numeral for any
concrete kernel (even though the `Real` coefficients are noncomputable — the degree functions never
inspect them). -/
def khovBound (p : MultiPoly 2) : Nat :=
  invPhi (MultiPoly.degreeX p + 2) (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
    (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p * (MultiPoly.degreeX p + 2 + 1)
      + (MultiPoly.degreeX p + 2))
    (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)

/-- **The tool.** The number of zeros of `chain2Fn p` on any `(a,b)` where it is not identically zero is
`≤ khovBound p` — an explicit ceiling computed from the kernel's syntactic degrees alone. -/
theorem chain2_khovanskii_bound_syntactic (p : MultiPoly 2) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chain2Fn p).eval z ≠ 0)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) :
    zeros.length ≤ khovBound p := by
  have h := chain2_khovanskii_bound_explicit (MultiPoly.degreeX p) a b hab p (Nat.le_refl _)
    hne zeros hnd hz
  exact Nat.le_trans h (invPhi_mono_ir _ _ _ (innerRank_le_syntactic p))

/-! ## Worked kernels

Interpreting `y₀ = e^x`, `y₁ = e^(e^x)`. Each kernel gets an explicit, machine-checked zero bound. -/

/-- `e^(e^x) − x·e^x`. A genuine chain-2 transcendental that does cross zero. -/
def kernelExpMinusXExp : MultiPoly 2 :=
  MultiPoly.sub (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))
    (MultiPoly.mul MultiPoly.varX (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))

/-- `x·e^(e^x) − e^(2x)` (with `e^(2x) = (e^x)²`). Higher inner degree ⇒ larger bound. -/
def kernelXExpMinusExp2 : MultiPoly 2 :=
  MultiPoly.sub (MultiPoly.mul MultiPoly.varX (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))

/-- The degrees compute: `kernelExpMinusXExp` has `degreeX = 1`, `degreeY₀ = 1`, `degreeY₁ = 1`. -/
example : MultiPoly.degreeX kernelExpMinusXExp = 1
    ∧ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) kernelExpMinusXExp = 1
    ∧ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) kernelExpMinusXExp = 1 := by decide

/-- **Explicit zero bound: `e^(e^x) − x·e^x` crosses zero at most 47 times on any interval.** -/
theorem khovBound_kernelExpMinusXExp : khovBound kernelExpMinusXExp = 47 := by decide

/-- **Explicit zero bound: `x·e^(e^x) − e^(2x)` crosses zero at most 71 times on any interval.** -/
theorem khovBound_kernelXExpMinusExp2 : khovBound kernelXExpMinusExp2 = 71 := by decide

/-- The tool, packaged for `kernelExpMinusXExp`: a fully concrete `zeros.length ≤ 47`. -/
theorem zeros_kernelExpMinusXExp_le (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chain2Fn kernelExpMinusXExp).eval z ≠ 0)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn kernelExpMinusXExp).eval z = 0) :
    zeros.length ≤ 47 :=
  khovBound_kernelExpMinusXExp ▸ chain2_khovanskii_bound_syntactic kernelExpMinusXExp a b hab hne zeros hnd hz

end MachLib.ChainExp2NoZeros
