import MachLib.Basic
import MachLib.Ring

/-!
# Reciprocal-top descent step — Brick A-3 (crux of the extended descent)

Stripping a **top reciprocal level** from an `IsExpOrRecipChain` (see
`MachLib.PfaffianExpRecipClass`). This is the piece the general
`sin_not_in_eml_any_depth` retirement turns on, and it is where the extended
descent departs from the existing exp descent.

## The key structural fact (why the reciprocal top is *easier* than the exp top)

The existing exp-top step (`pfaffian_bound_step_hnz_gen_IF`) builds an
integrating factor `vehExpo` — the "divide out the top exponential" trick — valid
because an exp top's relation is *linear* (`G·yᵢ`). A reciprocal top's relation is
degree-2 (`G·yᵢ²`), so `vehExpo` does not apply. But it does not need to:

the top generator is `y_N = 1/v` with `v` a value of the *restricted* chain. A
`MultiPoly` target `p` is a polynomial in `y_N`, hence `p = P / v^d` with
`P = Σⱼ cⱼ·v^{d−j}` a polynomial over the restricted chain (`d = degreeY_N p`,
using `y_N·v = 1`). On the EML domain `v > 0`, so `p z = 0 ⇔ P z = 0`: the
reciprocal top **clears straight to the sub-chain**, reducing to the depth
descent's induction hypothesis with no analytic step. `clearNum` /
`reciprocalPfaffian_zero_count` (Bricks 3b/3c) are the concrete-base incarnation
of this same clearing.

## Bricks
- **A-3-i (this):** the zero-count *reduction* — given the clearing bridge
  `fp·fD = fP` (`fD = v^d > 0`), bound `fp`'s zeros by `fP`'s. The logical core.
- **A-3-ii (next):** the clearing *construction* — `clearTop v : MultiPoly (N+1)
  → MultiPoly N` (generalising `clearNum` from `1/x` to a general denominator
  `v`) and its eval bridge `pfaffianChainFn c p · (eval v)^d =
  pfaffianChainFn (chainRestrict c) (clearTop v p)`.
- **A-3-iii:** package A-3-i∘A-3-ii into the reciprocal-top step consuming the
  restricted-chain IH.
-/

namespace MachLib
namespace PfaffianExpRecip

open MachLib.Real

/-- **A-3-i — reciprocal-top zero reduction.** If the target `fp` (using the top
reciprocal `y_N = 1/v`) relates to a cleared numerator `fP` over the restricted
chain by `fp·fD = fP` on `(a,b)` (`fD = v^d`), then every zero of `fp` on `(a,b)`
is a zero of `fP`, so `fp`'s zero-count is bounded by `fP`'s. No integrating
factor — the reciprocal top clears to the sub-chain directly.

Only the forward bridge is needed for the count bound (`fp z = 0 → fP z = 0`),
so `fD`'s sign is irrelevant here; the *faithfulness* direction (`fP z = 0 →
fp z = 0`, i.e. clearing introduces no spurious zeros) is what will use `v^d > 0`
in A-3-ii, but it is not needed to bound the count. -/
theorem recip_top_zero_reduction
    (fp fP fD : Real → Real) (a b : Real) (M : Nat)
    (hbridge : ∀ z : Real, a < z → z < b → fp z * fD z = fP z)
    (hPbound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ fP z = 0) → zeros.length ≤ M) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ fp z = 0) → zeros.length ≤ M := by
  intro Z hnd hZ
  apply hPbound Z hnd
  intro z hz
  obtain ⟨ha, hb, hfp⟩ := hZ z hz
  refine ⟨ha, hb, ?_⟩
  rw [← hbridge z ha hb, hfp, zero_mul]

end PfaffianExpRecip
end MachLib
