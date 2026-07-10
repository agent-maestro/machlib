import MachLib.IterExpDepthNExplicit

/-!
# Tower separation via the uniform Khovanskii zero bound (scoping + first brick)

**Goal (the scoped, provable core of "no single operator spans two towers").** The
oscillatory towers (`sin`/`cos`, and the Bessel/Airy/Si/Ci generators) live in a
different Pfaffian chain from the exp–log tower. The honest, machine-checkable
separator is the ZERO COUNT, and it rests on a fact already proved in this library:

  `chainN_khovanskii_bound_explicit` bounds the zeros of an iterated-exp chain
  function of order `m+2` and degree `≤ D` by `Ndep m D` — a bound that depends
  ONLY on the order and degree, **not on the interval `(a,b)`**.

Interval-independence is the whole game. It means an exp-chain function has at most
`Ndep m D` zeros on EVERY interval, hence globally finitely many. Any function that
has, for every `(m, D)`, some interval carrying more than `Ndep m D` distinct zeros
therefore cannot be an exp-chain function of any order/degree. `sin` is exactly such
a function (`sin (k·π) = 0` for every `k`), so `sin` is separated from the exp tower.

## Status

- `IsExpChainFn` — realizability as an iterated-exp chain function (pointwise).
- `not_expChainFn_of_excess_zeros` — **PROVED** here: the general separator. A
  function with the "excess zeros for every `(m,D)`" property is not an exp-chain
  function. Two-line reduction to `chainN_khovanskii_bound_explicit` + `omega`.
- `sin_not_expChainFn` — **STATED**; its one remaining brick is the enumeration
  `sin (k·π) = 0` for `k = 1 … Ndep m D + 1` (from `sin_pi` + `sin_periodic`),
  packaged as the excess-zeros witness. Left as the next step.

## Scope (honest)

This separates the OSCILLATORY towers from the ITERATED-EXP tower by zero count — the
rigorous form of "trig has infinite real EML cost". It is NOT the full
differential-algebraic independence of `{T_F, T_Γ, T_W}` under all 23 operators
(that needs differential-Galois / Hölder-type machinery Mathlib lacks). The
`EMLTree` version (`eml_eval_boundedZeros_unconditional`, which adds `log`/`recip`
with `LogArgPos` domain hypotheses) extends the same argument to the full exp–log
tower; that is the natural follow-on.
-/

namespace MachLib

open MachLib.Real
open MachLib.IterExpDepthN
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly

/-- `g` is realizable as an iterated-exp chain function: it equals, pointwise, the
evaluation of some `chainNFn (m+2) p` whose polynomial has X- and Y-degrees `≤ D`. -/
def IsExpChainFn (g : Real → Real) : Prop :=
  ∃ (m : Nat) (p : MultiPoly (m + 2)) (D : Nat),
    MultiPoly.degreeX p ≤ D ∧ (∀ i : Fin (m + 2), MultiPoly.degreeY i p ≤ D) ∧
    ∀ x : Real, g x = (chainNFn (m + 2) p).eval x

/-- **The general separator (PROVED).** If for every order/degree budget `(m, D)`
there is an interval on which `g` is not identically zero yet carries a nodup list
of MORE than `Ndep m D` zeros, then `g` is not an iterated-exp chain function of any
order or degree. Direct contradiction with the interval-uniform Khovanskii bound. -/
theorem not_expChainFn_of_excess_zeros (g : Real → Real)
    (hexcess : ∀ (m D : Nat), ∃ (a b : Real) (zeros : List Real),
        a < b ∧ zeros.Nodup ∧
        (∀ z ∈ zeros, a < z ∧ z < b ∧ g z = 0) ∧
        (∃ z, a < z ∧ z < b ∧ g z ≠ 0) ∧
        Ndep m D < zeros.length) :
    ¬ IsExpChainFn g := by
  rintro ⟨m, p, D, hdX, hdY, hgeq⟩
  obtain ⟨a, b, zeros, hab, hnd, hzero, ⟨zn, hzna, hznb, hgzn⟩, hcard⟩ := hexcess m D
  -- transfer `g`'s zeros / non-vanishing to the chain function via the pointwise equality
  have hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z ≠ 0 :=
    ⟨zn, hzna, hznb, by rw [← hgeq]; exact hgzn⟩
  have hzchain : ∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z = 0 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hzero z hz
    exact ⟨h1, h2, by rw [← hgeq]; exact h3⟩
  have hbound :=
    chainN_khovanskii_bound_explicit m p D a b hab hdX hdY hne zeros hnd hzchain
  -- `Ndep m D < zeros.length ≤ Ndep m D` is impossible
  omega

/-! ## The `sin` target — reduced to one enumeration obligation

`sin` is the canonical oscillatory generator. It is separated from the exp tower
the moment we exhibit, for each budget `(m, D)`, an interval carrying more than
`Ndep m D` of its zeros. The reduction below is unconditional; the remaining brick
`SinExcessZeros` is the concrete witness `{π, 2π, …, (Ndep m D + 1)·π} ⊂ (0, …)`,
each a zero by `sin (k·π) = 0` (induction from `sin_pi` via `sin_add`), pairwise
distinct, with `sin (π/2) = 1 ≠ 0` for non-vanishing. That is the next step. -/

/-- The concrete excess-zeros obligation for `sin`. -/
def SinExcessZeros : Prop :=
  ∀ (m D : Nat), ∃ (a b : Real) (zeros : List Real),
    a < b ∧ zeros.Nodup ∧
    (∀ z ∈ zeros, a < z ∧ z < b ∧ sin z = 0) ∧
    (∃ z, a < z ∧ z < b ∧ sin z ≠ 0) ∧
    Ndep m D < zeros.length

/-- **`sin` is separated from the exp tower, modulo the enumeration witness.** Once
`SinExcessZeros` is discharged, `sin` is not an iterated-exp chain function of any
order or degree — the rigorous form of "no exp–log operator computes `sin`". -/
theorem sin_not_expChainFn (h : SinExcessZeros) : ¬ IsExpChainFn sin :=
  not_expChainFn_of_excess_zeros sin h

end MachLib
