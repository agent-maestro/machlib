import MachLib.Basic
import MachLib.Ring
import MachLib.MultiPoly
import MachLib.FieldLemmas

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
open MachLib.MultiPolyMod

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

/-! ## Brick A-3-ii — the clearing construction (`clearTop` + eval bridge)

Generalises `MachLib.clearNum` from the specific `1/x` (base variable `x` as
denominator) to a **general denominator `v`** (a `MultiPoly N`, a value of the
restricted chain). `clearTop v p` clears the top reciprocal variable
`y_N = 1/v` of a `MultiPoly (N+1)`, producing a `MultiPoly N` over the restricted
chain. The eval bridge is `clearTop_eval` below — the `fp·fD = fP` the
reduction (A-3-i) consumes, with `fD = v^d` (`d = degreeY_N p`). -/

variable {N : Nat}

/-- `v^k` as a `MultiPoly N` (iterated `v`) — the clearing-power carrier, the
`MultiPoly` analog of `clearNum`'s `polyVarPow`. -/
noncomputable def mpolyPow (v : MultiPoly N) : Nat → MultiPoly N
  | 0 => MultiPoly.const 1
  | k + 1 => MultiPoly.mul v (mpolyPow v k)

theorem mpolyPow_eval_zero (v : MultiPoly N) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (mpolyPow v 0) x env = 1 := rfl

theorem mpolyPow_eval_succ (v : MultiPoly N) (k : Nat) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (mpolyPow v (k + 1)) x env
      = MultiPoly.eval v x env * MultiPoly.eval (mpolyPow v k) x env := rfl

/-- `v^(a+b) = v^a · v^b` at the evaluation level. -/
theorem mpolyPow_eval_add (v : MultiPoly N) (a b : Nat) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (mpolyPow v (a + b)) x env
      = MultiPoly.eval (mpolyPow v a) x env * MultiPoly.eval (mpolyPow v b) x env := by
  induction b with
  | zero =>
    show MultiPoly.eval (mpolyPow v a) x env
        = MultiPoly.eval (mpolyPow v a) x env * MultiPoly.eval (mpolyPow v 0) x env
    rw [mpolyPow_eval_zero]; mach_ring
  | succ b ih =>
    show MultiPoly.eval (mpolyPow v ((a + b) + 1)) x env
        = MultiPoly.eval (mpolyPow v a) x env * MultiPoly.eval (mpolyPow v (b + 1)) x env
    rw [mpolyPow_eval_succ, ih, mpolyPow_eval_succ]; mach_ring

/-- Padding algebra for the shared-degree `add` case (the `MultiPoly` analog of
`pad_combine_add`). -/
theorem mpad_combine_add (v : MultiPoly N) (x : Real) (env : Fin N → Real)
    (m np nq : Nat) (A B : Real) (hp : np ≤ m) (hq : nq ≤ m) :
    MultiPoly.eval (mpolyPow v (m - np)) x env * (MultiPoly.eval (mpolyPow v np) x env * A)
      + MultiPoly.eval (mpolyPow v (m - nq)) x env * (MultiPoly.eval (mpolyPow v nq) x env * B)
      = MultiPoly.eval (mpolyPow v m) x env * (A + B) := by
  have h1 : MultiPoly.eval (mpolyPow v (m - np)) x env * MultiPoly.eval (mpolyPow v np) x env
      = MultiPoly.eval (mpolyPow v m) x env := by
    rw [← mpolyPow_eval_add, Nat.sub_add_cancel hp]
  have h2 : MultiPoly.eval (mpolyPow v (m - nq)) x env * MultiPoly.eval (mpolyPow v nq) x env
      = MultiPoly.eval (mpolyPow v m) x env := by
    rw [← mpolyPow_eval_add, Nat.sub_add_cancel hq]
  rw [← mul_assoc, ← mul_assoc, h1, h2]; mach_ring

/-- Padding algebra for the shared-degree `sub` case. -/
theorem mpad_combine_sub (v : MultiPoly N) (x : Real) (env : Fin N → Real)
    (m np nq : Nat) (A B : Real) (hp : np ≤ m) (hq : nq ≤ m) :
    MultiPoly.eval (mpolyPow v (m - np)) x env * (MultiPoly.eval (mpolyPow v np) x env * A)
      - MultiPoly.eval (mpolyPow v (m - nq)) x env * (MultiPoly.eval (mpolyPow v nq) x env * B)
      = MultiPoly.eval (mpolyPow v m) x env * (A - B) := by
  have h1 : MultiPoly.eval (mpolyPow v (m - np)) x env * MultiPoly.eval (mpolyPow v np) x env
      = MultiPoly.eval (mpolyPow v m) x env := by
    rw [← mpolyPow_eval_add, Nat.sub_add_cancel hp]
  have h2 : MultiPoly.eval (mpolyPow v (m - nq)) x env * MultiPoly.eval (mpolyPow v nq) x env
      = MultiPoly.eval (mpolyPow v m) x env := by
    rw [← mpolyPow_eval_add, Nat.sub_add_cancel hq]
  rw [← mul_assoc, ← mul_assoc, h1, h2]; mach_ring

/-- **A-3-ii — the numerator.** Clear the top reciprocal variable `y_N = 1/v` of
a `MultiPoly (N+1)` to a `MultiPoly N` over the restricted chain, denominator
`v`. Lower vars project (dropLastY-style); the top var clears to `const 1`
(`y_N·v = 1`); the clearing power is `degreeY_N`. `mul` adds it, `add`/`sub`
share it (pad by `v^(m−dᵢ)`). -/
noncomputable def clearTop (v : MultiPoly N) : MultiPoly (N + 1) → MultiPoly N
  | MultiPoly.const c => MultiPoly.const c
  | MultiPoly.varX => MultiPoly.varX
  | MultiPoly.varY j => if h : j.val < N then MultiPoly.varY ⟨j.val, h⟩ else MultiPoly.const 1
  | MultiPoly.add p q =>
      MultiPoly.add
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)) (clearTop v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)) (clearTop v q))
  | MultiPoly.sub p q =>
      MultiPoly.sub
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)) (clearTop v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)) (clearTop v q))
  | MultiPoly.mul p q => MultiPoly.mul (clearTop v p) (clearTop v q)

/-- **A-3-ii — eval bridge.** On the restricted-chain env `env` and full env
`envFull` (agreeing on the lower slots, with `envFull` at the top `= 1/eval v`),
`clearTop v p = v^(degreeY_N p) · p`. This is the `fp·fD = fP` the reduction
(A-3-i) consumes, `fD = v^d > 0` on the domain (`hvne` from `v > 0`). The
concrete-base analog of `clearNum_eval`. -/
theorem clearTop_eval (v : MultiPoly N) (x : Real) (env : Fin N → Real)
    (envFull : Fin (N + 1) → Real)
    (hlow : ∀ (j : Fin (N + 1)) (hj : j.val < N), envFull j = env ⟨j.val, hj⟩)
    (htop : envFull ⟨N, Nat.lt_succ_self N⟩ = 1 / MultiPoly.eval v x env)
    (hvne : MultiPoly.eval v x env ≠ 0)
    (p : MultiPoly (N + 1)) :
    MultiPoly.eval (clearTop v p) x env
      = MultiPoly.eval (mpolyPow v (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)) x env
        * MultiPoly.eval p x envFull := by
  induction p with
  | const c =>
    show MultiPoly.eval (MultiPoly.const c) x env = MultiPoly.eval (mpolyPow v 0) x env * c
    rw [mpolyPow_eval_zero]; show c = 1 * c; mach_ring
  | varX =>
    show MultiPoly.eval MultiPoly.varX x env = MultiPoly.eval (mpolyPow v 0) x env * x
    rw [mpolyPow_eval_zero]; show x = 1 * x; mach_ring
  | varY j =>
    by_cases h : j.val < N
    · have hval : j.val ≠ N := Nat.ne_of_lt h
      have hne : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) ≠ j :=
        fun heq => hval (congrArg Fin.val heq).symm
      have hdeg : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (MultiPoly.varY j) = 0 := by
        show (if (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = j then (1 : Nat) else 0) = 0
        rw [if_neg hne]
      have hclear : clearTop v (MultiPoly.varY j) = MultiPoly.varY ⟨j.val, h⟩ := by
        show (if h' : j.val < N then MultiPoly.varY ⟨j.val, h'⟩ else MultiPoly.const 1)
            = MultiPoly.varY ⟨j.val, h⟩
        rw [dif_pos h]
      rw [hclear, hdeg, mpolyPow_eval_zero]
      show env ⟨j.val, h⟩ = 1 * MultiPoly.eval (MultiPoly.varY j) x envFull
      rw [show MultiPoly.eval (MultiPoly.varY j) x envFull = envFull j from rfl, hlow j h]
      mach_ring
    · have hjN : j.val = N := Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) (Nat.not_lt.mp h)
      have heq : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = j := Fin.ext hjN.symm
      have hdeg : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (MultiPoly.varY j) = 1 := by
        show (if (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = j then (1 : Nat) else 0) = 1
        rw [if_pos heq]
      have hclear : clearTop v (MultiPoly.varY j) = MultiPoly.const 1 := by
        show (if h' : j.val < N then MultiPoly.varY ⟨j.val, h'⟩ else MultiPoly.const 1)
            = MultiPoly.const 1
        rw [dif_neg h]
      rw [hclear, hdeg, mpolyPow_eval_succ, mpolyPow_eval_zero]
      show (1 : Real) = MultiPoly.eval v x env * 1 * MultiPoly.eval (MultiPoly.varY j) x envFull
      rw [show MultiPoly.eval (MultiPoly.varY j) x envFull = envFull j from rfl, ← heq, htop,
        mul_one_ax]
      exact (mul_div_cancel_left hvne).symm
  | add p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.add
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)) (clearTop v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)) (clearTop v q))) x env
        = MultiPoly.eval (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
            (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q))) x env
          * MultiPoly.eval (MultiPoly.add p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq]
    exact mpad_combine_add v x env _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | sub p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.sub
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)) (clearTop v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
              (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)
            - MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)) (clearTop v q))) x env
        = MultiPoly.eval (mpolyPow v (Nat.max (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p)
            (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q))) x env
          * MultiPoly.eval (MultiPoly.sub p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq]
    exact mpad_combine_sub v x env _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | mul p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.mul (clearTop v p) (clearTop v q)) x env
        = MultiPoly.eval (mpolyPow v (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ p
            + MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q)) x env
          * MultiPoly.eval (MultiPoly.mul p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq, mpolyPow_eval_add]; mach_ring

end PfaffianExpRecip
end MachLib
