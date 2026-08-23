import MachLib.BipevClearedDeriv

/-!
# Elimination: killing the top term

Step 2 of the three `BipevExpDeriv` listed. With `BipevClearedDeriv` having made the differentiated
relation's coefficients polynomial, this is **coefficient algebra** rather than analysis — which was
the point of clearing denominators there.

## The combination

Given the relation `Σ pⱼ yʲ = 0` and the cleared differentiated relation `Σ cⱼ yʲ = 0` (where
`cⱼ = Q²pⱼ' + j·D·pⱼ`), the combination `c_m·(relation) − p_m·(differentiated)` has coefficients

```
c_m·pⱼ − p_m·cⱼ  =  Q²·(p_m'·pⱼ − p_m·pⱼ') + (m−j)·D·p_m·pⱼ
```

which is `Q²` times the coefficient `CRUX.md` §1 derives — as it must be, since `cⱼ` already carries
one factor of `Q²`. At `j = m` it is `c_m·p_m − p_m·c_m`, which vanishes: **the top term is killed**,
and that is the whole content of the step.

## What is proved here and what is not

`bipev_elim` is an identity, not an implication: it computes the combination's value as
`c_m·(relation) − p_m·(differentiated)` for *any* lists of matching length. The vanishing corollary
follows in one line. `bipev_concat` then exhibits the degree drop — a relation whose top coefficient
evaluates to zero everywhere agrees with its own truncation.

**Still not built:** minimal degree, which is the remaining step and the only one needing genuine
well-founded recursion rather than a fuel budget.
-/

namespace MachLib

open Real

/-! ## The eliminated coefficient family -/

/-- `c_m·pⱼ − p_m·cⱼ`, coefficientwise. The two lists are consumed in lockstep; a length mismatch
returns `[]` and is excluded by hypothesis at every use. -/
noncomputable def elimCoeffs (top topD : List Real) :
    List (List Real) → List (List Real) → List (List Real)
  | L :: Ls, C :: Cs => psub (pmul topD L) (pmul top C) :: elimCoeffs top topD Ls Cs
  | _,       _       => []

/-- **The combination, as an identity.** -/
theorem bipev_elim : ∀ (Ls Cs : List (List Real)) (top topD : List Real) (x y : Real),
    Ls.length = Cs.length →
    bipev (elimCoeffs top topD Ls Cs) x y
      = pev topD x * bipev Ls x y - pev top x * bipev Cs x y := by
  intro Ls
  induction Ls with
  | nil =>
      intro Cs top topD x y hlen
      cases Cs with
      | nil =>
          show (0 : Real) = pev topD x * 0 - pev top x * 0
          mach_ring
      | cons _ _ => exact absurd hlen (by simp)
  | cons L Ls ih =>
      intro Cs top topD x y hlen
      cases Cs with
      | nil => exact absurd hlen (by simp)
      | cons C Cs =>
          have hrec := ih Cs top topD x y (by simpa using hlen)
          show pev (psub (pmul topD L) (pmul top C)) x
              + y * bipev (elimCoeffs top topD Ls Cs) x y
              = pev topD x * (pev L x + y * bipev Ls x y)
                - pev top x * (pev C x + y * bipev Cs x y)
          rw [hrec, pev_psub, pev_pmul, pev_pmul]
          mach_ring

/-- **Both relations vanish ⟹ the combination vanishes.** -/
theorem bipev_elim_eq_zero {Ls Cs : List (List Real)} {top topD : List Real} {x y : Real}
    (hlen : Ls.length = Cs.length)
    (hL : bipev Ls x y = 0) (hC : bipev Cs x y = 0) :
    bipev (elimCoeffs top topD Ls Cs) x y = 0 := by
  rw [bipev_elim Ls Cs top topD x y hlen, hL, hC]
  mach_ring

/-! ## The degree drop -/

theorem bipev_concat : ∀ (Ms : List (List Real)) (Z : List Real) (x y : Real),
    bipev (Ms ++ [Z]) x y = bipev Ms x y + powNat y Ms.length * pev Z x := by
  intro Ms
  induction Ms with
  | nil =>
      intro Z x y
      show pev Z x + y * 0 = 0 + powNat y 0 * pev Z x
      show pev Z x + y * 0 = 0 + 1 * pev Z x
      mach_ring
  | cons M Ms ih =>
      intro Z x y
      show pev M x + y * bipev (Ms ++ [Z]) x y
          = pev M x + y * bipev Ms x y + (y * powNat y Ms.length) * pev Z x
      rw [ih Z x y]
      mach_ring

/-- **The top term is killed.** A relation whose final coefficient evaluates to zero agrees with its
own truncation, so the eliminated relation has strictly smaller degree in `y`. -/
theorem bipev_drop_top {Ms : List (List Real)} {Z : List Real} {x y : Real}
    (hZ : pev Z x = 0) : bipev (Ms ++ [Z]) x y = bipev Ms x y := by
  rw [bipev_concat Ms Z x y, hZ]
  mach_ring

/-- The eliminated family's final entry is exactly `c_m·p_m − p_m·c_m`, which evaluates to zero —
this is the entry `bipev_drop_top` discards. -/
theorem elimCoeffs_top_eval (top topD : List Real) (x : Real) :
    pev (psub (pmul topD top) (pmul top topD)) x = 0 := by
  rw [pev_psub, pev_pmul, pev_pmul]
  mach_ring

end MachLib
