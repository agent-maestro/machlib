import MachLib.EMLSignNotZeroQuery

/-!
# The decoders stop at the positive ray, and the boundary point already breaks them

`EF_eval` and `LF_eval` carry the hypothesis `0 < eval u x`, and the docstrings say "wherever that is
positive". That leaves a question the `sign` construction runs straight into: **is the hypothesis
load-bearing, or merely what the proof happened to need?** `sign x = H x − H (0 − x)` is built from
`log` at arguments that are nonpositive exactly half the time, so if the decoders extended, `log`
would be an `FTerm` everywhere and `q_F(sign) ≤ K` would follow immediately.

They do not extend, and the cheapest possible witness settles it: **`x = 0`**, the boundary itself.

## The computation

`Fbasis 0 = exp 0 + log₀ 0 = 1 + 0 = 1` — totalisation makes the log term vanish, and this is the
whole mechanism. Both the numerator's and the denominator's `Fbasis` differences collapse:

```
eval (EF var) 0 = (1 − 1 − log 3) / (1 − 1 − log 2) − 1 = log 3 / log 2 − 1
```

and that equals `exp 0 = 1` only if `log 3 = 2·log 2 = log 4`, i.e. only if `3 = 4`.

No numerics, no bounds on `exp(−1)`: the failure is exact and algebraic, and it happens **at the
boundary**, not far out on the negative ray.

## What it settles

* The `q_F(sign)` sandwich **cannot** be obtained from `EF`/`LF` as they stand. The semantic result
  (`sign_eq_posIndicator`: `sign` over field operations and totalised `log`) does not upgrade to a
  query-complexity bound for free. Recorded because that upgrade is the tempting next sentence.
* The hypothesis `0 < eval u x` in `EF_eval`/`LF_eval` is **necessary, not incidental**.
* What *is* free off the positive ray is the other direction: `Fbasis x = exp x` for `x ≤ 0`, since
  the log term is totalised away. `exp` needs no decoder there — it is `F` itself. The open problem
  is the positive ray, where `exp x = 1 / Fbasis (0 − x)` also holds, and the difficulty is that no
  single finite expression is yet known to cover both without a branch — which is what the whole
  construction was trying to build.
-/

namespace MachLib

open Real

/-- **Off the positive ray, `F` *is* `exp`.** Totalisation deletes the log term, so the exponential
decoder is unnecessary there — this is the half that comes free. -/
theorem Fbasis_eq_exp_of_nonpos {x : Real} (h : x ≤ 0) : Fbasis x = exp x := by
  show exp x + log x = exp x
  rw [log_nonpos h]
  mach_ring

private theorem three_ne_four : (1 + 1 + 1 : Real) ≠ (1 + 1) * (1 + 1) := by
  intro h
  have e1 := congrArg (fun z : Real => z - (1 + 1 + 1)) h
  have el : (1 + 1 + 1 : Real) - (1 + 1 + 1) = 0 := by mach_ring
  have er : (1 + 1 : Real) * (1 + 1) - (1 + 1 + 1) = 1 := by mach_ring
  rw [el, er] at e1
  exact lt_irrefl_ax 0 (e1 ▸ zero_lt_one_ax)

private theorem three_pos : (0 : Real) < 1 + 1 + 1 :=
  lt_of_lt_of_le zero_lt_one_ax (by
    have v := add_le_add_wit (le_refl (1 : Real)) (le_of_lt two_pos)
    have e : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : (1 : Real) + (1 + 1) = 1 + 1 + 1 := by mach_ring
    rw [e2] at v
    have w := add_le_add_wit (le_refl (1 : Real)) (le_of_lt zero_lt_one_ax)
    rw [e] at w
    exact le_trans w (by
      have u := add_le_add_wit (le_refl (1 + 1 : Real)) (le_of_lt zero_lt_one_ax)
      have e3 : (1 + 1 : Real) + 0 = 1 + 1 := by mach_ring
      rw [e3] at u; exact u))

/-- **`log 3 ≠ 2·log 2`**, because `3 ≠ 4`. The one arithmetic fact the refutation needs. -/
private theorem log_three_ne_two_log_two : log (1 + 1 + 1) ≠ log (1 + 1) + log (1 + 1) := by
  intro h
  rw [← log_mul two_pos two_pos] at h
  have hexp := congrArg exp h
  rw [exp_log three_pos, exp_log (mul_pos two_pos two_pos)] at hexp
  exact three_ne_four hexp

/-- **The exponential decoder is wrong at `0`.** So `EF_eval`'s positivity hypothesis is necessary,
and the `sign` representation does not lift to an `L_F` term through these decoders.

`Fbasis 0 = 1` because totalisation kills the log, both `Fbasis` differences collapse, and the
decoder returns `log 3 / log 2 − 1`, which is `exp 0 = 1` only if `3 = 4`. -/
theorem EF_ne_exp_at_zero :
    FTerm.eval (FTerm.EF FTerm.var) 0 ≠ exp (FTerm.eval FTerm.var 0) := by
  have hF0 : Fbasis (0 : Real) = 1 := by
    show exp 0 + log 0 = 1
    rw [log_nonpos (le_refl (0 : Real)), exp_zero]
    mach_ring
  have h3 : ((1 + 1 + 1 : Real)) * 0 = 0 := by mach_ring
  have h2 : ((1 + 1 : Real)) * 0 = 0 := by mach_ring
  have hlog2 : log (1 + 1 : Real) ≠ 0 := log_ne_zero_of_pos_of_ne_one two_pos two_ne_one
  intro hbad
  -- unfold the decoder at 0
  have hval : FTerm.eval (FTerm.EF FTerm.var) 0
      = (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) - 1 := by
    show (Fbasis ((1 + 1 + 1) * 0) - Fbasis 0 - log (1 + 1 + 1))
        / (Fbasis ((1 + 1) * 0) - Fbasis 0 - log (1 + 1)) - 1
        = (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) - 1
    rw [h3, h2, hF0]
    have e : (1 : Real) - 1 - log (1 + 1 + 1) = 0 - log (1 + 1 + 1) := by mach_ring
    have e2 : (1 : Real) - 1 - log (1 + 1) = 0 - log (1 + 1) := by mach_ring
    rw [e, e2]
  have hden : (0 : Real) - log (1 + 1) ≠ 0 := by
    intro hz
    exact hlog2 (by
      have e : log (1 + 1 : Real) = 0 - (0 - log (1 + 1)) := by mach_ring
      rw [e, hz]; mach_ring)
  -- the decoder's value would have to be exp 0 = 1
  have hone : (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) - 1 = 1 := by
    rw [← hval, hbad]
    show exp (0 : Real) = 1
    exact exp_zero
  have hq : (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) = 1 + 1 := by
    have e := congrArg (fun z : Real => z + 1) hone
    have el : (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) - 1 + 1
        = (0 - log (1 + 1 + 1)) / (0 - log (1 + 1)) := by mach_ring
    have er : (1 : Real) + 1 = 1 + 1 := rfl
    rw [el] at e; exact e
  -- clear the denominator: log 3 = 2 log 2
  have hmul := div_mul_self' (a := 0 - log (1 + 1 + 1)) hden
  rw [hq] at hmul
  refine log_three_ne_two_log_two ?_
  have e : (1 + 1 : Real) * (0 - log (1 + 1)) = 0 - (log (1 + 1) + log (1 + 1)) := by
    mach_mpoly [log (1 + 1 : Real)]
  rw [e] at hmul
  have e2 : log (1 + 1 + 1 : Real)
      = 0 - (0 - log (1 + 1 + 1)) := by mach_ring
  rw [e2, ← hmul]
  mach_ring

end MachLib
