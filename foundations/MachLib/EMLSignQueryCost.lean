import MachLib.EMLDecoderOffPositives
import MachLib.EMLExpQueryCost

/-!
# `q_F(sign)`: a branching operation gets a complexity sandwich

The previous file closed one door and I read it as closing the corridor. `EF_ne_exp_at_zero` shows
the decoder `EF`/`LF` pair does not reach off the positive ray — true — and I concluded no
`q_F(sign)` bound was available. That was wrong, and the corpus already contained the correction:

**`FTerm.LFneg` is a GLOBAL logarithm decoder.** `LFneg u = F u − EFneg u`, where `EFneg` evaluates
`exp` through `F` at the always-negative arguments `−(u²+1)` and `−(u+u²+1)`, so the totalised log
never contributes and no positivity hypothesis is needed. `LFneg_eval` carries **no side condition**.
It costs three queries where `LF` costs four and only works on the positives.

So `log` is an `FTerm` everywhere, `sign` is a finite expression in `log`, and the sandwich follows:

```
1 ≤ q_F(sign) ≤ 24
```

The upper bound is deliberately unoptimised — `fOcc` counts *tree* occurrences, and the indicator
uses its `logGap` subterm twice on each side, so a DAG measure would see 12, not 24. Tightening it is
a separate question from establishing that the sandwich exists.

## What the sandwich says

`sign` is a two-sided classifier. It is **not** zero-query (`sign_not_zero_query`), and it is
**finitely** many queries. So the branch is not free and not impossible: it has a price, and the
price is what the query hierarchy is for. Alongside `q_F^eventual(exp) = 1` this is the second
function with both bounds recorded, and the first one whose lower bound comes from a *branching*
obstruction rather than a growth one.
-/

namespace MachLib

open Real

/-- `log (2u) − log u`, as a term. Three queries per `LFneg`, six in all. -/
noncomputable def FTerm.logGapT (u : FTerm) : FTerm :=
  FTerm.sub (FTerm.LFneg (FTerm.mul (FTerm.const (1 + 1)) u)) (FTerm.LFneg u)

/-- The positivity indicator, as a term. -/
noncomputable def FTerm.posIndT (u : FTerm) : FTerm :=
  FTerm.div (FTerm.logGapT u) (FTerm.logGapT u)

/-- `sign`, as a term. -/
noncomputable def FTerm.signT : FTerm :=
  FTerm.sub (FTerm.posIndT FTerm.var) (FTerm.posIndT (FTerm.sub (FTerm.const 0) FTerm.var))

theorem FTerm.logGapT_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.logGapT u) x = logGap (FTerm.eval u x) := by
  show FTerm.eval (FTerm.LFneg (FTerm.mul (FTerm.const (1 + 1)) u)) x
      - FTerm.eval (FTerm.LFneg u) x = logGap (FTerm.eval u x)
  rw [FTerm.LFneg_eval, FTerm.LFneg_eval]
  rfl

theorem FTerm.posIndT_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.posIndT u) x = posIndicator (FTerm.eval u x) := by
  show FTerm.eval (FTerm.logGapT u) x / FTerm.eval (FTerm.logGapT u) x
      = posIndicator (FTerm.eval u x)
  rw [FTerm.logGapT_eval]
  rfl

/-- **`signT` computes `sign`, everywhere.** No domain restriction: the global decoder makes the
whole construction total. -/
theorem FTerm.signT_eval (x : Real) : FTerm.eval FTerm.signT x = Real.sign x := by
  show FTerm.eval (FTerm.posIndT FTerm.var) x
      - FTerm.eval (FTerm.posIndT (FTerm.sub (FTerm.const 0) FTerm.var)) x = Real.sign x
  rw [FTerm.posIndT_eval, FTerm.posIndT_eval]
  show posIndicator x - posIndicator (0 - x) = Real.sign x
  exact (sign_eq_posIndicator x).symm

theorem FTerm.fOcc_signT : fOcc FTerm.signT = 24 := rfl

/-- **`1 ≤ q_F(sign) ≤ 24`.** Both bounds, on a branching operation.

The lower bound is `sign_not_zero_query` — the level-set argument, which owes nothing to growth or
continuity. The upper bound is an explicit term. The gap between 1 and 24 is wide and honest: the
construction was written for correctness, and `fOcc` counts tree occurrences, so the shared `logGap`
subterms are paid for twice on each side. -/
theorem sign_query_cost_bounds :
    (fOcc FTerm.signT = 24 ∧ ∀ x : Real, FTerm.eval FTerm.signT x = Real.sign x)
    ∧ (∀ T : FTerm, (∀ x : Real, FTerm.eval T x = Real.sign x) → 1 ≤ fOcc T) := by
  refine ⟨⟨FTerm.fOcc_signT, FTerm.signT_eval⟩, fun T hT => ?_⟩
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exact absurd ⟨T, h0, hT⟩ sign_not_zero_query
  · exact hp

end MachLib
