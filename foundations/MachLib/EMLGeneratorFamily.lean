import MachLib.EMLQueryComplexity

/-!
# `F` is not isolated: a two-parameter family of unary generators

`F(x) = exp x + log₀ x` looked like a lucky function. It is not. The whole affine mixture

```
F_{a,b,c}(x) = a·exp x + b·log₀ x + c
```

generates the same class, for **every** `a ≠ 0` and `b ≠ 0`, with the same query counts: two `F`
evaluations per exponential and three per logarithm. `F = F_{1,1,0}`.

## Why the generalisation is free

The *dilation* decoder would have had to work for this: `c` removed by taking a difference, `b·log n`
subtracted off, `a` cancelled in a ratio. Three separate repairs, one per parameter.

The **negative-argument** decoder needs none of them. Where `y ≤ 0` the totalised logarithm vanishes,
so

```
F_{a,b,c}(y) = a·exp y + c        for every y ≤ 0
```

and `a`, `c` come out by one subtraction and one ratio *simultaneously*:

```
exp u = (F_{a,b,c}(−q(u)) − c) / (F_{a,b,c}(−p(u)) − c)
```

because the `a` cancels between numerator and denominator. Only `a ≠ 0` is needed, and `b` never
appears — the exponential half of the basis does not see the logarithmic coefficient at all.

`b` enters only for the other half, where it is inverted directly:
`log₀ u = (F_{a,b,c}(u) − a·exp u − c)/b`.

So the parameters are not obstacles that had to be defeated one at a time; the decoder was never
looking at them. That is a property of *where* it evaluates the generator, not of the generator.
-/

namespace MachLib

open Real

/-- The affine mixture of the two primitives. `Fbasis = Fmix 1 1 0`. -/
noncomputable def Fmix (a b c : Real) (x : Real) : Real := a * exp x + b * log x + c

theorem Fmix_one_one_zero (x : Real) : Fmix 1 1 0 x = Fbasis x := by
  unfold Fmix Fbasis; mach_mpoly [exp x, log x]

/-- `L_F` syntax, reinterpreted: the same terms, with the unary symbol meaning `F_{a,b,c}`. -/
noncomputable def FTerm.evalM (a b c : Real) : FTerm → Real → Real
  | .const k, _ => k
  | .var,     x => x
  | .add u v, x => evalM a b c u x + evalM a b c v x
  | .sub u v, x => evalM a b c u x - evalM a b c v x
  | .mul u v, x => evalM a b c u x * evalM a b c v x
  | .div u v, x => evalM a b c u x / evalM a b c v x
  | .F u,     x => Fmix a b c (evalM a b c u x)

/-- Where the argument is non-positive the generator reports the exponential, affinely. -/
theorem Fmix_of_nonpos (a b c : Real) {y : Real} (hy : y ≤ 0) :
    Fmix a b c y = a * exp y + c := by
  unfold Fmix; rw [log_nonpos hy]; mach_mpoly [a, b, c, exp y]

/-! ## The two-query exponential decoder, for the whole family -/

/-- `(F(−q u) − c) / (F(−p u) − c)`. The `a` cancels; `b` never appears. -/
noncomputable def FTerm.EFmix (c : Real) (u : FTerm) : FTerm :=
  FTerm.div (FTerm.sub (FTerm.F (FTerm.negQ u)) (FTerm.const c))
            (FTerm.sub (FTerm.F (FTerm.negP u)) (FTerm.const c))

private theorem sub_nonpos_of_pos' {z : Real} (hz : 0 < z) : (0 : Real) - z ≤ 0 := by
  have v := add_lt_add_left hz (-z)
  have l : -z + 0 = -z := by mach_ring
  have r : -z + z = 0 := by mach_ring
  rw [l, r] at v
  have e : (0 : Real) - z = -z := by mach_ring
  rw [e]; exact le_of_lt v

theorem FTerm.EFmix_eval {a : Real} (b c : Real) (ha : a ≠ 0) (u : FTerm) (x : Real) :
    FTerm.evalM a b c (FTerm.EFmix c u) x = exp (FTerm.evalM a b c u x) := by
  have hq : (0 : Real) < FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one_ax
  have hp : (0 : Real) < FTerm.evalM a b c u x
      + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1 := by
    have hq2 := quad_pos (FTerm.evalM a b c u x)
    have e : FTerm.evalM a b c u x * FTerm.evalM a b c u x + FTerm.evalM a b c u x + 1
        = FTerm.evalM a b c u x + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1 := by mach_ring
    rw [e] at hq2; exact hq2
  show (Fmix a b c (0 - (FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) - c)
      / (Fmix a b c (0 - (FTerm.evalM a b c u x
          + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) - c)
      = exp (FTerm.evalM a b c u x)
  rw [Fmix_of_nonpos a b c (sub_nonpos_of_pos' hq), Fmix_of_nonpos a b c (sub_nonpos_of_pos' hp)]
  have hden : a * exp (0 - (FTerm.evalM a b c u x
      + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) + c - c ≠ 0 := by
    have e : a * exp (0 - (FTerm.evalM a b c u x
        + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) + c - c
        = a * exp (0 - (FTerm.evalM a b c u x
        + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) := by mach_ring
    rw [e]
    exact mul_ne_zero ha (ne_of_gt (exp_pos _))
  refine div_of_eq_mul hden ?_
  have el : a * exp (0 - (FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) + c - c
      = a * exp (0 - (FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) := by mach_ring
  have er : (a * exp (0 - (FTerm.evalM a b c u x
        + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) + c - c)
      * exp (FTerm.evalM a b c u x)
      = a * (exp (0 - (FTerm.evalM a b c u x
        + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)) * exp (FTerm.evalM a b c u x)) := by
    mach_mpoly [a, c, exp (0 - (FTerm.evalM a b c u x
      + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)), exp (FTerm.evalM a b c u x)]
  rw [el, er, ← exp_add]
  have e : 0 - (FTerm.evalM a b c u x + FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1)
      + FTerm.evalM a b c u x
      = 0 - (FTerm.evalM a b c u x * FTerm.evalM a b c u x + 1) := by mach_ring
  rw [e]

/-- `log₀ u = (F(u) − a·exp u − c)/b`. Three queries: the exponential's two, plus `u` itself. -/
noncomputable def FTerm.LFmix (a b c : Real) (u : FTerm) : FTerm :=
  FTerm.div (FTerm.sub (FTerm.sub (FTerm.F u)
      (FTerm.mul (FTerm.const a) (FTerm.EFmix c u))) (FTerm.const c)) (FTerm.const b)

theorem FTerm.LFmix_eval {a b : Real} (c : Real) (ha : a ≠ 0) (hb : b ≠ 0) (u : FTerm) (x : Real) :
    FTerm.evalM a b c (FTerm.LFmix a b c u) x = log (FTerm.evalM a b c u x) := by
  show (Fmix a b c (FTerm.evalM a b c u x) - a * FTerm.evalM a b c (FTerm.EFmix c u) x - c) / b
      = log (FTerm.evalM a b c u x)
  rw [FTerm.EFmix_eval b c ha u x]
  refine div_of_eq_mul hb ?_
  unfold Fmix
  mach_mpoly [a, b, c, exp (FTerm.evalM a b c u x), log (FTerm.evalM a b c u x)]

/-! ## Every `F_{a,b,c}` with `a ≠ 0 ≠ b` is a unary generator -/

/-- The compiler, for an arbitrary member of the family. -/
noncomputable def toFTermMix (a b c : Real) : EMLTree → FTerm
  | .const k => FTerm.const k
  | .var     => FTerm.var
  | .eml s t => FTerm.sub (FTerm.EFmix c (toFTermMix a b c s)) (FTerm.LFmix a b c (toFTermMix a b c t))

/-- **The family theorem.** For every `a ≠ 0` and every `b ≠ 0`, every EML tree is computed at every
real point by a term over constants, the variable, the four field operations and the single unary
symbol `F_{a,b,c}`.

`F` was never special: what does the work is that the generator contains `exp` with a nonzero
coefficient and `log₀` with a nonzero coefficient, and that `log₀` *vanishes* on a half-line the
decoder can steer into. -/
theorem Fmix_unary_basis {a b : Real} (c : Real) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ t : EMLTree, ∀ x : Real, FTerm.evalM a b c (toFTermMix a b c t) x = t.eval x := by
  intro t
  induction t with
  | const k => intro _; rfl
  | var => intro _; rfl
  | eml s t ihs iht =>
      intro x
      show FTerm.evalM a b c (FTerm.EFmix c (toFTermMix a b c s)) x
          - FTerm.evalM a b c (FTerm.LFmix a b c (toFTermMix a b c t)) x
          = exp (s.eval x) - log (t.eval x)
      rw [FTerm.EFmix_eval b c ha _ x, FTerm.LFmix_eval c ha hb _ x, ihs x, iht x]

/-- **Both coefficients are needed, and for different halves.** With `b = 0` the generator is
`a·exp + c`, which is `exp` up to an affine change and carries no information about `log₀` at all —
so no term over it can compute `log₀`, while the exponential decoder above still works unchanged.
Recorded as the *reason* `b ≠ 0` appears in `LFmix_eval` and not in `EFmix_eval`. -/
theorem Fmix_b_zero_is_affine_exp (a c : Real) (x : Real) : Fmix a 0 c x = a * exp x + c := by
  unfold Fmix; mach_mpoly [a, c, exp x, log x]

/-! ## The query counts are unchanged

`EFmix` applies `F` at `negQ u` and `negP u` — the same two arguments as `EFneg`, since the
parameters are absorbed by field operations outside the generator. `LFmix` adds `u`. So the
`fDepth` and `FQueriesLe` accounting of `EMLQueryComplexity.lean` transfers verbatim: two queries
per exponential, three per logarithm, and `F`-depth equal to EML depth. -/

theorem fDepth_EFmix (c : Real) (u : FTerm) : fDepth (FTerm.EFmix c u) = 1 + fDepth u := by
  simp only [FTerm.EFmix, FTerm.negQ, FTerm.negP, fDepth]
  omega

theorem fDepth_LFmix (a b c : Real) (u : FTerm) : fDepth (FTerm.LFmix a b c u) = 1 + fDepth u := by
  simp only [FTerm.LFmix, fDepth, fDepth_EFmix]
  omega

theorem fDepth_toFTermMix (a b c : Real) :
    ∀ t : EMLTree, fDepth (toFTermMix a b c t) = t.depth := by
  intro t
  induction t with
  | const k => rfl
  | var => rfl
  | eml s t ihs iht =>
      simp only [toFTermMix, fDepth, fDepth_EFmix, fDepth_LFmix, ihs, iht, EMLTree.depth]
      omega

end MachLib
