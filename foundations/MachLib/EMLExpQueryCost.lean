import MachLib.EMLFTranscendence

/-!
# `q_F(exp) = 1` — exactly, in the eventual setting

The two-query decoder `EFneg` was built to be **global**, and it is. On a tail it is not optimal, and
the optimum is one query:

```
exp x = 1 / F(−x)        for every x > 0
```

because `−x < 0` puts `F` on the branch where the totalised logarithm vanishes, so `F(−x) = exp(−x)`
and a single reciprocal finishes it.

Together with the lower bound this pins the cost exactly. The global question is a different one and
stays open — `1/F(−x)` fails for `x < 0`, where `−x > 0` and the logarithm comes back.

## How this was found, and the correction it carries

By **searching for the identity before attempting to prove it impossible.** A validated numeric
search over rational substitutions `S` and rational post-processing flagged `S = −x`, `S = −x−1` and
`S = −x/2` at out-of-sample relative error `1e-52`, `1e-52`, `1e-47`, against `1e-3`–`1` for every
other candidate.

The first two versions of that search reported *every* candidate as a hit. Both were broken: monomial
bases on a short interval are so ill-conditioned that `σ_min/σ_max` is tiny regardless, and the
negative control (`y = x`) was degenerate by construction — it duplicates columns, so the matrix is
exactly rank-deficient for reasons having nothing to do with the target. The working test fits on one
interval and **validates out of sample** on another, with a positive control (a genuine rational
target) and a negative control (`sin`, which is not rational in `x` and `F(x)`).

So: `1 ≤ q_F(exp) ≤ 2` was the right bracket to state, and the answer is the lower end. The upper
bound was an artefact of having asked for a global identity.
-/

namespace MachLib

open Real

/-- `1 / F(−x)`. One `F` node. -/
noncomputable def FTerm.EFone : FTerm :=
  FTerm.div (FTerm.const 1) (FTerm.F (FTerm.sub (FTerm.const 0) FTerm.var))

theorem fOcc_EFone : fOcc FTerm.EFone = 1 := rfl

/-- **One query decodes `exp` on the positives.** `−x < 0`, so the totalised logarithm vanishes and
`F(−x) = exp(−x)`. -/
theorem FTerm.EFone_eval {x : Real} (hx : 0 < x) : FTerm.eval FTerm.EFone x = exp x := by
  have hneg : (0 : Real) - x ≤ 0 := by
    have v := add_lt_add_left hx (-x)
    have l : -x + 0 = -x := by mach_ring
    have r : -x + x = 0 := by mach_ring
    rw [l, r] at v
    have e : (0 : Real) - x = -x := by mach_ring
    rw [e]; exact le_of_lt v
  show (1 : Real) / Fbasis (0 - x) = exp x
  rw [Fbasis_of_nonpos hneg]
  refine div_of_eq_mul (ne_of_gt (exp_pos _)) ?_
  rw [← exp_add]
  have e : (0 : Real) - x + x = 0 := by mach_ring
  rw [e, exp_zero]

/-- The lower bound, in the eventual form the upper bound is stated in. -/
theorem fQueryLowerBound_eventual (T : FTerm)
    (h : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → FTerm.eval T x = exp x) : 1 ≤ fOcc T := by
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exfalso
    obtain ⟨X, hX, he⟩ := h
    exact not_polyEnvelope_of_ge_exp ⟨X, hX, fun x hx => le_of_eq (he x hx).symm⟩
      (polyEnvelope_of_ratGerm (ratGerm_of_zero_query T h0))
  · exact hp

/-- **`q_F(exp) = 1`, eventually.** Both bounds, and they meet.

The upper bound is `1/F(−x)`, valid on all of `(0, ∞)`; the lower bound is the zero-query barrier in
its eventual form. -/
theorem exp_query_cost_eventual :
    (fOcc FTerm.EFone = 1 ∧ ∀ x : Real, 0 < x → FTerm.eval FTerm.EFone x = exp x)
    ∧ (∀ T : FTerm, (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → FTerm.eval T x = exp x) →
        1 ≤ fOcc T) :=
  ⟨⟨fOcc_EFone, fun _ hx => FTerm.EFone_eval hx⟩, fQueryLowerBound_eventual⟩

/-! ## The global question is a different one, and stays open

`1/F(−x)` is wrong for `x < 0`: there `−x > 0`, the logarithm returns, and `F(−x) = exp(−x) + log(−x)`.
`EFneg` costs two queries and is right everywhere. So

```
q_F^eventual(exp) = 1        q_F^global(exp) ∈ {1, 2}
```

and the gap between them is exactly the totalisation branch. That is a sharper statement than the
one it replaces, and it locates the remaining uncertainty in a single place rather than in "is `F`
minimal". -/

/-- **The one-query term is genuinely wrong on the negatives.** At `x = −e` the argument `−x = e`
is positive, so `log` contributes `1` and `F(e) = exp(e) + 1` rather than `exp(e)`. -/
theorem EFone_fails_globally : ∃ x : Real, x < 0 ∧ FTerm.eval FTerm.EFone x ≠ exp x := by
  refine ⟨-(exp 1), neg_of_neg_pos' (by
    have e : -(-(exp 1)) = exp 1 := by mach_ring
    rw [e]; exact exp_pos 1), ?_⟩
  intro h
  have hx : (0 : Real) - -(exp 1) = exp 1 := by mach_ring
  have hA : (0 : Real) < exp (exp 1) := exp_pos _
  have hA1 : (0 : Real) < exp (exp 1) + 1 := add_pos hA zero_lt_one_ax
  have hval : FTerm.eval FTerm.EFone (-(exp 1)) = 1 / (exp (exp 1) + 1) := by
    show (1 : Real) / Fbasis (0 - -(exp 1)) = 1 / (exp (exp 1) + 1)
    rw [hx]
    show (1 : Real) / (exp (exp 1) + log (exp 1)) = 1 / (exp (exp 1) + 1)
    rw [log_exp]
  have hrhs : exp (-(exp 1)) = 1 / exp (exp 1) := by
    refine (div_of_eq_mul (ne_of_gt hA) ?_).symm
    rw [← exp_add]
    have e : exp 1 + -(exp 1) = 0 := by mach_ring
    rw [e, exp_zero]
  rw [hval, hrhs] at h
  -- `1/(A+1) = 1/A` forces `1/A = 0`
  have key : (1 : Real) / (exp (exp 1) + 1) * (exp (exp 1) + 1)
      = 1 / exp (exp 1) * (exp (exp 1) + 1) := by rw [h]
  rw [div_mul_self' (ne_of_gt hA1)] at key
  have expand : (1 : Real) / exp (exp 1) * (exp (exp 1) + 1)
      = 1 / exp (exp 1) * exp (exp 1) + 1 / exp (exp 1) := by
    mach_mpoly [(1 : Real) / exp (exp 1), exp (exp 1)]
  rw [expand, div_mul_self' (ne_of_gt hA)] at key
  have hz : (0 : Real) = 1 / exp (exp 1) := by
    have v : (1 : Real) + -1 = 1 + 1 / exp (exp 1) + -1 := by rw [← key]
    have el : (1 : Real) + -1 = 0 := by mach_ring
    have er : (1 : Real) + 1 / exp (exp 1) + -1 = 1 / exp (exp 1) := by
      mach_mpoly [(1 : Real) / exp (exp 1)]
    rw [el, er] at v; exact v
  have hpos := one_div_pos_of_pos hA
  rw [← hz] at hpos
  exact absurd hpos (lt_irrefl_ax 0)

end MachLib
