import MachLib.EMLFTranscendence

/-!
# Bivariate polynomial arithmetic

`List (List Real)` carries a polynomial in two variables — `bipev Cs x y = Σⱼ pev Cs[j] x · yʲ` —
and the `S > 0` branch needs to *build* such polynomials, not merely evaluate them. The identity
`c_d·(c_(d−1)' + v·m·c_d) − c_d'·c_(d−1) ≈ 0` has to be rearranged into a single relation in `e^S`
before `all_coeffs_nil_of_relation` can make it syntactic, and that rearrangement is products and
sums of `R[x][T]` polynomials.

This is the same construction as `padd`/`pmul`/`psub` one level up: the coefficient ring is
`List Real` instead of `Real`, so `padd` replaces `+` and `pmul` replaces `*`. Every proof mirrors
its univariate original, and the four evaluation laws are the point:

```
bipev (biadd A B)   x y = bipev A x y + bipev B x y
bipev (biscale A B) x y = pev A x * bipev B x y
bipev (bimul A B)   x y = bipev A x y * bipev B x y
bipev (bisub A B)   x y = bipev A x y - bipev B x y
```

## Why not reuse the univariate development

`pmul`, `pnorm`, `Pdvd` and the whole Euclid spine are written concretely for `List Real`, not over
an abstract coefficient ring — MachLib has no algebraic hierarchy, by design. So a second level
means a second set of definitions. That is four definitions and four lemmas here, versus introducing
a ring class and re-instantiating twenty modules; the arithmetic is all this layer needs, and none of
the divisibility theory.
-/

namespace MachLib

open Real

/-- Coefficientwise sum. -/
noncomputable def biadd : List (List Real) → List (List Real) → List (List Real)
  | [],      M       => M
  | A :: As, []      => A :: As
  | A :: As, B :: Bs => padd A B :: biadd As Bs

/-- Multiply every coefficient by a polynomial in `x` alone. -/
noncomputable def biscale (A : List Real) : List (List Real) → List (List Real)
  | []      => []
  | B :: Bs => pmul A B :: biscale A Bs

/-- Convolution, exactly as `pmul` one level down. -/
noncomputable def bimul : List (List Real) → List (List Real) → List (List Real)
  | [],      _ => []
  | A :: As, M => biadd (biscale A M) ([] :: bimul As M)

/-- Difference, via scaling by `−1` — the same shape as `psub`. -/
noncomputable def bisub (A B : List (List Real)) : List (List Real) :=
  biadd A (biscale [0 - 1] B)

/-! ## The evaluation laws -/

theorem bipev_biadd : ∀ (A B : List (List Real)) (x y : Real),
    bipev (biadd A B) x y = bipev A x y + bipev B x y := by
  intro A
  induction A with
  | nil => intro B x y; show bipev B x y = 0 + bipev B x y; mach_ring
  | cons A As ih =>
      intro B x y
      cases B with
      | nil => show bipev (A :: As) x y = bipev (A :: As) x y + 0; mach_ring
      | cons B Bs =>
          show pev (padd A B) x + y * bipev (biadd As Bs) x y
              = (pev A x + y * bipev As x y) + (pev B x + y * bipev Bs x y)
          rw [pev_padd, ih Bs x y]
          mach_mpoly [pev A x, pev B x, y, bipev As x y, bipev Bs x y]

theorem bipev_biscale (A : List Real) : ∀ (B : List (List Real)) (x y : Real),
    bipev (biscale A B) x y = pev A x * bipev B x y := by
  intro B
  induction B with
  | nil => intro x y; show (0 : Real) = pev A x * 0; mach_ring
  | cons B Bs ih =>
      intro x y
      show pev (pmul A B) x + y * bipev (biscale A Bs) x y
          = pev A x * (pev B x + y * bipev Bs x y)
      rw [pev_pmul, ih x y]
      mach_mpoly [pev A x, pev B x, y, bipev Bs x y]

theorem bipev_bimul : ∀ (A B : List (List Real)) (x y : Real),
    bipev (bimul A B) x y = bipev A x y * bipev B x y := by
  intro A
  induction A with
  | nil => intro B x y; show (0 : Real) = 0 * bipev B x y; mach_ring
  | cons A As ih =>
      intro B x y
      show bipev (biadd (biscale A B) ([] :: bimul As B)) x y
          = (pev A x + y * bipev As x y) * bipev B x y
      rw [bipev_biadd, bipev_biscale]
      show pev A x * bipev B x y + (pev ([] : List Real) x + y * bipev (bimul As B) x y) = _
      rw [ih B x y]
      show pev A x * bipev B x y + (0 + y * (bipev As x y * bipev B x y)) = _
      mach_mpoly [pev A x, y, bipev As x y, bipev B x y]

theorem bipev_bisub (A B : List (List Real)) (x y : Real) :
    bipev (bisub A B) x y = bipev A x y - bipev B x y := by
  show bipev (biadd A (biscale [0 - 1] B)) x y = _
  rw [bipev_biadd, bipev_biscale]
  show bipev A x y + ((0 - 1) + x * 0) * bipev B x y = _
  mach_mpoly [bipev A x y, bipev B x y, x]

end MachLib
