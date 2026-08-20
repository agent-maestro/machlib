import MachLib.EMLDepthTameness

/-!
# A unary decoder for `exp` and `log`

The EML node is binary: `eml a b ↦ exp(a) − log(b)`. This module records that a *single unary*
function built from it already carries both primitives, on `(0, ∞)`.

Take

```
    F(x) = eml(x, 1/x) = exp x − log (1/x) = exp x + log x
```

and form the **multiplicative finite difference**

```
    Δₙ F(x) = F(n·x) − F(x) − log n
```

The logarithm cancels *exactly*, because `log` turns dilation into translation:
`log(n·x) = log n + log x`, and the `− log n` removes what is left. So `Δₙ F(x) = exp(n x) − exp x`,
a pure exponential difference — the logarithmic component has been annihilated by a discrete
operator rather than by an estimate.

Two scales then recover everything. With `y = exp x`:

```
    Δ₂F = y² − y        Δ₃F = y³ − y        Δ₃F / Δ₂F − 1 = y
```

and `log x = F(x) − exp x`. So `F`, dilation by `2` and `3`, and field operations suffice to
reconstruct both `exp` and `log` on the positive reals.

**Why three scales and not two.** With `Δ₂` alone, `y` satisfies `y² − y = Δ₂`, a quadratic — the
value is pinned only up to a root choice, and no *rational* expression in `Δ₂` isolates it. Adding
the third scale makes the recovery rational, because `y³ − y = (y² − y)(y + 1)` factors through the
second. The minimality question — for which finite `S ⊆ ℕ` is `exp x` rationally recoverable from
`{F(nx) : n ∈ S}` — is open and is a clean algebra problem about the polynomials `yⁿ − y`.

**Scope.** Stated for the *functions*, on `(0, ∞)`. Nothing here claims `F` is cheap as a tree: its
right child computes `1/x`, and `d(1/x) = 4` is recorded elsewhere, so `F` itself is not a low-depth
object. Whether `F` is a genuine *basis* — every EML node recoverable from unary `F` data — is a
separate question and is not addressed here.
-/

namespace MachLib

open Real

/-- `F(x) = exp x + log x`, the value of `eml(x, 1/x)` on `(0, ∞)`. -/
noncomputable def Fbasis (x : Real) : Real := exp x + log x

/-- `a / b = c` from `a = b · c`. -/
private theorem div_of_eq_mul {a b c : Real} (hb : b ≠ 0) (h : a = b * c) : a / b = c := by
  rw [div_def a b hb, h]
  have e : b * c * (1 / b) = c * (b * (1 / b)) := by mach_mpoly [b, c, (1 : Real) / b]
  rw [e, mul_inv b hb]; mach_ring

/-- **The dilation difference annihilates the logarithm.**

`Δₙ F(x) = exp (n x) − exp x`, exactly — no error term, no ray, no hypothesis beyond positivity.
This is the whole mechanism: `log` is a cocycle for dilation, so a dilation difference kills it. -/
theorem dilation_diff (n x : Real) (hn : 0 < n) (hx : 0 < x) :
    Fbasis (n * x) - Fbasis x - log n = exp (n * x) - exp x := by
  unfold Fbasis
  rw [log_mul hn hx]
  mach_mpoly [exp (n * x), exp x, log n, log x]

/-- **`log` is recovered from `F` and `exp`.** Immediate, and recorded because it is half the
decoder. -/
theorem decoder_log (x : Real) : Fbasis x - exp x = log x := by
  unfold Fbasis; mach_mpoly [exp x, log x]

/-- **`exp` is recovered from `F` at three scales, rationally.**

```
    (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2)  −  1  =  exp x
```

The denominator is nonzero because `x > 0` forces `exp x > 1`. -/
theorem decoder_exp (x : Real) (hx : 0 < x) :
    (Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
      / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1 = exp x := by
  have h2p : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have h3p : (0 : Real) < 1 + 1 + 1 := add_pos h2p zero_lt_one_ax
  rw [dilation_diff (1 + 1 + 1) x h3p hx, dilation_diff (1 + 1) x h2p hx]
  have e2 : exp ((1 + 1) * x) = exp x * exp x := by
    have hx2 : (1 + 1) * x = x + x := by mach_ring
    rw [hx2, exp_add]
  have e3 : exp ((1 + 1 + 1) * x) = exp x * exp x * exp x := by
    have hx3 : (1 + 1 + 1) * x = x + x + x := by mach_ring
    rw [hx3, exp_add, exp_add]
  rw [e2, e3]
  have hy : 1 < exp x := one_lt_exp hx
  have hy0 : (0 : Real) < exp x := lt_trans_ax zero_lt_one_ax hy
  have hy1 : (0 : Real) < exp x - 1 := by
    have v := add_lt_add_left hy (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp x = exp x - 1 := by mach_ring
    rw [l, r] at v; exact v
  have hne : exp x * exp x - exp x ≠ 0 := by
    refine ne_of_gt ?_
    have hp : (0 : Real) < exp x * (exp x - 1) := mul_pos hy0 hy1
    have e : exp x * (exp x - 1) = exp x * exp x - exp x := by mach_mpoly [exp x]
    rw [e] at hp; exact hp
  have hfac : exp x * exp x * exp x - exp x
      = (exp x * exp x - exp x) * (exp x + 1) := by mach_mpoly [exp x]
  rw [div_of_eq_mul hne hfac]
  mach_ring

/-- **The decoder, both halves.** From the values of `F` at `x`, `2x` and `3x` alone, both
primitives are recovered on `(0, ∞)`. -/
theorem unary_decoder (x : Real) (hx : 0 < x) :
    ((Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
        / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1 = exp x)
    ∧ (Fbasis x - ((Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
        / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1) = log x) := by
  have he := decoder_exp x hx
  exact ⟨he, by rw [he]; exact decoder_log x⟩

end MachLib
