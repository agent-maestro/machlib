import MachLib.ForwardError
import MachLib.Lemmas

/-!
# Absolute forward-error accumulation — the cancellation-tolerant fold

`ForwardError.Renc` is a *relative* enclosure: `Renc d w v ve` says `v` is within a `(1±w)^d`
factor of the exact `ve`. It composes beautifully through `+`/`·` on a cancellation-FREE tree of
NON-NEGATIVE quantities (`cosh = ½(eˣ+e⁻ˣ)`, `x²+y²`, …), but it says nothing useful once a
subtraction can cancel: if `xe − ye ≈ 0` the relative bound is unbounded, and `Renc` simply does
not apply (it is two-sided about a nonneg exact).

This file supplies the honest general answer: the **absolute** running-error bound (Higham,
*Accuracy and Stability of Numerical Algorithms*, §3.4). `AbsEnc E fl e` tracks `|fl − e| ≤ E`
directly, so it composes through **every** arithmetic node — crucially through `sub`, where the
`AbsEnc` bound is *identical* to the `add` bound. That is the whole point: cancellation does not
enlarge the absolute error of a subtraction (`|(x−y)−(x̂−ŷ)| = |(x−x̂)−(y−ŷ)| ≤ Eₓ+E_y`); it only
destroys the *relative* accuracy, which `AbsEnc` never promised. The `eml = exp x − log y` node
(`CompositeRuntimeError.eml_fwd_reduces_to_primitives`) is exactly the `absenc_sub` instance done
by hand; this generalises it to an arbitrary tree.

The residual trust is the same as everywhere in the certcom stack: the leaf `RoundsW u` specs
(one ULP fact per primitive). `sorryAx`-free, `MachLib.Real`-only (no Mathlib).
-/

namespace MachLib.Real

/-- **Absolute forward-error enclosure.** `fl` is within absolute error `E` of the exact real `e`.
Unlike `Renc`, this composes through cancellation. -/
def AbsEnc (E fl e : Real) : Prop := abs (fl - e) ≤ E

/-- An `AbsEnc` bound is non-negative (`0 ≤ |fl − e| ≤ E`). Used to discharge the positivity side
conditions of the product node. -/
theorem absenc_nonneg {E fl e : Real} (h : AbsEnc E fl e) : 0 ≤ E :=
  le_trans (abs_nonneg _) h

/-- **Leaf (exact).** A value carried with no rounding is within `0` of itself. -/
theorem absenc_exact (v : Real) : AbsEnc 0 v v := by
  unfold AbsEnc; rw [sub_self]; exact le_of_eq abs_zero

/-- **Leaf (rounded).** A correctly-rounded value is within `u·|e|` of the exact `e`. -/
theorem absenc_round {fl e : Real} (h : RoundsW u fl e) : AbsEnc (u * abs e) fl e :=
  roundsW_abs h

/-- `|a − b| ≤ |a| + |b|` (triangle for a difference). -/
theorem abs_sub_le' (a b : Real) : abs (a - b) ≤ abs a + abs b := by
  have h := abs_add a (-b)
  have e : a + -b = a - b := by mach_mpoly [a, b]
  rw [e, abs_neg] at h; exact h

/-- Monotonicity of `·` in both nonneg arguments (local, from the one-sided versions in scope). -/
private theorem mul_le_mul_both {a b c d : Real}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_right hab hc) (mul_le_mul_of_nonneg_left hcd (le_trans ha hab))

/-- **Negation node.** IEEE-754 negation is exact, so it preserves the absolute error unchanged:
`|(-flx) − (-xe)| = |flx − xe| ≤ Ex`. -/
theorem absenc_neg {Ex flx xe : Real} (hx : AbsEnc Ex flx xe) : AbsEnc Ex (-flx) (-xe) := by
  unfold AbsEnc at hx ⊢
  have e : -flx - -xe = -(flx - xe) := by mach_mpoly [flx, xe]
  rw [e, abs_neg]; exact hx

/-- **Addition node.** If `flx`/`fly` are within `Ex`/`Ey` of `xe`/`ye` and `fls` correctly rounds
`flx+fly`, then `fls` is within `u·((|xe|+Ex)+(|ye|+Ey)) + (Ex+Ey)` of `xe+ye`. -/
theorem absenc_add {flx fly fls xe ye Ex Ey : Real}
    (hx : AbsEnc Ex flx xe) (hy : AbsEnc Ey fly ye) (hs : RoundsW u fls (flx + fly)) :
    AbsEnc (u * ((abs xe + Ex) + (abs ye + Ey)) + (Ex + Ey)) fls (xe + ye) := by
  unfold AbsEnc at hx hy ⊢
  have htri : abs (fls - (xe + ye))
      ≤ abs (fls - (flx + fly)) + abs ((flx + fly) - (xe + ye)) := by
    have h := abs_add (fls - (flx + fly)) ((flx + fly) - (xe + ye))
    have e : (fls - (flx + fly)) + ((flx + fly) - (xe + ye)) = fls - (xe + ye) := by
      mach_mpoly [fls, flx, fly, xe, ye]
    rw [e] at h; exact h
  have hsum_abs : abs (flx + fly) ≤ (abs xe + Ex) + (abs ye + Ey) :=
    le_trans (abs_add flx fly) (add_le_add_both (abs_le_add_err hx) (abs_le_add_err hy))
  have h1 : abs (fls - (flx + fly)) ≤ u * ((abs xe + Ex) + (abs ye + Ey)) :=
    le_trans (roundsW_abs hs) (mul_le_mul_of_nonneg_left hsum_abs u_nonneg)
  have h2 : abs ((flx + fly) - (xe + ye)) ≤ Ex + Ey := by
    have e : (flx + fly) - (xe + ye) = (flx - xe) + (fly - ye) := by mach_mpoly [flx, fly, xe, ye]
    rw [e]; exact le_trans (abs_add (flx - xe) (fly - ye)) (add_le_add_both hx hy)
  exact le_trans htri (add_le_add_both h1 h2)

/-- **Subtraction node — the cancellation-tolerant one.** Same absolute bound as `absenc_add`: the
error of `flx − fly` is `u·((|xe|+Ex)+(|ye|+Ey)) + (Ex+Ey)`, *regardless* of how close `xe` and
`ye` are. Cancellation destroys relative accuracy, never the absolute bound. -/
theorem absenc_sub {flx fly fld xe ye Ex Ey : Real}
    (hx : AbsEnc Ex flx xe) (hy : AbsEnc Ey fly ye) (hs : RoundsW u fld (flx - fly)) :
    AbsEnc (u * ((abs xe + Ex) + (abs ye + Ey)) + (Ex + Ey)) fld (xe - ye) := by
  unfold AbsEnc at hx hy ⊢
  have htri : abs (fld - (xe - ye))
      ≤ abs (fld - (flx - fly)) + abs ((flx - fly) - (xe - ye)) := by
    have h := abs_add (fld - (flx - fly)) ((flx - fly) - (xe - ye))
    have e : (fld - (flx - fly)) + ((flx - fly) - (xe - ye)) = fld - (xe - ye) := by
      mach_mpoly [fld, flx, fly, xe, ye]
    rw [e] at h; exact h
  have hsub_abs : abs (flx - fly) ≤ (abs xe + Ex) + (abs ye + Ey) :=
    le_trans (abs_sub_le' flx fly) (add_le_add_both (abs_le_add_err hx) (abs_le_add_err hy))
  have h1 : abs (fld - (flx - fly)) ≤ u * ((abs xe + Ex) + (abs ye + Ey)) :=
    le_trans (roundsW_abs hs) (mul_le_mul_of_nonneg_left hsub_abs u_nonneg)
  have h2 : abs ((flx - fly) - (xe - ye)) ≤ Ex + Ey := by
    have e : (flx - fly) - (xe - ye) = (flx - xe) - (fly - ye) := by mach_mpoly [flx, fly, xe, ye]
    rw [e]; exact le_trans (abs_sub_le' (flx - xe) (fly - ye)) (add_le_add_both hx hy)
  exact le_trans htri (add_le_add_both h1 h2)

/-- **Multiplication node.** `flp` rounds `flx·fly`; the product error is
`u·(|xe|+Ex)(|ye|+Ey) + ((|xe|+Ex)·Ey + Ex·|ye|)`. -/
theorem absenc_mul {flx fly flp xe ye Ex Ey : Real}
    (hx : AbsEnc Ex flx xe) (hy : AbsEnc Ey fly ye) (hs : RoundsW u flp (flx * fly)) :
    AbsEnc (u * ((abs xe + Ex) * (abs ye + Ey)) + ((abs xe + Ex) * Ey + Ex * abs ye))
      flp (xe * ye) := by
  have hEx : 0 ≤ Ex := absenc_nonneg hx
  unfold AbsEnc at hx hy ⊢
  have htri : abs (flp - xe * ye)
      ≤ abs (flp - flx * fly) + abs (flx * fly - xe * ye) := by
    have h := abs_add (flp - flx * fly) (flx * fly - xe * ye)
    have e : (flp - flx * fly) + (flx * fly - xe * ye) = flp - xe * ye := by
      mach_mpoly [flp, flx, fly, xe, ye]
    rw [e] at h; exact h
  have hprod_abs : abs (flx * fly) ≤ (abs xe + Ex) * (abs ye + Ey) := by
    rw [abs_mul]
    exact mul_le_mul_both (abs_nonneg flx) (abs_le_add_err hx) (abs_nonneg fly) (abs_le_add_err hy)
  have h1 : abs (flp - flx * fly) ≤ u * ((abs xe + Ex) * (abs ye + Ey)) :=
    le_trans (roundsW_abs hs) (mul_le_mul_of_nonneg_left hprod_abs u_nonneg)
  have h2 : abs (flx * fly - xe * ye) ≤ (abs xe + Ex) * Ey + Ex * abs ye := by
    have e : flx * fly - xe * ye = flx * (fly - ye) + (flx - xe) * ye := by
      mach_mpoly [flx, fly, xe, ye]
    rw [e]
    have ha : abs (flx * (fly - ye)) ≤ (abs xe + Ex) * Ey := by
      rw [abs_mul]
      exact mul_le_mul_both (abs_nonneg flx) (abs_le_add_err hx) (abs_nonneg (fly - ye)) hy
    have hb : abs ((flx - xe) * ye) ≤ Ex * abs ye := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg ye)
    exact le_trans (abs_add (flx * (fly - ye)) ((flx - xe) * ye)) (add_le_add_both ha hb)
  exact le_trans htri (add_le_add_both h1 h2)

/-- **Lipschitz / transcendental node.** The general shape for a unary primitive `f` (exp, sin, tanh, …):
if `f` is `L`-Lipschitz, the input `flx` is within `Ex` of `xe`, and the computed `flf` is within the
primitive's own rounding error `Eround` of `f flx` (the primitive applied to the input), then `flf` is
within `Eround + L·Ex` of the exact `f xe`. The input error is amplified by the Lipschitz constant (an
`L`-fold sensitivity) and the primitive's rounding is added — the standard forward-error rule for a
transcendental. Instantiating it per primitive (e.g. `sin`/`cos`/`tanh`: `L = 1`) needs that primitive's
Lipschitz lemma (MachLib has them in `TrigLipschitz`/`HyperbolicLipschitz`) + its `RoundsW` spec. -/
theorem absenc_lip {f : Real → Real} {L flx xe Ex flf Eround : Real}
    (hLnn : 0 ≤ L) (hL : ∀ p q : Real, abs (f p - f q) ≤ L * abs (p - q))
    (hx : AbsEnc Ex flx xe) (hround : abs (flf - f flx) ≤ Eround) :
    AbsEnc (Eround + L * Ex) flf (f xe) := by
  unfold AbsEnc at hx ⊢
  have htri : abs (flf - f xe) ≤ abs (flf - f flx) + abs (f flx - f xe) := by
    have h := abs_add (flf - f flx) (f flx - f xe)
    have e : (flf - f flx) + (f flx - f xe) = flf - f xe := by mach_mpoly [flf, f flx, f xe]
    rw [e] at h; exact h
  have h2 : abs (f flx - f xe) ≤ L * Ex :=
    le_trans (hL flx xe) (mul_le_mul_of_nonneg_left hx hLnn)
  exact le_trans htri (add_le_add_both hround h2)

/-- **Local-Lipschitz node — for the unbounded-derivative primitives (`exp`, `log`, `sinh`, …).** Same
composition as `absenc_lip`, but `f` need only be `L`-Lipschitz on a bounded domain `[lo,hi]`, provided
BOTH the computed input `flx` and the exact input `xe` lie in `[lo,hi]`. This is exactly what the
unbounded-derivative primitives need: globally their slope blows up, but on `[lo,hi]` it is bounded (e.g.
`exp` by `exp hi`, `log` by `1/lo` for `lo > 0`), and that local bound is all the forward-error argument
uses. The two range hypotheses are the honest cost of leaving the globally-Lipschitz class. -/
theorem absenc_lip_local {f : Real → Real} {L flx xe Ex flf Eround lo hi : Real}
    (hLnn : 0 ≤ L)
    (hLip : ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi → abs (f p - f q) ≤ L * abs (p - q))
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - f flx) ≤ Eround) :
    AbsEnc (Eround + L * Ex) flf (f xe) := by
  unfold AbsEnc at hx ⊢
  have htri : abs (flf - f xe) ≤ abs (flf - f flx) + abs (f flx - f xe) := by
    have h := abs_add (flf - f flx) (f flx - f xe)
    have e : (flf - f flx) + (f flx - f xe) = flf - f xe := by mach_mpoly [flf, f flx, f xe]
    rw [e] at h; exact h
  have h2 : abs (f flx - f xe) ≤ L * Ex :=
    le_trans (hLip flx xe hflx_lo hflx_hi hxe_lo hxe_hi) (mul_le_mul_of_nonneg_left hx hLnn)
  exact le_trans htri (add_le_add_both hround h2)

/-- **Capstone — the `eml` node as a two-line instance of the general fold.** If `flx`/`fly`
correctly round the exact leaves `xe`/`ye` and `fld` rounds `flx − fly`, then
`|fld − (xe − ye)| ≤ u·(2+u)·(|xe| + |ye|)`. This is *exactly* the bound
`CompositeRuntimeError.eml_fwd_reduces_to_primitives` establishes by hand for `eml = exp x − log y`
(take `xe = exp x`, `ye = log y`) — here it falls out of `absenc_sub` on two rounded leaves plus one
ring identity, and holds under arbitrary cancellation `xe ≈ ye` (where a relative bound is vacuous).
The general fold thus subsumes the bespoke composite-error proof. -/
theorem absenc_sub_rounded {flx fly fld xe ye : Real}
    (hx : RoundsW u flx xe) (hy : RoundsW u fly ye) (hs : RoundsW u fld (flx - fly)) :
    AbsEnc (u * (1 + 1 + u) * (abs xe + abs ye)) fld (xe - ye) := by
  have h := absenc_sub (absenc_round hx) (absenc_round hy) hs
  unfold AbsEnc at h ⊢
  have e : u * ((abs xe + u * abs xe) + (abs ye + u * abs ye)) + (u * abs xe + u * abs ye)
         = u * (1 + 1 + u) * (abs xe + abs ye) := by mach_mpoly [u, abs xe, abs ye]
  rw [← e]; exact h

end MachLib.Real
