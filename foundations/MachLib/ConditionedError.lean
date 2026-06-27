import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.ErrorAlgebra

/-!
# Conditioned (mixed-sign) forward error — the cancellation road

The relative `(1+w)^d` algebra (`ForwardError`) is for nonneg accumulations. For
**mixed-sign** kernels (`dot`, `lerp`, differences) the relative bound is *false*
near cancellation, so the honest currency is the **absolute** forward error
bounded against the *conditioning quantity* `Σ|tᵢ|` — never dividing by the
(possibly near-zero) exact value.

FPModel already has the **sum** side: `cond_combine` tracks `(exact, error)` pairs
through a rounded `+`. The missing piece — supplied here — is the **product**
rule `cond_mul`, which closes the algebra for `{+, −, ×}` (subtraction via
`cond_neg`).

The object of study is the **condition number** `κ = Σ|tᵢ| / |exact|`. The bound
`cond_*` produce is `≈ w·Σ|tᵢ|`; the *relative* forward error is `≈ w·κ`. So the
bound is meaningful exactly when `κ` is moderate (well-conditioned) and degrades
honestly — to a still-true absolute statement — as `κ→∞` (cancellation). Proving
`κ`-bounds for specific kernel families is the open research past this wedge.

`sorryAx`-free. Builds on `FPModel` (`cond_combine`, `roundsW_abs`,
`abs_le_add_err`).
-/

namespace MachLib.Real

theorem cm_rearr (P Q R : Real) : P + (Q + R) = (Q + R) + P := by mach_mpoly [P, Q, R]

/-- **Conditioned product rule.** For computed `x ≈ ex` (error `≤ Ex`), `y ≈ ey`
(error `≤ Ey`), and a rounded product `p ≈ x·y`, the absolute error against the
exact `ex·ey` is bounded *without dividing* by anything — in terms of the exact
magnitudes and the operand errors. The `×`-analogue of `cond_combine`. -/
theorem cond_mul {w x y p ex ey Ex Ey : Real}
    (hw0 : 0 ≤ w) (hEx : 0 ≤ Ex) (hEy : 0 ≤ Ey)
    (hx : abs (x - ex) ≤ Ex) (hy : abs (y - ey) ≤ Ey)
    (hp : RoundsW w p (x * y)) :
    abs (p - ex * ey)
      ≤ (abs ex + Ex) * Ey + (abs ey + Ey) * Ex + (abs ex + Ex) * (abs ey + Ey) * w := by
  have hxM : abs x ≤ abs ex + Ex := abs_le_add_err hx
  have hyM : abs y ≤ abs ey + Ey := abs_le_add_err hy
  have hxM_nn : 0 ≤ abs ex + Ex := le_trans (abs_nonneg x) hxM
  -- rounding term: |p − x·y| ≤ (|ex|+Ex)(|ey|+Ey)·w
  have hA : abs (p - x * y) ≤ (abs ex + Ex) * (abs ey + Ey) * w := by
    have hxy : abs x * abs y ≤ (abs ex + Ex) * (abs ey + Ey) :=
      le_trans (mul_le_mul_of_nonneg_right hxM (abs_nonneg y))
               (mul_le_mul_of_nonneg_left hyM hxM_nn)
    refine le_trans (roundsW_abs hp) ?_
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hxy hw0)
                   (le_of_eq (mul_comm w ((abs ex + Ex) * (abs ey + Ey))))
  -- propagation term: |x·y − ex·ey| ≤ (|ex|+Ex)·Ey + (|ey|+Ey)·Ex
  have hB : abs (x * y - ex * ey) ≤ (abs ex + Ex) * Ey + (abs ey + Ey) * Ex := by
    rw [show x * y - ex * ey = x * (y - ey) + ey * (x - ex) from by mach_mpoly [x, y, ex, ey]]
    refine le_trans (abs_add _ _) (add_le_add_both ?_ ?_)
    · rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_right hxM (abs_nonneg (y - ey)))
                     (mul_le_mul_of_nonneg_left hy hxM_nn)
    · rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hx (abs_nonneg ey))
                     (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hEy) hEx)
  rw [show p - ex * ey = (p - x * y) + (x * y - ex * ey) from by mach_mpoly [p, x, y, ex, ey]]
  exact le_trans (abs_add _ _)
    (le_trans (add_le_add_both hA hB)
      (le_of_eq (cm_rearr ((abs ex + Ex) * (abs ey + Ey) * w)
                          ((abs ex + Ex) * Ey) ((abs ey + Ey) * Ex))))

/-- Leaf product (exact inputs): `|p − a·b| ≤ |a|·|b|·w`. The clean `Ex=Ey=0`
case of `cond_mul`. -/
theorem cond_mul_leaf {w a b p : Real} (hp : RoundsW w p (a * b)) :
    abs (p - a * b) ≤ abs a * abs b * w := by
  refine le_trans (roundsW_abs hp) ?_
  rw [abs_mul]; exact le_of_eq (mul_comm w (abs a * abs b))

/-- Negation preserves absolute error — gives subtraction (`a − b = a + (−b)`)
through `cond_combine`. -/
theorem cond_neg {v e E : Real} (h : abs (v - e) ≤ E) : abs ((-v) - (-e)) ≤ E := by
  apply abs_le_of
  · rw [show (-v) - (-e) = -(v - e) from by mach_ring]; exact le_trans (neg_le_abs (v - e)) h
  · rw [show -((-v) - (-e)) = v - e from by mach_ring]; exact le_trans (le_abs_self (v - e)) h

/-- **Worked composition** — `a*b − c*d`, the cancellation case the relative
algebra cannot touch. Folds `cond_mul_leaf → cond_neg → cond_combine` to bound
the absolute error against `|a*b| + |c*d|` (the conditioning quantity `Σ|tᵢ|`),
NOT against `|a*b − c*d|` — so it stays valid through cancellation. The relative
error is this bound over `|a*b − c*d|` = `≈ w·κ`, useful when `κ` is moderate. -/
theorem prod_diff_fwd {w a b c d p1 p2 r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d))
    (hr : RoundsW w r (p1 + (-p2))) :
    abs (r - (a * b + (-(c * d))))
      ≤ w * ((abs (a * b) + abs a * abs b * w) + (abs (-(c * d)) + abs c * abs d * w))
          + (abs a * abs b * w + abs c * abs d * w) :=
  cond_combine w hw0 (cond_mul_leaf hp1) (cond_neg (cond_mul_leaf hp2)) hr

end MachLib.Real
