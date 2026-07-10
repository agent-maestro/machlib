import MachLib.AbsoluteError
import MachLib.HyperbolicLipschitz
import MachLib.HyperbolicPreservation
import MachLib.Log
import MachLib.Differentiation
import MachLib.Rolle
import MachLib.DivisionError

/-!
# Local-Lipschitz forward-error nodes for the remaining unbounded-derivative primitives

`ExpLipschitz` did `exp`. This completes the set the absolute fold's `tr1` layer needs among the
non-globally-Lipschitz primitives:

* `log` — `1/lo`-Lipschitz on `[lo, ∞)` (`lo > 0`): the MVT slope `1/c ≤ 1/lo` for `c ≥ lo`. Same MVT
  route as `exp_lip_lt`, using `HasDerivAt_log_pos` + `div_le_div_pos`.
* `sinh` / `cosh` — `HyperbolicLipschitz` already proves their bounded-domain Lipschitz bounds
  (`cosh R` / `sinh R` on `|·| ≤ R`); here they are wrapped into `absenc_lip_local` nodes.

Each `absenc_*_local` feeds the EML `tr1` fold once wired. `sorryAx`-free.
-/

namespace MachLib.Real

/-- `|x − y| = |y − x|` (local — the base one lives in `TrigLipschitz`). -/
private theorem abs_sub_comm2 (x y : Real) : abs (x - y) = abs (y - x) := by
  have h : y - x = -(x - y) := by mach_ring
  rw [h, abs_neg]

/-! ## `log` -/

/-- One-sided MVT bound: for `0 < lo ≤ a < b`, `|log b − log a| ≤ (1/lo)·(b − a)`. Slope `1/c ≤ 1/lo`. -/
theorem log_lip_lt {a b lo : Real} (hlo : 0 < lo) (hloa : lo ≤ a) (hab : a < b) :
    abs (log b - log a) ≤ (1 / lo) * (b - a) := by
  obtain ⟨c, f', hac, _, hd, heq⟩ :=
    mean_value_theorem_ct log a b hab
      (fun c hc1 _ => ⟨1 / c, HasDerivAt_log_pos c (lt_of_lt_of_le_r hlo (le_trans hloa hc1))⟩)
  have hc_pos : 0 < c := lt_of_lt_of_le_r hlo (le_trans hloa (le_of_lt hac))
  have hf' : f' = 1 / c := HasDerivAt_unique log f' (1 / c) c hd (HasDerivAt_log_pos c hc_pos)
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_of_nonneg hba_nn, abs_of_nonneg (le_of_lt (one_div_pos_of_pos hc_pos))]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) hlo (le_trans hloa (le_of_lt hac))) hba_nn

/-- **`log` is `1/lo`-Lipschitz on `[lo, hi]`** (`lo > 0`) — the `absenc_lip_local` hypothesis for `log`. -/
theorem log_lip_local (lo hi : Real) (hlo : 0 < lo) :
    ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
      abs (log p - log q) ≤ (1 / lo) * abs (p - q) := by
  intro p q hlp _ hlq _
  rcases lt_total p q with h | h | h
  · have hpq : abs (p - q) = q - p := by
      rw [abs_sub_comm2 p q]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))
    rw [abs_sub_comm2 (log p) (log q), hpq]
    exact log_lip_lt hlo hlp h
  · subst h
    rw [show log p - log p = (0 : Real) from by mach_ring, abs_zero]
    exact mul_nonneg (le_of_lt (one_div_pos_of_pos hlo)) (abs_nonneg (p - p))
  · rw [show abs (p - q) = p - q from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact log_lip_lt hlo hlq h

/-- **The `log` forward-error node.** Input within `Ex`, both in `[lo,hi]` (`lo > 0`) ⟹ output within
`Eround + (1/lo)·Ex`. -/
theorem absenc_log_local {flx xe Ex flf Eround lo hi : Real} (hlo : 0 < lo)
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - log flx) ≤ Eround) :
    AbsEnc (Eround + (1 / lo) * Ex) flf (log xe) :=
  absenc_lip_local (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo) hx
    hflx_lo hflx_hi hxe_lo hxe_hi hround

/-! ## `sinh` / `cosh` (wrapping `HyperbolicLipschitz`'s bounded-domain bounds) -/

/-- **The `sinh` forward-error node.** On `|·| ≤ R`, `sinh` is `cosh R`-Lipschitz. -/
theorem absenc_sinh_local {flx xe Ex flf Eround R : Real}
    (hx : AbsEnc Ex flx xe) (hflx : abs flx ≤ R) (hxe : abs xe ≤ R)
    (hround : abs (flf - sinh flx) ≤ Eround) :
    AbsEnc (Eround + cosh R * Ex) flf (sinh xe) := by
  refine absenc_lip_local (lo := -R) (hi := R) (le_of_lt (cosh_pos R)) ?_ hx
    (abs_le_iff.mp hflx).1 (abs_le_iff.mp hflx).2 (abs_le_iff.mp hxe).1 (abs_le_iff.mp hxe).2 hround
  intro p q hlp php hlq phq
  exact sinh_lipschitz_bound (abs_le_iff.mpr ⟨hlp, php⟩) (abs_le_iff.mpr ⟨hlq, phq⟩)

/-- **The `cosh` forward-error node.** On `|·| ≤ R` (`R ≥ 0`), `cosh` is `sinh R`-Lipschitz. -/
theorem absenc_cosh_local {flx xe Ex flf Eround R : Real} (hR : 0 ≤ R)
    (hx : AbsEnc Ex flx xe) (hflx : abs flx ≤ R) (hxe : abs xe ≤ R)
    (hround : abs (flf - cosh flx) ≤ Eround) :
    AbsEnc (Eround + sinh R * Ex) flf (cosh xe) := by
  refine absenc_lip_local (lo := -R) (hi := R) (sinh_nonneg hR) ?_ hx
    (abs_le_iff.mp hflx).1 (abs_le_iff.mp hflx).2 (abs_le_iff.mp hxe).1 (abs_le_iff.mp hxe).2 hround
  intro p q hlp php hlq phq
  exact cosh_lipschitz_bound (abs_le_iff.mpr ⟨hlp, php⟩) (abs_le_iff.mpr ⟨hlq, phq⟩)

end MachLib.Real
