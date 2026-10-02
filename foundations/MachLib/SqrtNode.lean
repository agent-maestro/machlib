import MachLib.TransNodes
import MachLib.OperatorBasisComplete

/-!
# The `sqrt` forward-error node — the asymmetric-domain twin of `absenc_log_local`

`TransNodes` built `log` (`1/lo`-Lipschitz on `[lo, ∞)`, `lo > 0`). `sqrt` is the other one-sided-domain
primitive control/DSP kernels reach for (RMS, magnitude, std-dev). It is `1/(2√lo)`-Lipschitz on
`[lo, ∞)` (`sqrt' = 1/(2√x)`, decreasing, so bounded by its value at the left endpoint) — the exact
analog of `log`, with constant `1/(√lo + √lo)`. `OperatorBasisComplete.sqrt_lipschitz_bound` already
proves the two-point bound; here it is wrapped into an `absenc_lip_local` node the fold can call.
`sorryAx`-free.
-/

namespace MachLib.Real

/-- **`sqrt` is `1/(√lo+√lo)`-Lipschitz on `[lo, hi]`** (`lo > 0`) — the `absenc_lip_local` hypothesis
for `sqrt`. Wraps `sqrt_lipschitz_bound`'s `|·−·|/(√lo+√lo)` into the fold's `L·|·−·|` shape. -/
theorem sqrt_lip_local (lo hi : Real) (hlo : 0 < lo) :
    ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
      abs (sqrt p - sqrt q) ≤ (1 / (sqrt lo + sqrt lo)) * abs (p - q) := by
  intro p q hlp _ hlq _
  have hdne : sqrt lo + sqrt lo ≠ 0 := ne_of_gt (add_pos (sqrt_pos hlo) (sqrt_pos hlo))
  rw [show (1 / (sqrt lo + sqrt lo)) * abs (p - q) = abs (p - q) / (sqrt lo + sqrt lo)
        from by rw [div_def (abs (p - q)) (sqrt lo + sqrt lo) hdne]; exact mul_comm _ _]
  exact sqrt_lipschitz_bound hlo hlp hlq

/-- **The `sqrt` forward-error node.** Input within `Ex`, both in `[lo,hi]` (`lo > 0`) ⟹ output within
`Eround + (1/(√lo+√lo))·Ex`. -/
theorem absenc_sqrt_local {flx xe Ex flf Eround lo hi : Real} (hlo : 0 < lo)
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - sqrt flx) ≤ Eround) :
    AbsEnc (Eround + (1 / (sqrt lo + sqrt lo)) * Ex) flf (sqrt xe) :=
  absenc_lip_local (le_of_lt (one_div_pos_of_pos (add_pos (sqrt_pos hlo) (sqrt_pos hlo))))
    (sqrt_lip_local lo hi hlo) hx hflx_lo hflx_hi hxe_lo hxe_hi hround

/-! ## At the endpoint: `sqrt` is ½-Hölder on `[0, ∞)`

`sqrt_lip_local` needs `0 < lo` because `sqrt'(x) = 1/(2√x)` is unbounded at `0`. `sqrt` itself is
not: `|√a − √b| ≤ √|a − b|` on all of `[0, ∞)`, a bound that is not LINEAR in the input error. It is
what Forge's analysis needs where a `sqrt` argument reaches exactly `0` inside a kernel's declared
domain -- a clamped discriminant, the distance between two points that may coincide -- where a
derivative rule must refuse while the program is perfectly well defined (forge, 2026-10-02: seven of
the corpus kernels no endpoint declaration could reach were exactly this). Proved from the `sqrt`
axioms already in `Trig` (`sqrt_sq_nonneg`, `le_sqrt_of_sq_le`); no new axiom. -/

private theorem le_total_sqrt_node (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

/-- One side: for `0 ≤ b ≤ a`, `√a − √b ≤ √(a − b)`. `(√a − √b)² = (a − b) − 2√b·(√a − √b)`, and the
subtracted term is non-negative. -/
theorem sqrt_sub_le_sqrt_sub {a b : Real} (hb : 0 ≤ b) (hba : b ≤ a) :
    sqrt a - sqrt b ≤ sqrt (a - b) := by
  have ha : 0 ≤ a := le_trans hb hba
  have hz : 0 ≤ sqrt a - sqrt b := sub_nonneg_of_le (sqrt_mono hb hba)
  apply le_sqrt_of_sq_le hz
  have hid : (sqrt a - sqrt b) * (sqrt a - sqrt b)
      = (sqrt a * sqrt a - sqrt b * sqrt b) - (sqrt b + sqrt b) * (sqrt a - sqrt b) := by
    mach_mpoly [sqrt a, sqrt b]
  rw [hid, sqrt_sq_nonneg a ha, sqrt_sq_nonneg b hb]
  exact sub_le_self (mul_nonneg (add_nonneg (sqrt_nonneg b) (sqrt_nonneg b)) hz)

/-- **`sqrt` is ½-Hölder on `[0, ∞)`**: `|√a − √b| ≤ √|a − b|` for `a, b ≥ 0`. -/
theorem sqrt_holder {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    abs (sqrt a - sqrt b) ≤ sqrt (abs (a - b)) := by
  rcases le_total_sqrt_node b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg_of_le (sqrt_mono hb hba)),
        abs_of_nonneg (sub_nonneg_of_le hba)]
    exact sqrt_sub_le_sqrt_sub hb hba
  · rw [abs_sub_comm (sqrt a) (sqrt b), abs_sub_comm a b,
        abs_of_nonneg (sub_nonneg_of_le (sqrt_mono ha hab)),
        abs_of_nonneg (sub_nonneg_of_le hab)]
    exact sqrt_sub_le_sqrt_sub ha hab

/-- **The `sqrt` forward-error node at an endpoint.** A computed argument `flx` within `Ex` of the
exact `xe`, both non-negative, gives an output within `Eround + √Ex` -- `absenc_sqrt_local` without its
`0 < lo`. `0 ≤ flx` is the side condition the caller must establish, about the COMPUTED value: IEEE
`sqrt` of a negative is NaN and MachLib's is `0` (`sqrt_neg_zero`), so nothing here could recover from
an argument that rounding pushed below zero. Forge establishes it structurally (a clamp, a sum of
squares) before it uses this rule. -/
theorem absenc_sqrt_holder {flx xe Ex flf Eround : Real}
    (hx : AbsEnc Ex flx xe) (hflx : 0 ≤ flx) (hxe : 0 ≤ xe)
    (hround : abs (flf - sqrt flx) ≤ Eround) :
    AbsEnc (Eround + sqrt Ex) flf (sqrt xe) := by
  have hsplit : flf - sqrt xe = (flf - sqrt flx) + (sqrt flx - sqrt xe) := by
    mach_mpoly [flf, sqrt flx, sqrt xe]
  have hprop : abs (sqrt flx - sqrt xe) ≤ sqrt Ex :=
    le_trans (sqrt_holder hflx hxe) (sqrt_mono (abs_nonneg _) hx)
  show abs (flf - sqrt xe) ≤ Eround + sqrt Ex
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hround hprop)

end MachLib.Real
