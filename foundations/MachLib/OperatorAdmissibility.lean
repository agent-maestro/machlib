import MachLib.OperatorBasisComplete
import MachLib.TrigLipschitz
import MachLib.FixedPoint

/-!
# Why *these* operators? — an admissibility characterization (both directions)

The certifier covers a 17-operator basis and reaches 88.2% of the stdlib; the excluded
~12% (`floor`, `tan`/`asin`/`acos` near poles, tuples/complex, loops) fail for *structural*
reasons. This file turns that empirical boundary into theorems: it names the abstract
property an operator must have to be certifiable, shows the certified operators **have** it,
and shows a representative excluded operator provably **cannot**.

The property is **Lipschitz-ness** — the propagation half of certifiability. An operator
`f` is admissible only if a bounded input error `E` yields a bounded output error that
vanishes as `E → 0`; that is exactly `|f v − f ve| ≤ L·|v − ve|` for some finite `L` (the
local condition number). The certifier's per-operator rules are instances; the discontinuous
`floor` is not, *provably*.

* **Sufficiency** (`fb_abs`/`fb_clamp`/`fb_sin`/`fb_cos`/`fb_tanh`/`fb_atan`): the certified
  1-Lipschitz operators are forward-boundable, and `fb_propagate` is the error-propagation
  consequence the fold uses.
* **Necessity** (`heaviside_not_forwardBoundable`): the unit heaviside — the local shape of `floor`
  at an integer — admits **no** Lipschitz constant, so it cannot be certified. The boundary
  is a theorem, not a coverage gap.
* **The guard is necessary** (`recip_no_magnitude_bound`): unguarded `1/x` has no magnitude
  bound near `0`, the structural reason `÷`/`√`/`ln`/`pow` carry a denominator guard.

`sorryAx`-free; no new axioms.
-/

open Classical

namespace MachLib.Real

/-- `f` is **Lipschitz** with constant `L`: it amplifies a distance by at most `L`. This is
the propagation half of certifiability — input error `E` becomes output error `≤ L·E`. -/
def Lipschitz (L : Real) (f : Real → Real) : Prop :=
  ∀ v ve, abs (f v - f ve) ≤ L * abs (v - ve)

/-- `f` is **forward-boundable** iff it is Lipschitz with some nonneg constant — the
abstract property the certifier's per-operator rules deliver (a *computable local condition
number* with a finite, vanishing-at-zero error rule). -/
def ForwardBoundable (f : Real → Real) : Prop := ∃ L : Real, 0 ≤ L ∧ Lipschitz L f

/-- The certifiability consequence: a forward-boundable operator turns an input error `≤ E`
into an output error `≤ L·E` — vanishing as `E → 0`. (This is what the certifier's fold
threads through every node.) -/
theorem fb_propagate {L : Real} {f : Real → Real} (hL : 0 ≤ L) (hlip : Lipschitz L f)
    {v ve E : Real} (hE : abs (v - ve) ≤ E) : abs (f v - f ve) ≤ L * E :=
  le_trans (hlip v ve) (mul_le_mul_of_nonneg_left hE hL)

/-! ## Sufficiency — the certified operators are instances (constructive) -/

private theorem lip_one {f : Real → Real}
    (h : ∀ v ve, abs (f v - f ve) ≤ abs (v - ve)) : ForwardBoundable f :=
  ⟨1, le_of_lt one_pos, fun v ve => by rw [one_mul_thm]; exact h v ve⟩

theorem fb_abs : ForwardBoundable abs := lip_one abs_abs_sub_le
theorem fb_clamp (lo hi : Real) : ForwardBoundable (fun x => clamp x lo hi) :=
  lip_one (fun v ve => clamp_lipschitz v ve lo hi)
theorem fb_sin : ForwardBoundable sin := lip_one sin_lipschitz
theorem fb_cos : ForwardBoundable cos := lip_one cos_lipschitz
theorem fb_tanh : ForwardBoundable tanh := lip_one tanh_lipschitz
theorem fb_atan : ForwardBoundable atan := lip_one atan_lipschitz

/-! ## Necessity — a discontinuity admits no Lipschitz constant (why `floor` is off-basis) -/

/-- The unit heaviside `H x = [0 ≤ x]` — the elementary discontinuity, the local shape of `floor`
at each integer. -/
noncomputable def heaviside (x : Real) : Real := if 0 ≤ x then 1 else 0

theorem heaviside_zero : heaviside 0 = 1 := if_pos (le_refl 0)
theorem heaviside_neg {x : Real} (h : x < 0) : heaviside x = 0 :=
  if_neg (fun hle => lt_irrefl_ax x (lt_of_lt_of_le h hle))

/-- **A discontinuity admits no Lipschitz constant.** A unit jump across `0` over an interval
of width `t = 1/(L+1)` forces `1 ≤ L·t`, yet `L·t < 1` for every finite `L` — so no `L`
works. Hence `heaviside` (a step, and `floor`, a jump at every integer) propagates an arbitrarily small
input error into a full `1` of output error: it cannot be certified. The basis boundary is
a theorem, not a coverage gap. -/
theorem heaviside_not_forwardBoundable : ¬ ForwardBoundable heaviside := by
  rintro ⟨L, hL0, hlip⟩
  have hL1 : (0 : Real) < L + 1 := lt_of_lt_of_le one_pos (le_add_of_nonneg_left hL0)
  have ht : (0 : Real) < 1 / (L + 1) := one_div_pos_of_pos hL1
  have hLL1 : L < L + 1 := by
    have h := add_lt_add_left one_pos L; rwa [add_zero] at h
  -- the jump at width t forces `1 ≤ L · t`
  have hjump := hlip 0 (-(1 / (L + 1)))
  rw [heaviside_zero, heaviside_neg (neg_neg_of_pos ht),
      show (1 : Real) - 0 = 1 from by mach_ring, abs_one,
      show (0 : Real) - (-(1 / (L + 1))) = 1 / (L + 1) from by mach_ring,
      abs_of_nonneg (le_of_lt ht)] at hjump
  -- but `L · t < 1`
  have hlt : L * (1 / (L + 1)) < 1 := by
    have hmul : (1 / (L + 1)) * L < (1 / (L + 1)) * (L + 1) := mul_lt_mul_left_helper ht hLL1
    rw [div_mul_cancel (ne_of_gt hL1)] at hmul
    rwa [mul_comm L (1 / (L + 1))]
  exact lt_irrefl_ax 1 (lt_of_le_of_lt hjump hlt)

/-! ## The guard is necessary — unguarded reciprocal has no magnitude bound -/

/-- **Unguarded `1/x` has no magnitude bound near `0`.** For any claimed bound `M ≥ 0` there
is a positive `x` with `M · x < 1` — i.e. `M < 1/x`: the magnitude envelope does not exist
without a positive lower bound on `x`. This is the structural reason `÷`/`√`/`ln`/`pow`
carry a denominator guard `m ≤ |denom|`; the magnitude rule `Mbound / m` is finite only once
`m > 0`. -/
theorem recip_no_magnitude_bound {M : Real} (hM : 0 ≤ M) : ∃ x : Real, 0 < x ∧ M * x < 1 := by
  refine ⟨1 / (M + 1), one_div_pos_of_pos ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_add_of_nonneg_left hM)
  · have hM1 : (0 : Real) < M + 1 := lt_of_lt_of_le one_pos (le_add_of_nonneg_left hM)
    have hMM1 : M < M + 1 := by
      have h := add_lt_add_left one_pos M; rwa [add_zero] at h
    have hmul : (1 / (M + 1)) * M < (1 / (M + 1)) * (M + 1) := mul_lt_mul_left_helper
      (one_div_pos_of_pos hM1) hMM1
    rw [div_mul_cancel (ne_of_gt hM1)] at hmul
    rwa [mul_comm M (1 / (M + 1))]

end MachLib.Real
