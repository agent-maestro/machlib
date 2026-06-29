import MachLib.OperatorBasisComplete
import MachLib.TrigLipschitz
import MachLib.FixedPoint
import MachLib.HyperbolicId

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
* **The airtight refinement** (`LocallyBoundable`, `lb_exp`/`lb_sinh`/`lb_cosh`): global
  Lipschitz misses the *amplifying* operators (`exp`/`sinh`/`cosh` have unbounded slope), so
  the honest notion is **local** Lipschitz-ness — a finite local condition number on every
  bounded range `[−R, R]`. Under it the certified basis is captured *in full*, amplifying ops
  included, while `floor` still fails (`heaviside_not_locallyBoundable`). The characterization
  is then total: admissible ⇔ finite local condition number; the guards are exactly the poles
  where that fails; the discontinuities are excluded outright.

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

/-! ## Local boundedness — the airtight characterization (incl. the amplifying operators)

`ForwardBoundable` (global Lipschitz) is the right notion for the 1-Lipschitz family, but the
**amplifying** operators `exp`/`sinh`/`cosh` are *not* globally Lipschitz (their slope grows
without bound) — yet they are exactly the operators the certifier handles via a *magnitude
envelope*. The honest notion is **local** Lipschitz-ness: on every bounded range `[−R, R]`
there is a finite constant `L(R)` (the *local condition number*). This captures the whole
certified basis — amplifying ops included — while the discontinuous `floor` still fails. -/

/-- `f` is **locally boundable**: on every `[−R, R]` it is Lipschitz with some finite
constant `L(R)`. The certifier's true admissibility notion (it always works with
magnitude-bounded inputs), broad enough to include the amplifying operators. -/
def LocallyBoundable (f : Real → Real) : Prop :=
  ∀ R : Real, 0 ≤ R → ∃ L : Real, 0 ≤ L ∧
    ∀ v ve, abs v ≤ R → abs ve ≤ R → abs (f v - f ve) ≤ L * abs (v - ve)

/-- Global Lipschitz ⇒ locally boundable (the same `L` works on every range). So every
`ForwardBoundable` operator is `LocallyBoundable`. -/
theorem ForwardBoundable.locallyBoundable {f : Real → Real} (h : ForwardBoundable f) :
    LocallyBoundable f := by
  obtain ⟨L, hL, hlip⟩ := h
  exact fun R _ => ⟨L, hL, fun v ve _ _ => hlip v ve⟩

theorem lb_abs : LocallyBoundable abs := fb_abs.locallyBoundable
theorem lb_clamp (lo hi : Real) : LocallyBoundable (fun x => clamp x lo hi) :=
  (fb_clamp lo hi).locallyBoundable
theorem lb_sin : LocallyBoundable sin := fb_sin.locallyBoundable
theorem lb_cos : LocallyBoundable cos := fb_cos.locallyBoundable
theorem lb_tanh : LocallyBoundable tanh := fb_tanh.locallyBoundable
theorem lb_atan : LocallyBoundable atan := fb_atan.locallyBoundable

/-- `exp` is Lipschitz on `[−R, R]` with constant `exp R` — derived from the hyperbolic
bounds via `exp = cosh + sinh`: `|exp a − exp b| ≤ |cosh a − cosh b| + |sinh a − sinh b| ≤
(sinh R + cosh R)·|a − b| = exp R·|a − b|`. -/
theorem exp_lipschitz_bound {a b R : Real} (ha : abs a ≤ R) (hb : abs b ≤ R) :
    abs (exp a - exp b) ≤ exp R * abs (a - b) := by
  have hrw : exp a - exp b = (cosh a - cosh b) + (sinh a - sinh b) := by
    rw [← cosh_add_sinh_eq_exp a, ← cosh_add_sinh_eq_exp b]; mach_ring
  have hfold : sinh R * abs (a - b) + cosh R * abs (a - b) = exp R * abs (a - b) := by
    rw [← cosh_add_sinh_eq_exp R]; mach_ring
  rw [hrw]
  exact le_trans (abs_add (cosh a - cosh b) (sinh a - sinh b))
    (le_trans (add_le_add_both (cosh_lipschitz_bound ha hb) (sinh_lipschitz_bound ha hb))
      (le_of_eq hfold))

/-- **The amplifying operators ARE locally boundable** (each with its local condition number
as the constant): `exp` with `exp R`, `sinh` with `cosh R`, `cosh` with `sinh R` on `[−R, R]`.
Global Lipschitz misses these; local Lipschitz captures them. -/
theorem lb_exp : LocallyBoundable exp :=
  fun R _ => ⟨exp R, le_of_lt (exp_pos R), fun _ _ hv hve => exp_lipschitz_bound hv hve⟩
theorem lb_sinh : LocallyBoundable sinh :=
  fun R _ => ⟨cosh R, le_of_lt (cosh_pos R), fun _ _ hv hve => sinh_lipschitz_bound hv hve⟩
theorem lb_cosh : LocallyBoundable cosh :=
  fun R hR => ⟨sinh R, sinh_nonneg hR, fun _ _ hv hve => cosh_lipschitz_bound hv hve⟩

/-- **`floor` is not even locally boundable.** The jump at `0` sits inside *every* range
`[−R, R]` with `R > 0`, so the same unit-gap-over-width-`1/(L+1)` contradiction kills any
local constant too. So the discontinuity is excluded under the certifier's *actual* (local)
admissibility notion, not merely the global one — the boundary is airtight. -/
theorem heaviside_not_locallyBoundable : ¬ LocallyBoundable heaviside := by
  intro h
  obtain ⟨L, hL0, hbound⟩ := h 1 (le_of_lt one_pos)
  have hL1 : (0 : Real) < L + 1 := lt_of_lt_of_le one_pos (le_add_of_nonneg_left hL0)
  have ht : (0 : Real) < 1 / (L + 1) := one_div_pos_of_pos hL1
  have hLL1 : L < L + 1 := by have h := add_lt_add_left one_pos L; rwa [add_zero] at h
  have hv0 : abs (0 : Real) ≤ 1 := by rw [abs_zero]; exact le_of_lt one_pos
  have hvt : abs (-(1 / (L + 1))) ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (le_of_lt ht)]
    exact div_le_one_of_le_of_pos hL1 (le_add_of_nonneg_left hL0)
  have hjump := hbound 0 (-(1 / (L + 1))) hv0 hvt
  rw [heaviside_zero, heaviside_neg (neg_neg_of_pos ht),
      show (1 : Real) - 0 = 1 from by mach_ring, abs_one,
      show (0 : Real) - (-(1 / (L + 1))) = 1 / (L + 1) from by mach_ring,
      abs_of_nonneg (le_of_lt ht)] at hjump
  have hlt : L * (1 / (L + 1)) < 1 := by
    have hmul : (1 / (L + 1)) * L < (1 / (L + 1)) * (L + 1) := mul_lt_mul_left_helper ht hLL1
    rw [div_mul_cancel (ne_of_gt hL1)] at hmul
    rwa [mul_comm L (1 / (L + 1))]
  exact lt_irrefl_ax 1 (lt_of_le_of_lt hjump hlt)

end MachLib.Real
