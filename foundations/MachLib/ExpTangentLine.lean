import MachLib.Exp
import MachLib.Differentiation
import MachLib.Rolle

/-!
# MachLib.ExpTangentLine — `1 + x ≤ exp x`, proved from the mean value theorem

`one_add_le_exp` was an axiom of `Exp.lean` from 2026-06-24 until 2026-10-11. It is a theorem here, with the
same name and the same type, proved from the closed-interval mean value theorem (`mean_value_theorem_ct`,
`Rolle.lean`, itself from `rolle_ct`) and the derivative seed `HasDerivAt_exp`:

* `x > 0`: the MVT on `[0, x]` gives `c ∈ (0, x)` with `exp x - 1 = exp c * x`, and `exp c > exp 0 = 1`
  (`exp_lt`), so `exp x - 1 > x`;
* `x < 0`: the MVT on `[x, 0]` gives `c ∈ (x, 0)` with `1 - exp x = exp c * (0 - x)`, and `exp c < 1`, so
  `1 - exp x < -x`;
* `x = 0`: `exp 0 = 1` (`exp_zero`).

**Why it needs calculus, and why it could not stay in `Exp.lean`.** `exp_add`, `exp_lt` and `exp_surj` are
satisfied by `b^x` for every `b > 1` (`Exp.lean`'s note), and `1 + x ≤ b^x` holds for all `x` only at
`b = e`. So no derivation from `Exp.lean`'s laws and the ordered-field axioms exists: the base has to come
from somewhere, and the only trusted axiom that pins it without assuming this inequality is
`HasDerivAt_exp` (`exp' = exp`). That is why the proof sits above `Rolle` in the import graph and why every
module that cites `one_add_le_exp` imports this one.

**What moved, read off `#print axioms`.** The theorem's footprint is 42 axioms, every one in
`AxiomLedger.trustedFootprint`: the ordered-field and `exp` laws, `rolle_ct`, `HasDerivAt` and its
structural rules (`_add`, `_const`, `_id`, `_mul`, `_of_eq`, `_unique`), and `HasDerivAt_exp`. It does not
contain `one_add_le_exp`, `exp_gt_one_plus_self`, `sorryAx` or a compiler-trust axiom. A theorem that cited
the axiom now carries that footprint instead of the single name: the trust is the same set of trusted
axioms, but the ROUTE is visible, and a theorem whose prose said "nothing analytic" while it cited
`one_add_le_exp` now shows `HasDerivAt_exp` and `rolle_ct` where it used to show one elementary-looking
name.

**`exp_gt_one_plus_self` (`1 + x < exp x` for `x > 0`) is the private `one_add_lt_exp_of_pos_etl` below,
and it STAYS AN AXIOM for now.** Not for want of a proof: `Differentiation` imports
`SinNotInEMLDepth2Sweep`, which cites `exp_gt_one_plus_self`, and `Exp.lean`'s `exp_grows_strictly_thm`
cites it too, so a theorem of that name proved here would sit above its own consumers. Converting it is a
module restructure (move those consumers above `Rolle`), not a one-line change. The helpers are `private`
so that no second public name states either inequality.
-/

namespace MachLib.Real

/-- `1 + x < exp x` for `x > 0`: the MVT on `[0, x]`. (The statement of the axiom `exp_gt_one_plus_self`.) -/
private theorem one_add_lt_exp_of_pos_etl {x : Real} (hx : 0 < x) : 1 + x < exp x := by
  obtain ⟨c, f', h0c, _, hd, hval⟩ :=
    mean_value_theorem_ct exp 0 x hx (fun c _ _ => ⟨exp c, HasDerivAt_exp c⟩)
  have hf' : f' = exp c := HasDerivAt_unique exp f' (exp c) c hd (HasDerivAt_exp c)
  rw [hf', exp_zero] at hval
  -- hval : exp x - 1 = exp c * (x - 0)
  have hc1 : 1 < exp c := by rw [← exp_zero]; exact exp_lt h0c
  have hx0 : x - 0 = x := by mach_ring
  rw [hx0] at hval
  have hlt : 1 * x < exp c * x := mul_lt_mul_of_pos_right hc1 hx
  rw [one_mul_thm, ← hval] at hlt
  -- hlt : x < exp x - 1
  have h := add_lt_add_left hlt 1
  rw [show (1 : Real) + (exp x - 1) = exp x from by mach_ring] at h
  exact h

/-- `1 + x < exp x` for `x < 0`: the MVT on `[x, 0]`. -/
private theorem one_add_lt_exp_of_neg_etl {x : Real} (hx : x < 0) : 1 + x < exp x := by
  obtain ⟨c, f', _, hc0, hd, hval⟩ :=
    mean_value_theorem_ct exp x 0 hx (fun c _ _ => ⟨exp c, HasDerivAt_exp c⟩)
  have hf' : f' = exp c := HasDerivAt_unique exp f' (exp c) c hd (HasDerivAt_exp c)
  rw [hf', exp_zero] at hval
  -- hval : 1 - exp x = exp c * (0 - x)
  have hc1 : exp c < 1 := by rw [← exp_zero]; exact exp_lt hc0
  have hpos : 0 < 0 - x := sub_pos_of_lt hx
  have hlt : exp c * (0 - x) < 1 * (0 - x) := mul_lt_mul_of_pos_right hc1 hpos
  rw [one_mul_thm, ← hval] at hlt
  -- hlt : 1 - exp x < 0 - x
  have h := add_lt_add_left hlt (x + exp x)
  rw [show x + exp x + (1 - exp x) = 1 + x from by mach_ring,
      show x + exp x + (0 - x) = exp x from by mach_ring] at h
  exact h

/-- The exponential tangent line: `1 + x ≤ exp x` for ALL real `x` (equality at `x = 0`). The non-strict,
unrestricted companion to `exp_gt_one_plus_self` (which needs `0 < x`). Closes saturating-integral
nonnegativity where the argument is `≤ 0` — e.g. sprint distance `t − τ·(1 − e^{−t/τ}) ≥ 0`, which reduces to
`1 − e^{−u} ≤ u`. An axiom until 2026-10-11; proved from the mean value theorem and `HasDerivAt_exp` (the
module docstring says what that moved). -/
theorem one_add_le_exp (x : Real) : 1 + x ≤ exp x := by
  rcases lt_total x 0 with h | h | h
  · exact le_of_lt (one_add_lt_exp_of_neg_etl h)
  · subst h
    rw [exp_zero, show (1 : Real) + 0 = 1 from by mach_ring]
    exact le_refl 1
  · exact le_of_lt (one_add_lt_exp_of_pos_etl h)

end MachLib.Real
