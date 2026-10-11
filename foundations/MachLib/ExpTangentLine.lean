import MachLib.Exp
import MachLib.Differentiation
import MachLib.Rolle

/-!
# MachLib.ExpTangentLine — `1 + x ≤ exp x`, derived from the mean value theorem

`one_add_le_exp_of_mvt` states exactly what the axiom `one_add_le_exp` (`Exp.lean`) states, and proves it from
the closed-interval mean value theorem (`mean_value_theorem_ct`, `Rolle.lean`, itself from `rolle_ct`) and the
derivative seed `HasDerivAt_exp`:

* `x > 0`: the MVT on `[0, x]` gives `c ∈ (0, x)` with `exp x - 1 = exp c * x`, and `exp c > exp 0 = 1`
  (`exp_lt`), so `exp x - 1 > x`;
* `x < 0`: the MVT on `[x, 0]` gives `c ∈ (x, 0)` with `1 - exp x = exp c * (0 - x)`, and `exp c < 1`, so
  `1 - exp x < -x`;
* `x = 0`: `exp 0 = 1` (`exp_zero`).

**THE AXIOM STAYS, on purpose (the owner's ruling, 2026-10-11, option (b)).** Converting `one_add_le_exp` into
this theorem was tried (branch `one-add-le-exp-theorem`, `de5ca5e3`, not merged) and is CORRECT, but it moved 503
footprints and failed the claim audit on 29 published claims: the F-transcendence results and the decay ladder
say they cost "nothing analytic -- no HasDerivAt" / "no rolle_ct", which is true of them only while the tangent
line is an axiom of the elementary-`exp` sub-theory. So the tangent inequality is PRIMITIVE there and DERIVABLE
once the calculus seeds are admitted (`zero_ne_one_ax`'s shape), and the full axiom-to-theorem replacement is a
separately reviewed change. Until then the derived theorem carries its own name and is used ONLY where a
consumer needs it: the four error-algebra rules of `gexpr_sound` that Forge's axiom policy reads
(`aerr_exp`, `aerr_exp_upper`, `aerr_pow`, `aerr_ln`, through `exp_grow_mvt` and `log_le_sub_one_mvt`).
Every other theorem that cites `one_add_le_exp` keeps its footprint.

**Why it needs calculus.** `exp_add`, `exp_lt` and `exp_surj` are satisfied by `b^x` for every `b > 1`
(`Exp.lean`'s note), and `1 + x ≤ b^x` holds for all `x` only at `b = e`. So no derivation from `Exp.lean`'s
laws and the ordered-field axioms exists: the base has to come from somewhere, and the only trusted axiom that
pins it without assuming this inequality is `HasDerivAt_exp` (`exp' = exp`). That is why this module sits above
`Rolle` in the import graph.

**Footprint, read off `#print axioms`:** 42 axioms, every one in `AxiomLedger.trustedFootprint` and in Forge's
policy: the ordered-field and `exp` laws (`exp_add`, `exp_lt`, `exp_surj`), `rolle_ct`, `HasDerivAt` and its
structural rules (`_add`, `_const`, `_id`, `_mul`, `_of_eq`, `_unique`), and `HasDerivAt_exp`. Not
`one_add_le_exp`, not `exp_gt_one_plus_self`, no `sorryAx`, no compiler-trust axiom.

The two cases are `private`, so no second public name states `exp_gt_one_plus_self`'s inequality.
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

/-- **The exponential tangent line, DERIVED**: `1 + x ≤ exp x` for all real `x`, from the mean value theorem and
`HasDerivAt_exp`. The same statement as the axiom `one_add_le_exp` (its stored type is `Expr`-identical), which
STAYS an axiom; cite this name where a footprint must not contain that axiom (the module docstring says why both
exist). -/
theorem one_add_le_exp_of_mvt (x : Real) : 1 + x ≤ exp x := by
  rcases lt_total x 0 with h | h | h
  · exact le_of_lt (one_add_lt_exp_of_neg_etl h)
  · subst h
    rw [exp_zero, show (1 : Real) + 0 = 1 from by mach_ring]
    exact le_refl 1
  · exact le_of_lt (one_add_lt_exp_of_pos_etl h)

/-- **The log tangent line, DERIVED**: `log t ≤ t − 1` for `t > 0` — `log_le_sub_one`'s statement and proof
(`EntropyDuality.lean`), with the tangent line taken from `one_add_le_exp_of_mvt` instead of the axiom. Used by
`ln_step`, so by `aerr_ln` and `aerr_pow`; `log_le_sub_one` itself is unchanged, because the value-gap ladder and
the grounded instances cite it and their published footprints carry no calculus. -/
theorem log_le_sub_one_mvt {t : Real} (ht : 0 < t) : Real.log t ≤ t - 1 := by
  have h : 1 + Real.log t ≤ t := by
    have hx := one_add_le_exp_of_mvt (Real.log t)
    rwa [exp_log ht] at hx
  -- 1 + log t ≤ t  ⇒  log t ≤ t − 1, by adding −1 on the left and cancelling.
  have h2 := add_le_add_left h (-1)
  rw [← add_assoc, neg_add_self, zero_add, add_comm (-1) t, ← sub_def] at h2
  exact h2

end MachLib.Real
