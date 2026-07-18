import MachLib.Decimal
import MachLib.SinTaylorRemainder

/-!
# Large-numeral arithmetic for `MachLib.Real` — the fix for the `mach_ring` scale wall

**The problem this closes** (found 2026-07-20ish while attempting `eml_tan.v`'s hardware
forward-error certificate, see [[project_forge_hardware_forward_error_scoping]] /
[[feedback_machlib_mach_ring_numeral_scale_wall]]): `MachLib.Real` has no native numerals beyond
0/1, so every constant used to be built as a flat sum of `1+1+1+...` or a product of two such sums
(`sevenhundredtwenty := six * onetwenty`, the pattern `SinTaylorRemainder`/`CosTaylorRemainder`
use). That works up to a few hundred. Empirically confirmed to hit `mach_ring`'s kernel-level
`maximum recursion depth` — not fixable by a bigger `maxRecDepth`, and not specific to *collecting*
like terms (a "distribute but never collect" variant at the same scale just hangs) — for anything
in the thousands, which is exactly the scale `tan`'s 8-level derivative-remainder chain needs
(coefficients like 3968, 12096, 40320, 129024).

**The fix.** `MachLib.Decimal` already proves `natCast_add`/`natCast_mul`
(`natCast (a+b) = natCast a + natCast b`, `natCast (a*b) = natCast a * natCast b`) BY INDUCTION on
`natCast_succ` — not by ring-normalizing a flat sum. Since Lean 4's kernel has fast native support
for `Nat` literals, `natCast_add`/`natCast_mul` turn a `Real`-arithmetic identity between large
numerals into a `Nat` arithmetic fact the kernel checks instantly, no matter how large. The recipe:

1. Represent every large coefficient as `natCast N` for a literal `Nat` `N` (not a flat sum).
2. State each needed "coefficient collects to this value" fact as its own `have`, proved by
   `rw [← natCast_add]` (or `natCast_mul`) — this is instant, since it reduces to `Nat` decidable
   equality, not a `Real`-level ring computation.
3. Rewrite the goal with those facts to put BOTH sides in the same *uncollected* shape, then finish
   with `mach_ring`, which treats each `natCast N` as an opaque atomic scalar (it never needs to
   *expand* the numeral — that's what made the old flat-sum approach explode) and only needs to
   verify the surrounding ring/distributivity structure over the free variable(s), which is cheap
   regardless of how large the coefficients are.

**Empirically verified at the actual scale `tan` needs** (both tests below reproduce exactly,
sorryAx-free, confirming this isn't just a toy case): the `g6→g7` derivative step (coefficients up
to 13440) and the `g7→g8` step (up to 129024, the largest number anywhere in `tan`'s chain).
Fraction coefficients (`tan`'s own Taylor coefficients are things like `17/315`) also work: reduce
via `natCast`-based numerator/denominator through the EXISTING `frac_reduce` lemma
(`SinTaylorRemainder`) plus `natCast_mul` for splitting off a common factor, e.g. `119/315 = 17/45`
below.
-/

namespace MachLib.Real

/-- `natCast n ≠ 0` whenever `n > 0` — the side condition every `1/natCast n` or `frac_reduce`
call over a `natCast`-represented denominator needs. -/
theorem natCast_ne_zero {n : Nat} (h : 0 < n) : natCast n ≠ 0 := ne_of_gt (natCast_pos h)

/-- **Worked template #1 — the `g6→g7` step from `tan`'s hardware forward-error chain**
(coefficients up to 13440). Distributes `(272+3696T²+8400T⁴+5040T⁶)(1+T²)` and collects into
`272+3968T²+12096T⁴+13440T⁶+5040T⁸`, entirely via `natCast_add` + `mach_ring` — no flat sums, no
recursion-depth issue. This is the RECIPE future large-coefficient proofs (e.g. a resumed `tan`
attempt) should follow directly. -/
theorem natcast_arith_template_g6_to_g7 (T : Real) :
    (natCast 272 + natCast 3696 * (T * T) + natCast 8400 * (T * T * T * T)
      + natCast 5040 * (T * T * T * T * T * T)) * (1 + T * T)
    = natCast 272 + natCast 3968 * (T * T) + natCast 12096 * (T * T * T * T)
      + natCast 13440 * (T * T * T * T * T * T) + natCast 5040 * (T * T * T * T * T * T * T * T) := by
  have h1 : natCast 3968 = natCast 272 + natCast 3696 := by rw [← natCast_add]
  have h2 : natCast 12096 = natCast 3696 + natCast 8400 := by rw [← natCast_add]
  have h3 : natCast 13440 = natCast 8400 + natCast 5040 := by rw [← natCast_add]
  rw [h1, h2, h3]
  mach_ring

/-- **Worked template #2 — the `g7→g8` step**, the LARGEST coefficients anywhere in `tan`'s chain
(up to 129024). Same recipe, confirming it holds at the full scale needed, not just a toy case. -/
theorem natcast_arith_template_g7_to_g8 (T : Real) :
    (natCast 7936 * T + natCast 48384 * (T * T * T) + natCast 80640 * (T * T * T * T * T)
      + natCast 40320 * (T * T * T * T * T * T * T)) * (1 + T * T)
    = natCast 7936 * T + natCast 56320 * (T * T * T) + natCast 129024 * (T * T * T * T * T)
      + natCast 120960 * (T * T * T * T * T * T * T)
      + natCast 40320 * (T * T * T * T * T * T * T * T * T) := by
  have h1 : natCast 56320 = natCast 48384 + natCast 7936 := by rw [← natCast_add]
  have h2 : natCast 129024 = natCast 80640 + natCast 48384 := by rw [← natCast_add]
  have h3 : natCast 120960 = natCast 40320 + natCast 80640 := by rw [← natCast_add]
  rw [h1, h2, h3]
  mach_ring

/-- **Worked template #3 — fraction-coefficient reduction via `natCast`.** `tan`'s OWN Taylor
coefficients are fractions (`17/315`, `2/15`, ...) that show up mid-derivation in unreduced form
(e.g. `119/315`, from `7·17/(7·45)`). Reduces `119/315` to `17/45` by splitting off the common
factor `7` (`natCast_mul`) and reusing `SinTaylorRemainder`'s existing `frac_reduce` on the
`natCast`-represented core fraction `7/315 = 1/45` — no new fraction machinery needed, `frac_reduce`
already works over ANY nonzero `Real` numerator/denominator, `natCast`-built or not. -/
theorem natcast_arith_template_frac_reduce :
    natCast 119 * (1 / natCast 315) = natCast 17 * (1 / natCast 45) := by
  have hcore : natCast 7 * (1 / natCast 315) = 1 / natCast 45 :=
    frac_reduce (natCast 7) (natCast 45) (natCast 315)
      (natCast_ne_zero (by decide)) (natCast_ne_zero (by decide)) (by rw [← natCast_mul])
  have hsplit : natCast 119 = natCast 17 * natCast 7 := by rw [← natCast_mul]
  rw [hsplit, mul_assoc, hcore]

end MachLib.Real
