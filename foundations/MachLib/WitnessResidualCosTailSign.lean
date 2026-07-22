import MachLib.WitnessResidualNormalFormClosure
import MachLib.CosNotInEMLAnyDepth

/-!
# The `cos` sibling: `eml_pfaffian_validon_from_cos_equality` discharged the same way

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 65 discharged
`eml_pfaffian_validon_from_sin_equality` (the axiom this whole arc was built to avoid) as a
vacuous corollary of `no_tree_eq_sin_unconditional`. Its sibling, `eml_pfaffian_validon_from_
cos_equality` (`CosNotInEMLAnyDepth.lean`), is the EXACT same shape with `cos` in place of `sin`
— and `eml_tailSign_unconditional` (`∀ T, TailSign T.eval`, cont. 58) is ALREADY fully general
over the target function: it says every EML tree eventually settles into one sign or vanishes,
with no dependence on `sin` anywhere in its own statement or proof. The only missing piece to
discharge the `cos` axiom the same way is `cos_not_tailSign` — mirroring `sin_not_tailSign`
exactly, swapping which point set is "zeros" and which is "the nonzero witness."

**Why this is cheap, not a new construction.** `cos`'s zeros (at `kπ + π/2`) and `sin`'s zeros (at
`kπ`) are already both fully proven and reusable, from TWO SEPARATE PRIOR pieces of this arc:
`cos_at_half_odd_pi` (`CosNotInEMLAnyDepth.lean`, built well before the `TailSign` detour, for the
ORIGINAL `cos ∉ EML_k` Khovanskii-bound proof) and `cos_natCast_mul_pi_ne_zero` (`WitnessResidual
TailSign.lean` cont. 56, built FOR `sin_not_tailSign`'s own `.zero` case, as the "`sin` is nonzero
at `kπ+π/2`" witness — which is exactly "cos is nonzero at `kπ`," `sin(kπ+π/2) = cos(kπ)`). Every
ingredient `cos_not_tailSign` needs was already sitting in the codebase; this file just assembles
them in the mirrored order `sin_not_tailSign` used.

**Payoff.** `no_tree_eq_cos_unconditional` — no finite EML tree's `eval` equals `cos` pointwise
everywhere, unconditionally, same shape as the `sin` result. `eml_pfaffian_validon_from_cos_
equality_proved` — the axiom, discharged vacuously, same `False.elim` shape as the `sin` side.
Fresh-rebuild `#print axioms` confirms non-circularity (neither `eml_pfaffian_validon_from_sin_
equality` nor `eml_pfaffian_validon_from_cos_equality` appears in the dependency list).
-/

namespace MachLib
namespace Real

/-- **`cos` fails all three `TailSign` classes** — the mirror image of `sin_not_tailSign`.
`cos`'s zeros (`kπ+π/2`, `MachLib.cos_at_half_odd_pi`) rule out `.pos`/`.neg`; `cos`'s nonzero
points (`kπ`, `cos_natCast_mul_pi_ne_zero` — already built for `sin_not_tailSign`'s OWN `.zero`
case) rule out `.zero`. Same archimedean growing-point machinery as the `sin` proof throughout. -/
theorem cos_not_tailSign : ¬ TailSign Real.cos := by
  intro h
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt1 : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hpidiv2pos : (0 : Real) < pi / (1 + 1) := by
      have h11 : (0 : Real) < 1 + 1 := by
        have h := add_lt_add_left zero_lt_one_ax 1
        rw [add_zero] at h
        exact lt_trans_ax zero_lt_one_ax h
      exact div_pos_of_pos_pos pi_pos h11
    have hlt2 : R < natCast n * pi + pi / (1 + 1) := by
      have h := add_lt_add_left hpidiv2pos (natCast n * pi)
      rw [add_zero] at h
      exact lt_trans_ax hlt1 h
    have hcosval := hR (natCast n * pi + pi / (1 + 1)) hlt2
    rw [MachLib.cos_at_half_odd_pi n] at hcosval
    exact lt_irrefl_ax 0 hcosval
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt1 : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hpidiv2pos : (0 : Real) < pi / (1 + 1) := by
      have h11 : (0 : Real) < 1 + 1 := by
        have h := add_lt_add_left zero_lt_one_ax 1
        rw [add_zero] at h
        exact lt_trans_ax zero_lt_one_ax h
      exact div_pos_of_pos_pos pi_pos h11
    have hlt2 : R < natCast n * pi + pi / (1 + 1) := by
      have h := add_lt_add_left hpidiv2pos (natCast n * pi)
      rw [add_zero] at h
      exact lt_trans_ax hlt1 h
    have hcosval := hR (natCast n * pi + pi / (1 + 1)) hlt2
    rw [MachLib.cos_at_half_odd_pi n] at hcosval
    exact lt_irrefl_ax 0 hcosval
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hcosval := hR (natCast n * pi) hlt
    exact cos_natCast_mul_pi_ne_zero n hcosval

/-- **No finite EML tree's `eval` function equals `cos` pointwise everywhere — unconditionally.**
Same shape as `no_tree_eq_sin_unconditional`: `eml_tailSign_unconditional` doesn't care which
target function is being ruled out. -/
theorem no_tree_eq_cos_unconditional (T : EMLTree) (heq : ∀ x : Real, T.eval x = Real.cos x) :
    False :=
  cos_not_tailSign (tailSign_congr_eventually 0 (fun x _ => heq x) (eml_tailSign_unconditional T))

end Real

open Real

/-- **The axiom `eml_pfaffian_validon_from_cos_equality`, proved.** Identical statement, same
`False.elim` shape as `eml_pfaffian_validon_from_sin_equality_proved`. -/
theorem eml_pfaffian_validon_from_cos_equality_proved
    (t : EMLTree) (hcos : ∀ x : Real, t.eval x = Real.cos x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b :=
  False.elim (no_tree_eq_cos_unconditional t hcos)

end MachLib
