import MachLib.WitnessResidualNormalFormClosure
import MachLib.WitnessResidualNestedTargetBWitness
import MachLib.WitnessResidualEntireCrossingFamilyClosed

/-!
# The unconditional closure, generalized to the whole `nestedTarget` family

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 58 closed the
LITERAL-`sin` instance (`no_tree_eq_sin_unconditional`) unconditionally, via `eml_tailSign_
unconditional` (every EML tree has SOME `TailSign`) plus `sin_not_tailSign` (`sin` has none). The
natural next step, flagged explicitly in cont. 58 as unattempted: does `sin_not_tailSign`'s
argument carry over to the whole `nestedTarget cs` family, not just `cs = []`?

**Answer: yes, for `cs` whose range genuinely straddles zero** (`nestedLo cs ≤ 0 < nestedHi cs` —
the SHARP form, one-sided-strict; see below). This is a genuinely NEW hypothesis, not present in
`no_tree_eq_nested_target_given_validon` — and necessarily so: if `nestedTarget cs`'s entire range
sat on one side of zero (e.g. `nestedLo cs > 0`), it would ALREADY be eventually single-signed,
i.e. it WOULD have a `TailSign` of its own, and this route genuinely could not rule out a tree
matching it (a different obstruction, not a gap in this argument).

**The mechanism, mirroring `sin_not_tailSign` exactly but at the two points that generalize `kπ`/
`π+1`.** `nestedTarget_at_neg_pi_div_two` (already proven, `WitnessResidualNestedTargetBWitness.lean`)
and its mirror `nestedTarget_at_pi_div_two` (new, same one-line induction — each layer's `log` is
monotone, so it carries "achieves the extreme value here" through unchanged) show `nestedTarget
cs` hits its EXACT range bounds `nestedLo cs`/`nestedHi cs` at `-π/2`/`π/2`. `nestedTarget cs` is
`2π`-periodic for ANY `cs` (`nestedTarget_add_natCast_mul_two_pi`, by induction on `cs`, base case
via the already-proven `sin` axiom `sin_periodic`, reusing `sin_sub_natCast_mul_two_pi`'s already-
built `Nat`-indexed propagation machinery from `WitnessResidualEntireCrossingFamilyClosed.lean`
rather than re-deriving it) — so both extremes recur, exactly, arbitrarily far out. Given `nestedLo
cs ≤ 0`, arbitrarily-far points with value `≤ 0` rule out `TailSign.pos`; given `0 < nestedHi cs`,
arbitrarily-far points with value `> 0` rule out `TailSign.neg` AND `TailSign.zero` (the `nestedHi`
point alone is a fixed nonzero witness). The hypothesis is deliberately ASYMMETRIC (`≤` on `lo`,
strict `<` on `hi`) rather than requiring strict `<` on both sides — the boundary case `nestedLo cs
= 0` (touching zero at isolated points, never going negative) still has no `TailSign`, since it's
also nonzero arbitrarily far out (at the `nestedHi` points) — and this asymmetric form turns out to
be exactly what settles the sharp `c2 ≤ 2` boundary below, not just a cosmetic weakening.

**Payoff.** `nestedTarget_not_tailSign` and `no_tree_eq_nestedTarget_unconditional` — no finite EML
tree's `eval` equals any `nestedTarget cs` with `nestedWF cs ∧ nestedLo cs ≤ 0 ∧ 0 < nestedHi cs`,
completely unconditionally. Sanity-check corollary confirms `cs = []` recovers
`no_tree_eq_sin_unconditional` exactly (`nestedLo [] = -1 ≤ 0`, `nestedHi [] = 1 > 0`, `nestedWF
[] = True` — the hypothesis is satisfied trivially, not vacuously excluded).

**The `c2` boundary, resolved exactly** (`no_tree_eq_log_c2_plus_sin_unconditional`). `nestedHi
[c2] = log(c2+1) > 0` for EVERY `c2 > 1`, unconditionally — it's `nestedLo [c2] = log(c2-1)` that
draws the line, `≤ 0` exactly when `c2 ≤ 2`. The relaxed (`≤`) hypothesis above closes `log(c2+sin
x)` for the FULL range `1 < c2 ≤ 2`, not just `1 < c2 < 2`, and this is the SHARP boundary for this
method: for `c2 > 2` strictly, `log(c2+sin x)` is ENTIRELY positive (has its own `TailSign.pos`,
trivially), and no argument of this shape can rule out a tree matching it.

**Honest scope.** `cs` with `nestedLo cs > 0` (or `nestedHi cs ≤ 0`) are NOT covered by this file,
and covering them would need a genuinely different argument (their `nestedTarget` provably HAS a
`TailSign` of its own — confirmed above for `c2 > 2` specifically, not just suspected). Whether
OTHER well-formed `cs` used elsewhere in this arc (deeper nestings, `cs = [d, c2]` etc.) satisfy
the relaxed straddle condition has NOT been checked — only the `[c2]` family was instantiated here.
-/

namespace MachLib
namespace Real

/-- **`nestedTarget` hits its own upper bound exactly at `π/2`** — mirrors `nestedTarget_at_neg_
pi_div_two` exactly (`sin`'s MAXIMUM instead of its minimum). -/
theorem nestedTarget_at_pi_div_two (cs : List Real) (hwf : nestedWF cs) :
    nestedTarget cs (pi / (1 + 1)) = nestedHi cs := by
  induction cs with
  | nil =>
    show Real.sin (pi / (1 + 1)) = 1
    exact sin_pi_div_two
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    rw [nestedTarget_cons, nestedHi_cons, ih hwf_cs']

/-- Shifting by `k` full `2π` periods leaves `nestedTarget cs` unchanged (SUBTRACT direction),
for ANY `cs` — no well-formedness needed, since `log` is only ever applied to whatever `nestedTarget
cs'` already computes, and that value is untouched by the shift (by the inductive hypothesis).
Base case reuses `sin_sub_natCast_mul_two_pi`, already built and verified in
`WitnessResidualEntireCrossingFamilyClosed.lean`. -/
theorem nestedTarget_sub_natCast_mul_two_pi (cs : List Real) (y : Real) (k : Nat) :
    nestedTarget cs (y - natCast k * ((1 + 1) * pi)) = nestedTarget cs y := by
  induction cs with
  | nil =>
    show Real.sin (y - natCast k * ((1 + 1) * pi)) = Real.sin y
    exact sin_sub_natCast_mul_two_pi y k
  | cons c cs' ih =>
    rw [nestedTarget_cons, nestedTarget_cons, ih]

/-- The ADD-direction mirror, a one-line corollary of the subtract version applied at the
shifted point itself. -/
theorem nestedTarget_add_natCast_mul_two_pi (cs : List Real) (y : Real) (k : Nat) :
    nestedTarget cs (y + natCast k * ((1 + 1) * pi)) = nestedTarget cs y := by
  have h := nestedTarget_sub_natCast_mul_two_pi cs (y + natCast k * ((1 + 1) * pi)) k
  have e : y + natCast k * ((1 + 1) * pi) - natCast k * ((1 + 1) * pi) = y := by mach_ring
  rw [e] at h
  exact h.symm

/-- `natCast k` never outpaces `natCast k * 2π` — the same bound `sin_two_different_values_le`
derives inline, factored out for reuse. -/
theorem natCast_le_natCast_mul_two_pi (k : Nat) : natCast k ≤ natCast k * ((1 + 1) * pi) :=
  le_mul_of_one_le_right (natCast_nonneg k) (by
    have h := mul_le_mul_of_nonneg_left (le_of_lt pi_gt_one) (le_of_lt zero_lt_one_add_one_local)
    have e : (1 + 1) * (1 : Real) = 1 + 1 := mul_one_ax _
    rw [e] at h
    exact le_trans (by
      have h2 := add_le_add_left (le_of_lt zero_lt_one_ax) (1 : Real)
      have e2 : (1 : Real) + 0 = 1 := add_zero _
      rwa [e2] at h2) h)

/-- **`nestedTarget cs` reaches `nestedLo cs` arbitrarily far out**, for any target point `R`. -/
theorem nestedTarget_lo_past (cs : List Real) (hwf : nestedWF cs) (R : Real) :
    ∃ x : Real, R < x ∧ nestedTarget cs x = nestedLo cs := by
  obtain ⟨k, hk⟩ := archimedean (R + pi / (1 + 1))
  have hstep : R + pi / (1 + 1) < natCast k * ((1 + 1) * pi) :=
    lt_of_lt_of_le hk (natCast_le_natCast_mul_two_pi k)
  refine ⟨-(pi / (1 + 1)) + natCast k * ((1 + 1) * pi), ?_, ?_⟩
  · have h := add_lt_add_left hstep (-(pi / (1 + 1)))
    have e1 : -(pi / (1 + 1)) + (R + pi / (1 + 1)) = R := by mach_ring
    rwa [e1] at h
  · have h := nestedTarget_add_natCast_mul_two_pi cs (-(pi / (1 + 1))) k
    rw [h]; exact nestedTarget_at_neg_pi_div_two cs hwf

/-- **`nestedTarget cs` reaches `nestedHi cs` arbitrarily far out**, mirroring the above. -/
theorem nestedTarget_hi_past (cs : List Real) (hwf : nestedWF cs) (R : Real) :
    ∃ x : Real, R < x ∧ nestedTarget cs x = nestedHi cs := by
  obtain ⟨k, hk⟩ := archimedean (R - pi / (1 + 1))
  have hstep : R - pi / (1 + 1) < natCast k * ((1 + 1) * pi) :=
    lt_of_lt_of_le hk (natCast_le_natCast_mul_two_pi k)
  refine ⟨pi / (1 + 1) + natCast k * ((1 + 1) * pi), ?_, ?_⟩
  · have h := add_lt_add_left hstep (pi / (1 + 1))
    have e1 : pi / (1 + 1) + (R - pi / (1 + 1)) = R := by mach_ring
    rwa [e1] at h
  · have h := nestedTarget_add_natCast_mul_two_pi cs (pi / (1 + 1)) k
    rw [h]; exact nestedTarget_at_pi_div_two cs hwf

/-- **`nestedTarget cs` has no `TailSign`, whenever its range genuinely straddles zero.** Mirrors
`sin_not_tailSign`'s three-way case split exactly, using `nestedLo`/`nestedHi`-valued points
instead of `sin`'s zeros/`kπ + π/2` witness. -/
theorem nestedTarget_not_tailSign (cs : List Real) (hwf : nestedWF cs)
    (hlo : nestedLo cs ≤ 0) (hhi : 0 < nestedHi cs) :
    ¬ TailSign (nestedTarget cs) := by
  intro h
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨x, hxR, hxeq⟩ := nestedTarget_lo_past cs hwf R
    have hpos := hR x hxR
    rw [hxeq] at hpos
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hpos hlo)
  · obtain ⟨x, hxR, hxeq⟩ := nestedTarget_hi_past cs hwf R
    have hneg := hR x hxR
    rw [hxeq] at hneg
    exact lt_irrefl_ax 0 (lt_trans_ax hhi hneg)
  · obtain ⟨x, hxR, hxeq⟩ := nestedTarget_hi_past cs hwf R
    have hzero := hR x hxR
    rw [hxeq] at hzero
    rw [hzero] at hhi
    exact lt_irrefl_ax 0 hhi

/-- **No finite EML tree's `eval` function equals any straddling `nestedTarget cs` pointwise
everywhere — unconditionally.** No dependence on `EMLPfaffianValidOn`, no dependence on
`eml_pfaffian_validon_from_sin_equality`, no dependence on any hypothesis beyond `nestedWF cs`
and the straddle condition. -/
theorem no_tree_eq_nestedTarget_unconditional (cs : List Real) (hwf : nestedWF cs)
    (hlo : nestedLo cs ≤ 0) (hhi : 0 < nestedHi cs)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = nestedTarget cs x) : False :=
  nestedTarget_not_tailSign cs hwf hlo hhi
    (tailSign_congr_eventually 0 (fun x _ => heq x) (eml_tailSign_unconditional T))

/-- **Sanity check**: `cs = []` recovers `no_tree_eq_sin_unconditional` exactly through the
general family theorem — `nestedLo [] = -1 < 0`, `nestedHi [] = 1 > 0`, `nestedWF [] = True`, all
satisfied trivially rather than vacuously excluded. Confirms the generalization is equivalent to,
not merely similar to, cont. 58's original result. -/
theorem no_tree_eq_sin_unconditional_via_family (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = Real.sin x) : False := by
  have hlo : nestedLo ([] : List Real) ≤ 0 := by
    show (-1 : Real) ≤ 0
    have h := sub_lt_sub_right_of_lt (r := (1 : Real)) zero_lt_one_ax
    have e1 : (0 : Real) - 1 = -1 := by mach_ring
    have e2 : (1 : Real) - 1 = 0 := by mach_ring
    rw [e1, e2] at h
    exact le_of_lt h
  have hhi : (0 : Real) < nestedHi ([] : List Real) := zero_lt_one_ax
  have heq' : ∀ x : Real, T.eval x = nestedTarget [] x := heq
  exact no_tree_eq_nestedTarget_unconditional [] trivial hlo hhi T heq'

/-- **The `c2` boundary, resolved exactly.** `nestedLo [c2] = log(c2-1)`, `nestedHi [c2] =
log(c2+1)`. `nestedHi [c2] > 0` holds for EVERY `c2 > 1` (`c2+1 > 2 > 1`, `log` strictly
increasing past `1`), unconditionally — it's `nestedLo` that draws the line: `≤ 0` exactly when
`c2 ≤ 2`. So `no_tree_eq_nestedTarget_unconditional`'s relaxed (`≤`) hypothesis closes `log(c2+sin
x)` for the FULL range `1 < c2 ≤ 2` — not just `1 < c2 < 2` as the strict version would have given
— and this is the SHARP boundary for this method: for `c2 > 2` strictly, `nestedLo [c2] =
log(c2-1) > log 1 = 0`, so `log(c2+sin x)` is ENTIRELY positive, has a `TailSign` of its own
(`TailSign.pos`, trivially — never touches `≤ 0` at all), and no argument of this shape can rule
out a tree matching it; a genuinely different route would be needed there, not a gap in this one. -/
theorem no_tree_eq_log_c2_plus_sin_unconditional (c2 : Real) (hc2 : 1 < c2)
    (hc2le : c2 ≤ 1 + 1)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = Real.log (c2 + Real.sin x)) : False := by
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hwf : nestedWF [c2] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < c2 + (-1)
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e]; exact hc2m1_pos
  have hc2m1_le1 : c2 - 1 ≤ 1 := by
    have h := sub_le_sub_right hc2le (1 : Real)
    have e : (1 : Real) + 1 - 1 = 1 := by mach_ring
    rwa [e] at h
  have hlo : nestedLo [c2] ≤ 0 := by
    show Real.log (c2 + nestedLo ([] : List Real)) ≤ 0
    show Real.log (c2 + (-1)) ≤ 0
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e, ← log_one]
    exact log_mono hc2m1_pos hc2m1_le1
  have hc2add1_gt1 : (1 : Real) < c2 + 1 := by
    have h0c2 : (0 : Real) < c2 := lt_trans_ax zero_lt_one_ax hc2
    have h := add_lt_add_left h0c2 1
    rw [add_zero, add_comm 1 c2] at h
    exact h
  have hhi : (0 : Real) < nestedHi [c2] := by
    show (0 : Real) < Real.log (c2 + nestedHi ([] : List Real))
    show (0 : Real) < Real.log (c2 + 1)
    rw [← log_one]
    exact log_lt_log zero_lt_one_ax hc2add1_gt1
  have hT1eq' : ∀ x : Real, T.eval x = nestedTarget [c2] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_nil]
    exact heq x
  exact no_tree_eq_nestedTarget_unconditional [c2] hwf hlo hhi T hT1eq'

end Real
end MachLib
