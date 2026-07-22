import MachLib.NonRepresentabilityCensusSinSq

/-!
# Compression: the reusable tail-approximation barrier behind C6

Per external review: `no_tree_eps_close_to_sin_eventually` (C6) never actually used anything
`sin`-specific except two facts — `sin` recurs to exactly `1` and to exactly `-1`, past any
threshold. Extracted here as `RecurringStraddle`, with the general theorem below concluding
`no_tree_eps_close_to_sin_eventually` as a corollary. Covers, immediately, any target recurring to
two fixed values straddling `0` — `cos` (recurs to `±1` the same way, shifted by `π/2`) and any
`nestedTarget cs` with `nestedLo cs < 0 < nestedHi cs` are corollaries a future session can write
in a few lines each, without a new census file per target.

**Scope, stated precisely — this does NOT generalize past what C6 itself proved.** Like C6, this
is a TAIL/asymptotic barrier (`R` is an arbitrary hypothesis, the conclusion is about `x > R`) —
it says nothing about bounded intervals. Like C6, it is restricted to targets recurring around `0`
specifically (matching what `eml_tailSign_unconditional` gives `T.eval` UNCONDITIONALLY, no
validity hypothesis needed) — a target centered at a general level `L ≠ 0` would need `TailSign
(T.eval - L)`, which is NOT unconditionally available the way `TailSign T.eval` is (that is exactly
why `no_tree_eq_target_of_not_tailSign`, the EXACT-equality meta-theorem, needs the heavier
`eml_eventually_valid_repr`/validity machinery for a general `L` — extending this tail barrier to
general `L` would need the same, and is not attempted here).

The general bound: `ε ≤ vHi` and `ε ≤ -vLo` (both, matching `RecurringStraddle`'s two witnesses) —
equivalently, for symmetric `vLo = -vHi` (matching `sin`'s `δ := vHi - vLo = 2`), `ε ≤ δ / 2`, i.e.
`2ε ≤ δ`.
-/

namespace MachLib
namespace Real

open MachLib

/-- Two values `f` recurs to EXACTLY, past any threshold, straddling `0`. Generalizes `sin`'s
`sin_one_recurring`/`sin_neg_one_recurring` (`QuantitativeNonApproximation.lean`). -/
def RecurringStraddle (f : Real → Real) (vHi vLo : Real) : Prop :=
  vLo < 0 ∧ 0 < vHi ∧
    (∀ R : Real, ∃ x : Real, R < x ∧ f x = vHi) ∧
    (∀ R : Real, ∃ x : Real, R < x ∧ f x = vLo)

/-- **The general tail-approximation barrier.** No finite EML tree stays within `ε` of `TARGET`
for all sufficiently large `x`, whenever `TARGET` has a `RecurringStraddle` and `ε` doesn't exceed
either recurring witness's distance from `0`. Identical proof shape to
`no_tree_eps_close_to_sin_eventually`, with `sin`'s two recurring facts replaced by the abstract
`RecurringStraddle` witnesses. -/
theorem no_tree_eps_close_to_target_eventually (TARGET : Real → Real) (vHi vLo : Real)
    (hstraddle : RecurringStraddle TARGET vHi vLo)
    (T : EMLTree) (ε : Real) (hεHi : ε ≤ vHi) (hεLo : ε ≤ -vLo)
    (R : Real) (hclose : ∀ x : Real, R < x → abs (T.eval x - TARGET x) < ε) : False := by
  obtain ⟨_hvLo, _hvHi, hHiRec, hLoRec⟩ := hstraddle
  rcases eml_tailSign_unconditional T with ⟨R1, hR1⟩ | ⟨R1, hR1⟩ | ⟨R1, hR1⟩
  · obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hval⟩ := hLoRec M
    have hTpos : 0 < T.eval x := hR1 x (lt_trans_ax hMR1 hxM)
    have hlt1 : T.eval x - TARGET x < ε := lt_of_abs_lt (hclose x (lt_trans_ax hMR hxM))
    rw [hval] at hlt1
    have e : T.eval x - vLo = T.eval x + -vLo := by mach_ring
    rw [e] at hlt1
    have hgt : (-vLo : Real) < T.eval x + -vLo := by
      have h := add_lt_add_left hTpos (-vLo)
      rwa [add_zero, add_comm (-vLo) (T.eval x)] at h
    exact lt_irrefl_ax ε (lt_of_le_of_lt hεLo (lt_trans_ax hgt hlt1))
  · obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hval⟩ := hHiRec M
    have hTneg : T.eval x < 0 := hR1 x (lt_trans_ax hMR1 hxM)
    have habs2 : abs (TARGET x - T.eval x) < ε := by
      rw [show TARGET x - T.eval x = -(T.eval x - TARGET x) from by mach_ring, abs_neg]
      exact hclose x (lt_trans_ax hMR hxM)
    have hlt1 : TARGET x - T.eval x < ε := lt_of_abs_lt habs2
    rw [hval] at hlt1
    have hgt : (vHi : Real) < vHi - T.eval x := by
      have hneg : (0:Real) < -T.eval x := by
        have hh := add_lt_add_left hTneg (-T.eval x)
        rwa [add_zero, neg_add_self] at hh
      have h := add_lt_add_left hneg vHi
      rw [add_zero] at h
      have e2 : vHi + -T.eval x = vHi - T.eval x := by mach_ring
      rwa [e2] at h
    exact lt_irrefl_ax ε (lt_of_le_of_lt hεHi (lt_trans_ax hgt hlt1))
  · obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hval⟩ := hHiRec M
    have hTzero : T.eval x = 0 := hR1 x (lt_trans_ax hMR1 hxM)
    have habs2 : abs (TARGET x - T.eval x) < ε := by
      rw [show TARGET x - T.eval x = -(T.eval x - TARGET x) from by mach_ring, abs_neg]
      exact hclose x (lt_trans_ax hMR hxM)
    have hlt1 : TARGET x - T.eval x < ε := lt_of_abs_lt habs2
    rw [hval, hTzero, sub_zero] at hlt1
    exact lt_irrefl_ax ε (lt_of_le_of_lt hεHi hlt1)

/-- `sin`'s `RecurringStraddle`, `vHi := 1`, `vLo := -1` — matches `δ := vHi - vLo = 2` from the
external review's proposed bound (`2ε < δ` gives exactly `ε < 1`). -/
private theorem sin_recurringStraddle : RecurringStraddle Real.sin 1 (-1) := by
  refine ⟨?_, zero_lt_one_ax, sin_one_recurring, sin_neg_one_recurring⟩
  have h := add_lt_add_left zero_lt_one_ax (-1)
  rw [add_zero, neg_add_self] at h
  exact h

/-- **`sin` as a corollary**, re-deriving `no_tree_eps_close_to_sin_eventually` from the general
barrier — confirms the extraction is genuinely uniform, not a bigger different thing. -/
theorem no_tree_eps_close_to_sin_eventually_via_barrier (T : EMLTree) (ε : Real) (hε : ε < 1)
    (R : Real) (hclose : ∀ x : Real, R < x → abs (T.eval x - Real.sin x) < ε) : False :=
  no_tree_eps_close_to_target_eventually Real.sin 1 (-1) sin_recurringStraddle T ε (le_of_lt hε)
    (by rw [show -(-1:Real) = 1 from by mach_ring]; exact le_of_lt hε) R hclose

end Real
end MachLib
