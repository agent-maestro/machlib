import MachLib.WitnessResidualTargetGeneric
import MachLib.Decimal

/-!
# The whole nested-target family, closed by one induction on nesting depth

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`).
`WitnessResidualTargetGeneric.lean` abstracted the zero-counting argument over a target/level
pair and demonstrated it reaches one nesting level deeper than `log(c2+sin x)`
(`T1_not_eq_nested_log_given_validon`, target `log(d+log(c2+sin x))`) by hand-deriving the two
facts (`hTargetKPi`, `hTargetPi1`) that theorem needs for that specific target. This file does
what that file's own write-up flagged as the natural next step: define the WHOLE nested-target
family as an actual recursive type and derive those two facts GENERICALLY, by induction on
nesting depth, so no future level needs its own by-hand proof.

**The family.** `nestedTarget cs`, for `cs : List Real` a list of shift constants:
`nestedTarget [] = sin`; `nestedTarget (c :: cs) x = log(c + nestedTarget cs x)`. `cs = [c2]`
recovers `log(c2+sin x)`; `cs = [d, c2]` recovers `log(d+log(c2+sin x))` — the two targets
already handled by hand in the prior two files, now special cases of one general statement.

**The induction (`nestedTarget_facts`).** By induction on `cs`, given a well-formedness
condition (`nestedWF cs` — each shift constant keeps its layer's log from ever clamping),
simultaneously establishes THREE things: `nestedTarget cs`'s range is bounded by
`[nestedLo cs, nestedHi cs]` (propagated the same way the target itself is, one log-shift per
layer); its value at every `kπ` (`k≥1`) is the fixed constant `nestedLevel cs` (`sin(kπ)=0`
propagates through arbitrarily many nesting layers uniformly in `k`, the same fact
`WitnessResidualTargetGeneric.lean` used once, now proved once and reused at every depth); and
it differs from that level at `π+1` (via `log_injective_pos`, peeling one layer of log at a
time, reducing depth-`n` injectivity to depth-`(n-1)` injectivity — this is the one place the
induction does genuinely new work beyond gluing base facts together, since each layer needs its
own application of `log_injective_pos`, not just algebra).

**The payoff (`no_tree_eq_nested_target_given_validon`).** Combined with
`no_tree_eq_target_given_validon`, no finite EML tree can equal ANY member of the nested-target
family while having `EMLPfaffianValidOn` throughout — not just the two levels checked by hand so
far, but the whole family, for one proof. This closes the "does a finite tree realize *some*
target in this family" side of the problem completely. It does NOT close `hvalidon_any_b` itself
(establishing a tree's own `EMLPfaffianValidOn` from its structure) — that remains the separate,
genuinely open induction on tree structure that the rest of Option D's remaining work is about.
-/

namespace MachLib

open MachLib.Real
open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

/-! ## The nested-target family, and the invariants it satisfies -/

/-- The nested log-of-shifted target. `nestedTarget [] = sin`; prepending `c` adds one more
OUTER log-shift layer around whatever `cs` already builds. -/
noncomputable def nestedTarget : List Real → Real → Real
  | [], x => Real.sin x
  | c :: cs, x => Real.log (c + nestedTarget cs x)

/-- Lower bound on `nestedTarget cs`'s range, propagated the same way the target itself is. -/
noncomputable def nestedLo : List Real → Real
  | [] => -1
  | c :: cs => Real.log (c + nestedLo cs)

/-- Upper bound on `nestedTarget cs`'s range. -/
noncomputable def nestedHi : List Real → Real
  | [] => 1
  | c :: cs => Real.log (c + nestedHi cs)

/-- The fixed value `nestedTarget cs` takes at every `kπ` (`k ≥ 1`). -/
noncomputable def nestedLevel : List Real → Real
  | [] => 0
  | c :: cs => Real.log (c + nestedLevel cs)

/-- Well-formedness: every shift constant keeps its own layer's log argument strictly positive
on the WHOLE range of the layer inside it (checked at the layer's lower bound, which suffices
since the upper bound only needs the same shift to stay positive too, and it's larger). Without
this, some layer clamps and the "target" collapses to something outside this family. -/
def nestedWF : List Real → Prop
  | [] => True
  | c :: cs => 0 < c + nestedLo cs ∧ nestedWF cs

/-! Plain unfold lemmas for the `cons` case of each recursive definition above, used instead of
`show` in the induction below (`show`'s defeq check interacted badly with these `noncomputable`
well-founded-recursion-compiled defs in this Mathlib-free setting — `rw` with an explicit
equation lemma is the robust idiom here, matching this codebase's established `let`+`show`
avoidance pattern from earlier files in this family). -/

theorem nestedTarget_nil (x : Real) : nestedTarget [] x = Real.sin x := rfl

theorem nestedTarget_cons (c : Real) (cs : List Real) (x : Real) :
    nestedTarget (c :: cs) x = Real.log (c + nestedTarget cs x) := rfl

theorem nestedLo_cons (c : Real) (cs : List Real) :
    nestedLo (c :: cs) = Real.log (c + nestedLo cs) := rfl

theorem nestedHi_cons (c : Real) (cs : List Real) :
    nestedHi (c :: cs) = Real.log (c + nestedHi cs) := rfl

theorem nestedLevel_cons (c : Real) (cs : List Real) :
    nestedLevel (c :: cs) = Real.log (c + nestedLevel cs) := rfl

/-- **The combined induction.** Range, `kπ`-value, and `π+1`-difference, all at once, by
induction on nesting depth. See the file docstring for why these three are proved together
rather than separately (the range fact is exactly what each induction step needs to keep its own
layer's log from clamping). -/
theorem nestedTarget_facts (cs : List Real) (hwf : nestedWF cs) :
    (∀ x, nestedLo cs ≤ nestedTarget cs x ∧ nestedTarget cs x ≤ nestedHi cs) ∧
    (∀ k : Nat, 1 ≤ k → nestedTarget cs (natCast k * pi) = nestedLevel cs) ∧
    (nestedTarget cs (pi + 1) ≠ nestedLevel cs) := by
  induction cs with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨neg_one_le_sin x, sin_le_one x⟩
    · intro k _
      show Real.sin (natCast k * pi) = 0
      exact sin_natCast_mul_pi k
    · show Real.sin (pi + 1) ≠ 0
      have heq : Real.sin (pi + 1) = Real.cos pi * Real.sin 1 := by
        rw [Real.sin_add, Real.sin_pi, zero_mul, zero_add]
      have hneg : Real.cos pi * Real.sin 1 < 0 := by
        rw [Real.cos_pi]
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos zero_lt_one_ax) Real.sin_one_pos
      rw [heq]; exact ne_of_lt hneg
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    obtain ⟨hrange', hkpi', hpi1'⟩ := ih hwf_cs'
    have hlevel_ge : nestedLo cs' ≤ nestedLevel cs' := by
      have h1 := hkpi' 1 (Nat.le_refl 1)
      have e1 : natCast 1 = (1 : Real) := by
        rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
      rw [e1, one_mul_thm] at h1
      have hr := (hrange' pi).1
      rwa [h1] at hr
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [nestedLo_cons, nestedTarget_cons, nestedHi_cons]
      have hgx := hrange' x
      have hclo_le : c + nestedLo cs' ≤ c + nestedTarget cs' x := add_le_add_left hgx.1 c
      have hc_gx_pos : (0 : Real) < c + nestedTarget cs' x := lt_of_lt_of_le hwf_c hclo_le
      have hchi_le : c + nestedTarget cs' x ≤ c + nestedHi cs' := add_le_add_left hgx.2 c
      exact ⟨log_mono hwf_c hclo_le, log_mono hc_gx_pos hchi_le⟩
    · intro k hk
      rw [nestedTarget_cons, nestedLevel_cons, hkpi' k hk]
    · rw [nestedTarget_cons, nestedLevel_cons]
      intro hcontra
      have hpos1 : (0 : Real) < c + nestedTarget cs' (pi + 1) := by
        have hge := (hrange' (pi + 1)).1
        exact lt_of_lt_of_le hwf_c (add_le_add_left hge c)
      have hpos2 : (0 : Real) < c + nestedLevel cs' :=
        lt_of_lt_of_le hwf_c (add_le_add_left hlevel_ge c)
      have hstep1 : c + nestedTarget cs' (pi + 1) = c + nestedLevel cs' :=
        log_injective_pos hpos1 hpos2 hcontra
      have el : (c + nestedTarget cs' (pi + 1)) - c = nestedTarget cs' (pi + 1) := by mach_ring
      have er : (c + nestedLevel cs') - c = nestedLevel cs' := by
        rw [add_comm c (nestedLevel cs')]
        exact add_sub_cancel_right (nestedLevel cs') c
      have e : (c + nestedTarget cs' (pi + 1)) - c = (c + nestedLevel cs') - c := by rw [hstep1]
      rw [el, er] at e
      exact hpi1' e

/-- **No finite tree realizes any member of the nested-target family, given its own validity.**
The whole point of this file: this covers `cs = []` (`sin` itself), `cs = [c2]`
(`log(c2+sin x)`), `cs = [d, c2]` (`log(d+log(c2+sin x))`), and every deeper nesting, in ONE
proof — not one hand-derivation per level. `EMLPfaffianValidOn T1` remains an explicit,
undischarged hypothesis; see the file docstring for what that still leaves open. -/
theorem no_tree_eq_nested_target_given_validon
    (cs : List Real) (hwf : nestedWF cs) (T1 : EMLTree)
    (hT1eq : ∀ x, T1.eval x = nestedTarget cs x)
    (hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b) :
    False := by
  obtain ⟨_, hkpi, hpi1⟩ := nestedTarget_facts cs hwf
  exact no_tree_eq_target_given_validon (nestedTarget cs) (nestedLevel cs) hkpi hpi1 T1 hT1eq
    hvalidon_any_b

/-- **Sanity check**: `cs = [c2]` recovers exactly
`T1_not_eq_log_c2_plus_sin_given_validon`'s statement (`WitnessResidualChainSkeleton.lean`) via
the general family theorem, confirming the abstraction is equivalent to — not just superficially
similar to — the original hand-proved result it's meant to generalize. -/
theorem T1_not_eq_log_c2_plus_sin_given_validon_via_family
    (c2 : Real) (hc2 : 1 < c2) (T1 : EMLTree)
    (hT1eq : ∀ x, T1.eval x = Real.log (c2 + Real.sin x))
    (hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b) :
    False := by
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hwf : nestedWF [c2] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < c2 + (-1)
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e]; exact hc2m1_pos
  have hT1eq' : ∀ x, T1.eval x = nestedTarget [c2] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_nil]
    exact hT1eq x
  exact no_tree_eq_nested_target_given_validon [c2] hwf T1 hT1eq' hvalidon_any_b

end MachLib
