import MachLib.EMLPfaffian
import MachLib.MultiVarTwoExpSum

/-!
# Differentiability away from log-clamp crossings

Toward closing `eml_pfaffian_validon_from_sin_equality`/`_from_cos_equality` (see the dated notes
in `EMLPfaffian.lean` after `eml_gap_avoidance` and `eml_continuousAt_of_sin_eq`). Rounds 3
(compactness/IVT) and 4 (free derivative transfer at the root) both found the same obstruction:
nothing ties an INTERIOR subtree back to a known-bounded/regular target function the way the ROOT
is tied to `sin`/`cos`.

This file attacks the problem from a different angle: instead of needing FULL validity (strict
positivity of a log-argument throughout an interval) to get continuity of an `eml` node, it's
enough to avoid landing EXACTLY on the clamp boundary (`t2.eval x ≠ 0`) at the point in question —
`MachLib.Real.log` is differentiable on EITHER side of `0` (`HasDerivAt_log_pos` for `>0`, the newly
derived `HasDerivAt_log_neg` for `<0`), just via different rules. This is a strictly WEAKER, purely
LOCAL, structural condition (`EMLNoCrossingAt`) than `EMLPfaffianValidOn`, provable by ordinary
structural induction with NO circularity (a subtree's own `EMLNoCrossingAt` never needs its
sibling's or parent's validity).

**Honest scope:** this does not, by itself, close either axiom — see the dated note at the bottom.
It sharpens exactly where the remaining difficulty lives: not "is `t2.eval` continuous" (answered
here, for free, away from crossings) but "does `t2.eval` ever actually reach `≤ 0` at all" (the
`EMLNoCrossingAt`-violating case), which still needs a global argument.
-/

namespace MachLib

open Real
open MachLib.MultiVarMod.TwoExp (neg_lt_neg)

/-- No internal `eml` node's log-argument is EXACTLY `0` at `x`. Strictly WEAKER than
`EMLPfaffianValidOn s a b` (which needs strict POSITIVITY of every log-argument throughout an
*interval*): this only rules out landing on log's clamp boundary at *this one point*, and never
mentions siblings/ancestors — a genuinely local, non-circular structural condition. -/
def EMLNoCrossingAt : EMLTree → Real → Prop
  | .const _,   _ => True
  | .var,       _ => True
  | .eml t1 t2, x => EMLNoCrossingAt t1 x ∧ EMLNoCrossingAt t2 x ∧ t2.eval x ≠ 0

/-- An `eml t1 t2` node is differentiable at `x`, given its children are and its own log-argument
isn't exactly `0` there — via `HasDerivAt_log_pos` (argument `> 0`) or `HasDerivAt_log_neg`
(argument `< 0`), whichever side of the clamp boundary applies. -/
theorem eml_hasDerivAt_away_from_crossing {t1 t2 : EMLTree} {x a b : Real}
    (h1 : HasDerivAt t1.eval a x) (h2 : HasDerivAt t2.eval b x) (hne : t2.eval x ≠ 0) :
    ∃ c : Real, HasDerivAt (EMLTree.eml t1 t2).eval c x := by
  have hexp : HasDerivAt (fun y => Real.exp (t1.eval y)) (Real.exp (t1.eval x) * a) x :=
    HasDerivAt_comp Real.exp t1.eval a (Real.exp (t1.eval x)) x h1 (HasDerivAt_exp _)
  rcases lt_total (t2.eval x) 0 with hlt | heq | hgt
  · have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (0 * b) x :=
      HasDerivAt_comp Real.log t2.eval b 0 x h2 (HasDerivAt_log_neg hlt)
    exact ⟨_, HasDerivAt_sub _ _ _ _ x hexp hlog⟩
  · exact absurd heq hne
  · have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (1 / t2.eval x * b) x :=
      HasDerivAt_comp Real.log t2.eval b (1 / t2.eval x) x h2 (HasDerivAt_log_pos _ hgt)
    exact ⟨_, HasDerivAt_sub _ _ _ _ x hexp hlog⟩

/-- **Differentiability away from crossings.** Any `EMLTree` is differentiable at `x` provided no
internal log-argument lands exactly on `0` there — by ordinary structural induction, no circularity
(the base cases `const`/`var` are unconditionally differentiable; the `eml` step only needs its
immediate children's differentiability, from the induction hypothesis, plus the local
`t2.eval x ≠ 0` side condition). -/
theorem eml_hasDerivAt_of_no_crossing (s : EMLTree) (x : Real) (h : EMLNoCrossingAt s x) :
    ∃ c : Real, HasDerivAt s.eval c x := by
  induction s with
  | const c => exact ⟨0, HasDerivAt_const c x⟩
  | var => exact ⟨1, HasDerivAt_id x⟩
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨h1, h2, hne⟩ := h
    obtain ⟨a, ha⟩ := ih1 h1
    obtain ⟨b, hb⟩ := ih2 h2
    exact eml_hasDerivAt_away_from_crossing ha hb hne

/-- Corollary: continuity away from crossings, via `hasDerivAt_continuousAt`. -/
theorem eml_continuousAt_of_no_crossing (s : EMLTree) (x : Real) (h : EMLNoCrossingAt s x) :
    ContinuousAt s.eval x :=
  (eml_hasDerivAt_of_no_crossing s x h).elim (fun _ hc => hasDerivAt_continuousAt hc)

/-! ## `log` is unbounded ABOVE too — the mirror of `log_unbounded_below`

`log_unbounded_below` (`EMLPfaffian.lean`) says `log` blows up to `-∞` as its argument `→ 0⁺`. The
blow-up-propagation argument below also needs the mirror fact: `log` blows up to `+∞` as its
argument `→ +∞`. Same derivation shape as `log_lt_of_lt_exp`/`log_unbounded_below`, just with the
inequality reversed. -/

/-- **`log` is unbounded above.** For any target `M`, there is a threshold `δ := exp M > 0` such
that every `y > δ` has `log y > M`. -/
theorem log_unbounded_above (M : Real) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, δ < y → M < Real.log y := by
  refine ⟨Real.exp M, Real.exp_pos M, fun y hy => ?_⟩
  have hypos : (0 : Real) < y := lt_trans_ax (Real.exp_pos M) hy
  have heq : Real.exp (Real.log y) = y := Real.exp_log hypos
  apply exp_reflect_lt
  rw [heq]
  exact hy

/-! ## Depth-2 blow-up: a crossing forces the composition arbitrarily low

The mechanism `eml_gap_avoidance` already uses (an `eml` node's own value bounded above forces its
log-argument away from a small gap, via `exp ≥ 0` absorbing the OTHER child) composes: if `s3`
(two levels down) takes a small enough positive value at `y`, `eml s2 s3` is forced arbitrarily
LARGE at `y` (again via `exp(s2.eval y) ≥ 0`, regardless of `s2`), and THEN `log` of that large
value is forced arbitrarily large too, forcing `eml t1 (eml s2 s3)` arbitrarily NEGATIVE at `y` —
regardless of `t1`'s value there, chosen pointwise. Two nested applications of `log`'s
unboundedness. -/

/-- **Depth-2 blow-up.** For any target `L`, there is a threshold `δ > 0` (depending on `y`'s
already-fixed `t1.eval y`/`s2.eval y`, chosen internally) such that `s3.eval y` landing in
`(0, δ)` forces `eml t1 (eml s2 s3)` below `L` at `y` — regardless of `t1` or `s2`'s actual
values there. -/
theorem eml_depth2_blowup (t1 s2 s3 : EMLTree) (y L : Real) :
    ∃ δ : Real, 0 < δ ∧ (0 < s3.eval y → s3.eval y < δ →
      (EMLTree.eml t1 (EMLTree.eml s2 s3)).eval y < L) := by
  obtain ⟨δ2, hδ2pos, hM2⟩ := log_unbounded_above (Real.exp (t1.eval y) - L + 1)
  obtain ⟨δ1, hδ1pos, hM1⟩ := log_unbounded_below (-δ2)
  refine ⟨δ1, hδ1pos, fun hpos hlt => ?_⟩
  have hlog3 : Real.log (s3.eval y) < -δ2 := hM1 (s3.eval y) hpos hlt
  have hexp_pos : (0 : Real) < Real.exp (s2.eval y) := Real.exp_pos _
  have hstep1 : δ2 < -Real.log (s3.eval y) := by
    have h2 := neg_lt_neg hlog3
    rwa [show -(-δ2) = δ2 from by mach_ring] at h2
  have hstep2 : -Real.log (s3.eval y) < Real.exp (s2.eval y) - Real.log (s3.eval y) := by
    have h2 := add_lt_add_left hexp_pos (-Real.log (s3.eval y))
    rwa [add_zero,
      show -Real.log (s3.eval y) + Real.exp (s2.eval y)
        = Real.exp (s2.eval y) - Real.log (s3.eval y)
        from by mach_mpoly [Real.log (s3.eval y), Real.exp (s2.eval y)]] at h2
  have ht2gap : δ2 < (EMLTree.eml s2 s3).eval y := by
    show δ2 < Real.exp (s2.eval y) - Real.log (s3.eval y)
    exact lt_trans_ax hstep1 hstep2
  have hlog2 : Real.exp (t1.eval y) - L + 1 < Real.log ((EMLTree.eml s2 s3).eval y) :=
    hM2 ((EMLTree.eml s2 s3).eval y) ht2gap
  show Real.exp (t1.eval y) - Real.log ((EMLTree.eml s2 s3).eval y) < L
  have h2 := neg_lt_neg hlog2
  have h3 := add_lt_add_left h2 (Real.exp (t1.eval y))
  rw [show Real.exp (t1.eval y) + -(Real.log ((EMLTree.eml s2 s3).eval y))
        = Real.exp (t1.eval y) - Real.log ((EMLTree.eml s2 s3).eval y)
        from by mach_mpoly [Real.exp (t1.eval y), Real.log ((EMLTree.eml s2 s3).eval y)],
      show Real.exp (t1.eval y) + -(Real.exp (t1.eval y) - L + 1) = L - 1
        from by mach_mpoly [Real.exp (t1.eval y), L]] at h3
  have hlt1 : L - 1 < L := by
    have h4 := add_lt_add_left (neg_neg_of_pos zero_lt_one_ax) L
    rwa [add_zero, show L + -1 = L - 1 from by mach_ring] at h4
  exact lt_trans_ax h3 hlt1

end MachLib
