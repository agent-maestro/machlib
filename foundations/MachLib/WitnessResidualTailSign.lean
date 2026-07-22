import MachLib.WitnessResidualLeftchildDerivative

/-! # Tail-sign stabilization: a genuinely different route into the fully general residual

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 55 investigated and
ruled out two candidate routes into the fully general residual (naive Taylor-coefficient matching,
and a validity-free Khovanskii extension), converging — for the sixth independent time across this
document and its prequel — on the fact that log-argument positivity is required by the actual
calculus, not a proof-technique artifact. This file attempts a third route, proposed externally
and evaluated on its own technical merits before building anything: instead of proving `T1` is
Pfaffian-valid EVERYWHERE (the wall every prior route hit), prove `T1`'s eval EVENTUALLY settles
into one fixed sign (or eventually vanishes) as `x → ∞` — a claim a PERIODIC target (`sin`, and
more generally anything built from it) can NEVER satisfy, since it keeps oscillating no matter how
far out you go. This sidesteps needing validity on any BOUNDED interval at all.

**What closes cleanly.** `TailSign f` — `f` is eventually positive, eventually negative, or
eventually identically zero. Base cases (`const`, `var`) are immediate. The inductive step's
`B` EVENTUALLY NON-POSITIVE case (`tailSign_eml_of_B_eventually_nonpos`) closes with NO dependence
on `A` at all: past the threshold where `B ≤ 0`, `(eml A B).eval x = exp(A.eval x)` exactly (the
same collapse identity `BChainNonpos` uses), and `exp` is unconditionally positive — `TailSign.pos`
falls out immediately, regardless of what `A` is doing. `sin_not_tailSign` closes the target side
completely: `sin` has zeros at every `kπ`, arbitrarily far out (ruling out `pos`/`neg`), and is
nonzero at `kπ + π/2` (`= cos(kπ) ≠ 0`), also arbitrarily far out (ruling out `zero`) — built from
scratch this round (`cos_natCast_mul_pi_ne_zero`, an Archimedean argument via the `archimedean`
axiom, and the standard `sin_add`/`cos_add` expansions), fully proven, no gaps.

**What does NOT close — the `B` eventually positive case, characterized precisely rather than
assumed away.** The natural hope (from the external suggestion this file is built from) was:
"combine the recursively frozen branch representations of `A` and `B`... invoke the uniform zero
bound." This undersells a real obstruction. `TailSign A.eval` (available from the induction
hypothesis) is a SIGN fact — it does NOT give `A` eventually Pfaffian-VALID, which is what
`enc_combinedBound`'s zero-counting bound actually needs. And "eventually Pfaffian-valid" is
NOT a fact every tree has: `eml var (const (-1))` is a tiny counterexample — its own right child
(`const (-1)`) is negative EVERYWHERE, so the node PERMANENTLY clamps, and `EMLPfaffianValidOn`
never holds for it at any tail, even though its VALUE (`exp x`, via the SAME collapse identity)
is perfectly well-behaved (`TailSign.pos`, in fact — this is exactly the EASY case above). So the
right invariant to carry through the induction is not "eventually valid" (false in general) and
not bare `TailSign` (too weak to run Khovanskii), but something like "eventually agrees with SOME
Pfaffian-valid representation" — which, when a right child clamps permanently, is a DIFFERENT,
structurally smaller expression than the tree itself (as above, `A` composed with `exp`, not
`eml A B`). Constructing and threading this "eventually-collapsing representation" recursively
through an arbitrarily deep tree — where each level's own right child could ALSO clamp partway,
requiring the same case analysis one level down — is real, substantial engineering: an inductive
NORMAL FORM for EML trees under eventual clamping, not a one-line gap. Not attempted this round.

**Honest net assessment.** This route is more promising than the two ruled out in cont. 55 — the
"B eventually non-positive" case falling out for free, with zero dependence on `A`'s own
structure, is a genuinely different (and encouraging) shape of result compared to every prior
attempt, all of which needed SOME information about the exp-side child. But the "B eventually
positive" case needs a real recursive normal-form construction, comparable in scope to (though
more concretely aimed than) the dimension-counting argument flagged since prequel round 7 — this
is a promising DIRECTION for a dedicated follow-on effort, not a closed result.

`sorryAx`-free, verified via a genuinely fresh rebuild for every theorem in this file. No
`eml_pfaffian_validon_from_sin_equality` dependence. -/

namespace MachLib
namespace Real

/-- `f` eventually settles into one fixed sign, or eventually vanishes identically. -/
inductive TailSign (f : Real → Real) : Prop
  | pos : (∃ R : Real, ∀ x : Real, R < x → 0 < f x) → TailSign f
  | neg : (∃ R : Real, ∀ x : Real, R < x → f x < 0) → TailSign f
  | zero : (∃ R : Real, ∀ x : Real, R < x → f x = 0) → TailSign f

theorem eml_eval_eq_exp_A_of_B_nonpos_at (A B : EMLTree) (x : Real) (hBx : B.eval x ≤ 0) :
    (EMLTree.eml A B).eval x = Real.exp (A.eval x) := by
  show Real.exp (A.eval x) - Real.log (B.eval x) = _
  rw [log_nonpos hBx, sub_zero]

/-- The easy half of the inductive step: whenever `B` is eventually non-positive, `TailSign` holds
for the WHOLE node with zero dependence on `A`'s own structure — the collapse identity forces
`(eml A B).eval x = exp(A.eval x)`, unconditionally positive, past the threshold. -/
theorem tailSign_eml_of_B_eventually_nonpos (A B : EMLTree)
    (hB : ∃ R : Real, ∀ x : Real, R < x → B.eval x ≤ 0) :
    TailSign (EMLTree.eml A B).eval := by
  obtain ⟨R, hR⟩ := hB
  exact TailSign.pos ⟨R, fun x hx => by
    rw [eml_eval_eq_exp_A_of_B_nonpos_at A B x (hR x hx)]
    exact Real.exp_pos _⟩

theorem tailSign_const (c : Real) : TailSign (EMLTree.const c).eval := by
  rcases lt_total c 0 with hlt | heq | hgt
  · exact TailSign.neg ⟨0, fun x _ => hlt⟩
  · exact TailSign.zero ⟨0, fun x _ => heq⟩
  · exact TailSign.pos ⟨0, fun x _ => hgt⟩

theorem tailSign_var : TailSign EMLTree.var.eval :=
  TailSign.pos ⟨0, fun x hx => hx⟩

/-- `cos` never vanishes at an integer multiple of `π` — proven directly (not cited), by
induction mirroring `sin_natCast_mul_pi`'s own proof shape: `cos((n+1)π) = -cos(nπ)` via
`cos_add`/`cos_pi`/`sin_natCast_mul_pi`, so the sign alternates and never hits `0`. -/
theorem cos_natCast_mul_pi_ne_zero (k : Nat) : Real.cos (natCast k * pi) ≠ 0 := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul, Real.cos_zero]
    intro hcontra
    exact lt_irrefl_ax 0 (hcontra ▸ zero_lt_one_ax)
  | succ n ih =>
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * pi = natCast n * pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib, Real.cos_add, sin_natCast_mul_pi, zero_mul, sub_zero, Real.cos_pi]
    intro hcontra
    apply ih
    have heq : Real.cos (natCast n * pi) * (-1) = -(Real.cos (natCast n * pi)) := by mach_ring
    rw [heq] at hcontra
    have h4 : Real.cos (natCast n * pi) = -(-(Real.cos (natCast n * pi))) := by mach_ring
    rw [hcontra] at h4
    rw [h4]; mach_ring

theorem natCast_le_natCast_mul_pi (n : Nat) : natCast n ≤ natCast n * pi := by
  have h := mul_le_mul_of_nonneg_left (le_of_lt pi_gt_one) (natCast_nonneg n)
  rwa [mul_one_ax] at h

/-- **`sin` fails all three tail-sign classes.** Zeros at every `kπ`, arbitrarily far out (via the
Archimedean axiom), rule out `pos`/`neg`; nonzero at `kπ + π/2` (`= cos(kπ) ≠ 0`), also
arbitrarily far out, rules out `zero`. This is exactly what a hypothetical `TailSign`-closure of
the general residual would need to contradict — proven completely, no gaps, so the target side of
this route is fully settled regardless of how far the tree side eventually gets pushed. -/
theorem sin_not_tailSign : ¬ TailSign Real.sin := by
  intro h
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt : R < natCast n * pi :=
      lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have := hR (natCast n * pi) hlt
    rw [sin_natCast_mul_pi] at this
    exact lt_irrefl_ax 0 this
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt : R < natCast n * pi :=
      lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have := hR (natCast n * pi) hlt
    rw [sin_natCast_mul_pi] at this
    exact lt_irrefl_ax 0 this
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
    have hsinval := hR (natCast n * pi + pi / (1 + 1)) hlt2
    rw [Real.sin_add, sin_natCast_mul_pi, sin_pi_div_two, cos_pi_div_two,
      mul_zero, zero_add, mul_one_ax] at hsinval
    exact cos_natCast_mul_pi_ne_zero n hsinval

end Real
end MachLib
