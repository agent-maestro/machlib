import MachLib.WitnessResidualEventualValidTailSign

/-!
# The recursive normal-form closure: `TailSign` holds unconditionally for every tree

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). `WitnessResidualTailSign.lean`
closed the "`B` eventually non-positive" case of the `TailSign` induction with zero dependence on
`A`, but flagged the "`B` eventually positive" case as needing a real recursive normal-form
construction: `TailSign A.eval`/`TailSign B.eval` (the natural induction hypotheses) are VALUE
facts, but `evalid_tailSign` (`WitnessResidualEventualValidTailSign.lean`) needs a VALIDITY fact
(`EMLPfaffianValidOn` on a tail) to fire — and "eventually valid" is FALSE for some trees with
perfectly good `TailSign` (`eml var (const (-1))`'s own right child clamps permanently, so
`EMLPfaffianValidOn` never holds for it at any tail, even though its value is `exp x`).

**The construction that closes it.** Strengthen the induction hypothesis from bare `TailSign` to
`eml_eventually_valid_repr`: every tree `T` has a REPRESENTATIVE tree `Trep` that (a) is eventually
Pfaffian-valid, and (b) has `Trep.eval` eventually equal to `T.eval` pointwise. `TailSign T.eval`
then falls out as a direct corollary via `evalid_tailSign Trep` plus transport across eventual
equality (`tailSign_congr_eventually`). The representative is built by structural induction:

- `const`/`var`: the tree IS its own representative (trivially valid everywhere).
- `eml A B`, `B` eventually non-positive (via IH-derived `TailSign Brep.eval`, transported to
  `B.eval`): `T`'s value collapses to `exp(A.eval ·)` past the threshold (the same identity
  `tailSign_eml_of_B_eventually_nonpos` uses). Representative: `eml Arep (const 1)` — `log 1 = 0`
  makes this compute to `exp(Arep.eval ·)` exactly, and the `const 1` slot is trivially valid AND
  trivially positive everywhere, so validity reduces PURELY to `Arep`'s (already established by
  IH), with no new obstruction from `B` at all.
- `eml A B`, `B` eventually positive: representative is simply `eml Arep Brep` — both children's
  own representatives, combined. Validity needs a COMMON tail exceeding both `Arep`'s and `Brep`'s
  own validity thresholds AND the point past which `Brep.eval = B.eval` AND `B` itself is
  positive (`EMLPfaffianValidOn_mono_a` handles shrinking each side's tail down to the common
  point; `lt_of_lt_four` picks a point exceeding all four thresholds at once).

**Payoff.** `eml_tailSign_unconditional : ∀ T, TailSign T.eval` — no hypothesis, no axiom,
`sorryAx`-free. Combined with `sin_not_tailSign` (already proven, `WitnessResidualTailSign.lean`),
this gives `no_tree_eq_sin_unconditional`: **no finite EML tree's `eval` function equals `sin`
pointwise everywhere** — completely unconditionally, with NO dependence on
`eml_pfaffian_validon_from_sin_equality` or `EMLPfaffianValidOn` at any point, and NOT routed
through `no_tree_eq_target_given_validon`'s `hvalidon_any_b` hypothesis at all (that hypothesis is
never discharged here — this is a genuinely different, more direct route to the same conclusion
for the `sin` instance specifically). Generalizing to the full `nestedTarget` family is the natural
next step (not attempted this round): the underlying "periodic ⟹ no TailSign" argument should
carry over since `nestedTarget` is itself built from `sin`, but that has not been checked.
-/

namespace MachLib
namespace Real

/-- Validity on `(a,b)` transports to any smaller-from-the-left interval `(a',b)` with `a ≤ a'` —
shrinking the interval only removes constraints from the universally-quantified positivity
condition. Needed to combine two subtrees' own (possibly different) eventual-validity thresholds
into one common tail. -/
theorem EMLPfaffianValidOn_mono_a {s : EMLTree} {a a' b : Real} (haa' : a ≤ a')
    (h : EMLPfaffianValidOn s a b) : EMLPfaffianValidOn s a' b := by
  induction s with
  | const c => trivial
  | var => trivial
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨ih1 h1, ih2 h2, fun x hxa hxb => h3 x (lt_of_le_of_lt haa' hxa) hxb⟩

/-- A point exceeding all four of a given quadruple of reals, built via three applications of
`lt_of_lt_both` (which itself avoids ever needing `max`). -/
theorem lt_of_lt_four (p q r s : Real) : ∃ M : Real, p < M ∧ q < M ∧ r < M ∧ s < M := by
  obtain ⟨M1, hp1, hq1⟩ := lt_of_lt_both p q
  obtain ⟨M2, h1M2, hr2⟩ := lt_of_lt_both M1 r
  obtain ⟨M3, h2M3, hs3⟩ := lt_of_lt_both M2 s
  exact ⟨M3, lt_trans_ax (lt_trans_ax hp1 h1M2) h2M3,
    lt_trans_ax (lt_trans_ax hq1 h1M2) h2M3,
    lt_trans_ax hr2 h2M3,
    hs3⟩

/-- **`TailSign` transports across eventual pointwise equality.** If `f` and `g` agree past some
`R0`, `f`'s tail behavior IS `g`'s tail behavior. -/
theorem tailSign_congr_eventually {f g : Real → Real} (R0 : Real)
    (heq : ∀ x : Real, R0 < x → f x = g x) (hf : TailSign f) : TailSign g := by
  rcases hf with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨M, hRM, hR0M⟩ := lt_of_lt_both R R0
    exact TailSign.pos ⟨M, fun x hx => by
      have h1 := hR x (lt_trans_ax hRM hx)
      rw [heq x (lt_trans_ax hR0M hx)] at h1
      exact h1⟩
  · obtain ⟨M, hRM, hR0M⟩ := lt_of_lt_both R R0
    exact TailSign.neg ⟨M, fun x hx => by
      have h1 := hR x (lt_trans_ax hRM hx)
      rw [heq x (lt_trans_ax hR0M hx)] at h1
      exact h1⟩
  · obtain ⟨M, hRM, hR0M⟩ := lt_of_lt_both R R0
    exact TailSign.zero ⟨M, fun x hx => by
      have h1 := hR x (lt_trans_ax hRM hx)
      rw [heq x (lt_trans_ax hR0M hx)] at h1
      exact h1⟩

/-- The "`B` eventually non-positive" collapse case of the representative construction, factored
out since it's shared verbatim between `TailSign.neg` and `TailSign.zero` on `B` (both imply
`B.eval x ≤ 0` eventually). `Arep`'s own representative is reused unchanged; the collapse tree is
`eml Arep (const 1)`, whose validity depends ONLY on `Arep`'s (the `const 1` slot is trivially
valid and trivially positive everywhere), and whose value matches `T.eval` past the later of
`Arep`'s equality threshold and `B`'s non-positivity threshold. -/
theorem eml_collapse_repr (A B Arep : EMLTree) (aA RA : Real)
    (hAvalid : ∀ b : Real, aA < b → EMLPfaffianValidOn Arep aA b)
    (hAeq : ∀ x : Real, RA < x → Arep.eval x = A.eval x)
    (hBnonpos : ∃ R : Real, ∀ x : Real, R < x → B.eval x ≤ 0) :
    ∃ (Trep : EMLTree) (a : Real),
      (∀ b : Real, a < b → EMLPfaffianValidOn Trep a b) ∧
      (∃ R : Real, ∀ x : Real, R < x → Trep.eval x = (EMLTree.eml A B).eval x) := by
  obtain ⟨R, hR⟩ := hBnonpos
  refine ⟨EMLTree.eml Arep (EMLTree.const 1), aA, ?_, ?_⟩
  · intro b hab
    refine ⟨hAvalid b hab, trivial, ?_⟩
    intro x _ _
    show (0 : Real) < (1 : Real)
    exact zero_lt_one_ax
  · obtain ⟨M, hRAM, hRM⟩ := lt_of_lt_both RA R
    refine ⟨M, fun x hx => ?_⟩
    have hxRA : RA < x := lt_trans_ax hRAM hx
    have hxR : R < x := lt_trans_ax hRM hx
    show Real.exp (Arep.eval x) - Real.log (1 : Real) = (EMLTree.eml A B).eval x
    rw [eml_eval_eq_exp_A_of_B_nonpos_at A B x (hR x hxR), log_one, sub_zero, hAeq x hxRA]

/-- **Every tree has an eventually-valid representative matching its eventual value.** The
recursive normal form under eventual clamping, flagged as substantial follow-on engineering in
`WitnessResidualTailSign.lean`. -/
theorem eml_eventually_valid_repr (T : EMLTree) :
    ∃ (Trep : EMLTree) (a : Real),
      (∀ b : Real, a < b → EMLPfaffianValidOn Trep a b) ∧
      (∃ R : Real, ∀ x : Real, R < x → Trep.eval x = T.eval x) := by
  induction T with
  | const c => exact ⟨EMLTree.const c, 0, fun _ _ => trivial, 0, fun _ _ => rfl⟩
  | var => exact ⟨EMLTree.var, 0, fun _ _ => trivial, 0, fun _ _ => rfl⟩
  | eml A B ihA ihB =>
    obtain ⟨Arep, aA, hAvalid, RA, hAeq⟩ := ihA
    obtain ⟨Brep, aB, hBvalid, RB, hBeq⟩ := ihB
    have hBrepTS : TailSign Brep.eval := evalid_tailSign Brep aB hBvalid
    have hBTS : TailSign B.eval := tailSign_congr_eventually RB hBeq hBrepTS
    rcases hBTS with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
    · -- B eventually positive: combine both representatives directly.
      obtain ⟨a0, haA0, haB0, haR0, haRB0⟩ := lt_of_lt_four aA aB R RB
      refine ⟨EMLTree.eml Arep Brep, a0, ?_, ?_⟩
      · intro b hab
        have hAvalid' : EMLPfaffianValidOn Arep a0 b :=
          EMLPfaffianValidOn_mono_a (le_of_lt haA0) (hAvalid b (lt_trans_ax haA0 hab))
        have hBvalid' : EMLPfaffianValidOn Brep a0 b :=
          EMLPfaffianValidOn_mono_a (le_of_lt haB0) (hBvalid b (lt_trans_ax haB0 hab))
        refine ⟨hAvalid', hBvalid', ?_⟩
        intro x hx0 _hxb
        have hxR : R < x := lt_trans_ax haR0 hx0
        have hxRB : RB < x := lt_trans_ax haRB0 hx0
        have hpos : 0 < B.eval x := hR x hxR
        rw [← hBeq x hxRB] at hpos
        exact hpos
      · obtain ⟨M, hRAM, hRBM⟩ := lt_of_lt_both RA RB
        refine ⟨M, fun x hx => ?_⟩
        show Real.exp (Arep.eval x) - Real.log (Brep.eval x) = (EMLTree.eml A B).eval x
        rw [hAeq x (lt_trans_ax hRAM hx), hBeq x (lt_trans_ax hRBM hx)]
        rfl
    · -- B eventually negative ⟹ ≤ 0: collapse.
      exact eml_collapse_repr A B Arep aA RA hAvalid hAeq ⟨R, fun x hx => le_of_lt (hR x hx)⟩
    · -- B eventually zero ⟹ ≤ 0: collapse (same shape).
      exact eml_collapse_repr A B Arep aA RA hAvalid hAeq ⟨R, fun x hx => le_of_eq (hR x hx)⟩

/-- **The payoff: `TailSign` holds unconditionally for every EML tree.** No hypothesis. -/
theorem eml_tailSign_unconditional (T : EMLTree) : TailSign T.eval := by
  obtain ⟨Trep, a, hvalid, R, heq⟩ := eml_eventually_valid_repr T
  have hTS : TailSign Trep.eval := evalid_tailSign Trep a hvalid
  exact tailSign_congr_eventually R heq hTS

/-- **No finite EML tree's `eval` function equals `sin` pointwise everywhere — unconditionally.**
No dependence on `EMLPfaffianValidOn` holding anywhere, no dependence on
`eml_pfaffian_validon_from_sin_equality`, no dependence on any hypothesis at all: every tree has
SOME fixed eventual sign or eventual zero (`eml_tailSign_unconditional`), `sin` has none
(`sin_not_tailSign`), so no tree can match it. -/
theorem no_tree_eq_sin_unconditional (T : EMLTree) (heq : ∀ x : Real, T.eval x = Real.sin x) :
    False :=
  sin_not_tailSign (tailSign_congr_eventually 0 (fun x _ => heq x) (eml_tailSign_unconditional T))

end Real
end MachLib
