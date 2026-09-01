/-
# A specimen for the INTERVAL theorem — and a false absence, corrected

`(gd)` inherited a real gap: `log_not_rational_on_interval` concludes `False`, so it lives in the
class `witness_audit.py` excludes by design, and a refutation whose structural hypotheses cannot be
satisfied refutes nothing.

**But the first draft of this module claimed `PIrred` had never been witnessed in 55 sites. That was
FALSE.** `MachLib/GermClearedSpecimen.lean` has proved `pIrred_X` since the cleared-relation arc, and
its header states the same discipline in the same words — *"conditional on a pole hypothesis set
that, until now, nobody had ever instantiated"* — having found two hypotheses there that were
genuinely unsatisfiable. The duplicate `pIrred_X` written here was caught by `lake build`, not by me:
`environment already contains 'MachLib.pIrred_X._proof_1_1'`.

The search that produced the false claim was broken twice over: the pattern `PIrred \[` cannot match
the actual text `PIrred ([0, 1] : List Real)`, and the exit code was read off `head` rather than
`grep` through a pipe. Both failures are already written down in this repo's own gotchas.

**What is genuinely new here** is narrow and worth keeping: a specimen for the *interval* theorem,
which did not exist before `(gd)`. `GermClearedSpecimen` instantiates the germ/cleared-relation arc;
nothing instantiated `log_not_rational_on_interval`. It reuses that module's `pIrred_X` rather than
re-proving it.
-/
import MachLib.LogNotRationalInterval
import MachLib.PolyConstDvd
import MachLib.PolyMulDegree
import MachLib.GermClearedSpecimen

namespace MachLib

open Real

/-- **The specimen: `log (1/x)` is not a rational function on `(1,2)`.**

`log_not_rational_on_interval` concludes `False`, so the witness audit cannot check it — and a
refutation whose structural hypotheses are unsatisfiable refutes nothing. This instantiates every one
of them concretely: `P = 1`, `Q = q = x`, `r = 0`, `Qt = 1`, interval `(1,2)`.

`PIrred` is a hypothesis at 40 sites in this corpus and `pIrred_X` above is its first witness. -/
theorem log_recip_not_rational_on_unit_interval
    (N D : List Real) (hNn : PNormal N) (hDne : pnorm D ≠ [])
    (hlow : Pdvd [(0 : Real), 1] D → ¬ Pdvd [(0 : Real), 1] N)
    (hD0 : ∀ x : Real, 1 < x → x < 1 + 1 → pev D x ≠ 0)
    (hlog : ∀ x : Real, 1 < x → x < 1 + 1 →
      log (pev [(1 : Real)] x / pev [(0 : Real), 1] x) = pev N x / pev D x) :
    False := by
  have hone : pnorm [(1 : Real)] ≠ [] := by
    have : pnorm [(1 : Real)] = [(1 : Real)] := by
      refine pnorm_eq_self _ ?_
      intro c hc
      have hc1 : c = 1 := by simpa using hc.symm
      rw [hc1]; exact Real.one_ne_zero
    rw [this]; simp
  have hnd : ¬ Pdvd [(0 : Real), 1] [(1 : Real)] := not_Pdvd_const pIrred_X hone (by simp)
  have hPn : PNormal [(1 : Real)] := by
    intro c hc
    have hc1 : c = 1 := by simpa using hc.symm
    rw [hc1]; exact Real.one_ne_zero
  -- pev [0,1] x = x, so it is non-zero on (1,2)
  have hQ0 : ∀ x : Real, 1 < x → x < 1 + 1 → pev [(0 : Real), 1] x ≠ 0 := by
    intro x h1 _ hz
    have hx : pev [(0 : Real), 1] x = x := by show 0 + x * (1 + x * 0) = x; mach_ring
    rw [hx] at hz
    exact (Real.ne_of_lt (Real.lt_trans_ax Real.zero_lt_one_ax h1)) hz.symm
  have hP0 : ∀ x : Real, 1 < x → x < 1 + 1 → pev [(1 : Real)] x ≠ 0 := by
    intro x _ _ hz
    have h1 : pev [(1 : Real)] x = 1 := by show 1 + x * 0 = 1; mach_ring
    rw [h1] at hz
    exact Real.one_ne_zero hz
  have hpos : ∀ x : Real, 1 < x → x < 1 + 1 → 0 < pev [(1 : Real)] x / pev [(0 : Real), 1] x := by
    intro x h1 _
    have hx : pev [(0 : Real), 1] x = x := by show 0 + x * (1 + x * 0) = x; mach_ring
    have h1' : pev [(1 : Real)] x = 1 := by show 1 + x * 0 = 1; mach_ring
    rw [hx, h1']
    exact one_div_pos_of_pos (Real.lt_trans_ax Real.zero_lt_one_ax h1)
  -- Q = q^1 * 1, i.e. the multiplicity of x in x is exactly one
  have hQfac : PEq [(0 : Real), 1] (pmul (ppow [(0 : Real), 1] (0 + 1)) [(1 : Real)]) := by
    have e2 : PEq (pmul (pmul [(0 : Real), 1] [(1 : Real)]) [(1 : Real)])
        (pmul [(0 : Real), 1] [(1 : Real)]) :=
      PEq.trans (peq_pmul_comm _ [(1 : Real)]) (peq_pmul_one_left _)
    have e1 : PEq (pmul [(0 : Real), 1] [(1 : Real)]) [(0 : Real), 1] :=
      PEq.trans (peq_pmul_comm _ [(1 : Real)]) (peq_pmul_one_left _)
    exact PEq.symm (PEq.trans e2 e1)
  have h11 : (1 : Real) < 1 + 1 := by
    have h := Real.add_lt_add_left Real.zero_lt_one_ax (1 : Real)
    rwa [Real.add_zero] at h
  exact log_not_rational_on_interval (r := 0) h11 pIrred_X hnd hPn hNn
    hQfac hnd hDne hlow hQ0 hD0 hP0 hpos hlog

end MachLib
