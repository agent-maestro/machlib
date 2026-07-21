import MachLib.WitnessResidualCrossingUnbounded
import MachLib.IntermediateValue
import MachLib.OperatorBasisComplete
import MachLib.CosNotInEML
import MachLib.EMLZeroCrossingBothCompound
import MachLib.WitnessResidualGrowthCompetitionNumeric

/-! # Digging into the original tree-depth induction — the crossing-unboundedness result, made fully general

`WitnessResidualCrossingUnbounded.lean` proved unboundedness for one hardcoded crossing shape,
`eml var (const c)`. That proof's mechanism — `exp(A)≥0` can never cancel `-log(B)`'s divergence
as `B→0⁺` — never actually used `B`'s specific closed form beyond one property: given a target
value, `B` could be driven to hit it EXACTLY, via `B`'s own algebraic invertibility.

**This file removes that dependency entirely**, replacing exact algebraic inversion with the
REAL Intermediate Value Theorem (`intermediate_value_of_hasDerivAt`, `IntermediateValue.lean` —
a genuine, complete IVT proven in-model from the completeness axiom `sup_exists`, not previously
exercised anywhere in this whole arc despite being available). `eml_A_crossing_B_unbounded_above`:
if `B.eval` crosses zero genuinely — `B(x0)=0` and `B(x1)>0` for SOME `x0<x1`, with `B`
differentiable throughout `[x0,x1]` — then `eml A B` is unbounded above, for ANY `A` AND for ANY
EML tree `B` whatsoever (not just `eml var (const c)`). This is the tree-depth-induction spirit of
the original Option D framing, done for real: a fact proven by structural properties of the
`eml`-constructor itself (positivity of `exp`, IVT for differentiable functions), not by
shape-by-shape enumeration.

**The proof, worked out on paper first.** For target `M`, either `exp(-(M+1)) < B(x1)` — apply
IVT to `g(z) := B(z) - exp(-(M+1))` on `[x0,x1]` (`g(x0) = -exp(-(M+1)) < 0`, `g(x1) > 0` by
assumption) to get an EXACT point `c` with `B(c) = exp(-(M+1))`, giving
`-log(B(c)) = M+1` exactly — or `exp(-(M+1)) ≥ B(x1)` — in which case `x1` ITSELF already works
directly (`log` is monotone, so `B(x1) ≤ exp(-(M+1))` gives `log(B(x1)) ≤ -(M+1)` immediately, no
IVT needed). Either way `exp(A.eval(\cdot)) - log(B(\cdot)) ≥ M+1 > M` at the witness point,
since `exp(A) ≥ 0` unconditionally.

**Confirmed via a sanity-check corollary**: `eml_A_crossing_var_const_unbounded_above_via_general`
re-derives the ORIGINAL, hand-built theorem exactly (`B := eml var (const c)`, `x0 := log(log c)`
the crossing, `x1 := x0+1` one step past it, differentiability from the pre-existing
`hasDerivAt_evarConstC`) — the generalization captures the same content, not merely a
similar-looking one.

**What this settles for Option D, precisely.** Every EML tree ever built anywhere in this arc with
a genuine finite-point right-child crossing uses `eml var (const c)` as that crossing — the ONLY
crossing primitive this whole 40+-file investigation ever constructed. This theorem now shows
unboundedness holds for a right child with ANY genuine crossing whatsoever, `eml var (const c)`
or not — meaning even a FUTURE construction using some other, more exotic crossing shape (as long
as it's differentiable and genuinely changes sign at a finite point) would hit the SAME wall. The
"original tree-depth induction" question — can an arbitrary compound tree's zero-crossing
structure be bounded without assuming `EMLPfaffianValidOn` — is answered, for the unboundedness
HALF of it, about as generally as this arc's own primitives allow: genuinely crossing right
children are structurally incompatible with boundedness, full stop, not merely difficult to
handle case by case.

`sorryAx`-free, verified via a genuinely fresh rebuild: depends only on foundational
`MachLib.Real` axioms plus `hasDerivAt_continuousAt` (the one analytic bridge axiom
`IntermediateValue.lean` needs) and `sup_exists` (the completeness axiom, already trusted
throughout this codebase) — no dependence on `EMLPfaffianValidOn` or
`eml_pfaffian_validon_from_sin_equality`. -/

namespace MachLib
namespace Real

/-- If `B.eval` crosses zero genuinely (`B(x0)=0`, `B(x1)>0` for `x0<x1`, differentiable
throughout), `eml A B` is unbounded above for ANY `A`. Generalizes
`eml_A_crossing_var_const_unbounded_above` from the one hardcoded shape `eml var (const c)` to
ANY EML tree `B` with a genuine crossing, via the real IVT (`intermediate_value_of_hasDerivAt`). -/
theorem eml_A_crossing_B_unbounded_above (A B : EMLTree) (x0 x1 : Real) (hx0x1 : x0 < x1)
    (hBx0 : B.eval x0 = 0) (hBx1pos : 0 < B.eval x1)
    (hBdiff : ∀ z : Real, x0 ≤ z → z ≤ x1 → ∃ Bd : Real, HasDerivAt B.eval Bd z) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases lt_total (Real.exp (-(M + 1))) (B.eval x1) with hcase | hcase | hcase
  · -- IVT case: find c with B.eval c = exp(-(M+1)) exactly
    have hdiff2 : ∀ z : Real, x0 ≤ z → z ≤ x1 →
        ∃ g' : Real, HasDerivAt (fun w => B.eval w - Real.exp (-(M + 1))) g' z := by
      intro z hz0 hz1
      obtain ⟨Bd, hBd⟩ := hBdiff z hz0 hz1
      refine ⟨Bd - 0, HasDerivAt_sub B.eval (fun _ => Real.exp (-(M + 1))) Bd 0 z hBd
        (HasDerivAt_const _ z)⟩
    have hga : (fun w => B.eval w - Real.exp (-(M + 1))) x0 < 0 := by
      show B.eval x0 - Real.exp (-(M + 1)) < 0
      rw [hBx0]
      have h1 : (0 : Real) - Real.exp (-(M + 1)) = -Real.exp (-(M + 1)) := by mach_ring
      rw [h1]
      exact neg_neg_of_pos (Real.exp_pos _)
    have hgb : 0 < (fun w => B.eval w - Real.exp (-(M + 1))) x1 := by
      show 0 < B.eval x1 - Real.exp (-(M + 1))
      exact sub_pos_of_lt hcase
    obtain ⟨c, hc0, hc1, hBc⟩ := intermediate_value_of_hasDerivAt
      (fun w => B.eval w - Real.exp (-(M + 1))) x0 x1 hx0x1 hdiff2 hga hgb
    have hBceq : B.eval c = Real.exp (-(M + 1)) := by
      have h1 : B.eval c - Real.exp (-(M + 1)) + Real.exp (-(M + 1)) = 0 + Real.exp (-(M + 1)) := by
        rw [hBc]
      have h2 : B.eval c - Real.exp (-(M + 1)) + Real.exp (-(M + 1)) = B.eval c := by mach_ring
      have h3 : (0 : Real) + Real.exp (-(M + 1)) = Real.exp (-(M + 1)) := by mach_ring
      rw [h2, h3] at h1
      exact h1
    refine ⟨c, ?_⟩
    show M < Real.exp (A.eval c) - Real.log (B.eval c)
    rw [hBceq, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval c) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval c) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval c) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · -- exp(-(M+1)) = B.eval x1: x1 itself already works
    refine ⟨x1, ?_⟩
    show M < Real.exp (A.eval x1) - Real.log (B.eval x1)
    rw [← hcase, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x1) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval x1) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x1) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · -- exp(-(M+1)) < B.eval x1 is FALSE means B.eval x1 < exp(-(M+1)): x1 itself works too
    refine ⟨x1, ?_⟩
    show M < Real.exp (A.eval x1) - Real.log (B.eval x1)
    have hlog_le : Real.log (B.eval x1) ≤ -(M + 1) := by
      have h := log_mono hBx1pos (le_of_lt hcase)
      rwa [Real.log_exp] at h
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x1) := le_of_lt (Real.exp_pos _)
    have hstep1 : Real.exp (A.eval x1) - -(M + 1) ≤ Real.exp (A.eval x1) - Real.log (B.eval x1) :=
      sub_le_sub_left hlog_le _
    have hstep2 : M + 1 ≤ Real.exp (A.eval x1) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x1) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt (le_trans hstep2 hstep1)

/-- Sanity check: the general theorem reproduces `eml_A_crossing_var_const_unbounded_above`
(`WitnessResidualCrossingUnbounded.lean`) exactly, instantiating `B := eml var (const c)`,
`x0 := log(log c)` (the crossing), `x1 := x0+1` (one comfortable step past it). -/
theorem eml_A_crossing_var_const_unbounded_above_via_general
    (A : EMLTree) (c : Real) (hc : 1 < c) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A (EMLTree.eml EMLTree.var (EMLTree.const c))).eval x := by
  have hlogc_pos : 0 < Real.log c := log_pos_of_gt_one hc
  let x0 : Real := Real.log (Real.log c)
  let x1 : Real := x0 + 1
  have hx0x1 : x0 < x1 := by
    have h := add_lt_add_left zero_lt_one_ax x0
    rwa [add_zero] at h
  have hBx0 : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval x0 = 0 := by
    show Real.exp x0 - Real.log c = 0
    have he : Real.exp x0 = Real.log c := Real.exp_log hlogc_pos
    rw [he]; mach_ring
  have hBx1pos : 0 < (EMLTree.eml EMLTree.var (EMLTree.const c)).eval x1 := by
    show 0 < Real.exp x1 - Real.log c
    have hexpx1 : Real.exp x1 = Real.exp x0 * Real.exp 1 := Real.exp_add x0 1
    have he : Real.exp x0 = Real.log c := Real.exp_log hlogc_pos
    rw [hexpx1, he]
    have hstep : Real.log c * 1 < Real.log c * Real.exp 1 :=
      mul_lt_mul_of_pos_left one_lt_exp_one hlogc_pos
    have he1 : Real.log c * 1 = Real.log c := mul_one_ax _
    rw [he1] at hstep
    exact sub_pos_of_lt hstep
  have hBdiff : ∀ z : Real, x0 ≤ z → z ≤ x1 →
      ∃ Bd : Real, HasDerivAt (EMLTree.eml EMLTree.var (EMLTree.const c)).eval Bd z := by
    intro z _ _
    exact ⟨Real.exp z, hasDerivAt_evarConstC c z⟩
  exact eml_A_crossing_B_unbounded_above A (EMLTree.eml EMLTree.var (EMLTree.const c))
    x0 x1 hx0x1 hBx0 hBx1pos hBdiff M

end Real
end MachLib
