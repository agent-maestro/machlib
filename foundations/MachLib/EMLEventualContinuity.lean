import MachLib.EMLSignFromNonzero

/-!
# Eventual continuity is bookkeeping, not an obligation

`evSign_of_hard` reduces sign-definiteness of every EML tree to `SignHardCase`, and
`evSign_of_continuous_nonzero_on_ray` converts *continuous + non-vanishing on a ray* into `EvSign`.
Wiring the second into the first needs continuity of `exp (A x) − log (B x)`, and the earlier attempt
to supply it went through `EMLNoCrossingAt` — a condition recursive over the whole tree, demanding
`t2.eval x ≠ 0` at **every** node, while `SignHardCase` offers positivity of the **top-level** log
argument only.

This module shows the gap was in the *route*, not in the obligation.

## What the induction already has

Read `evSign_of_hard`'s `eml A B` case: the context holds exactly one verdict, `ihB : EvSign B.eval`,
and `ihA` is discarded. Nothing nested. But the nested verdicts are not missing — they are produced
**at their own nodes**: every nested log argument is the right child of some `eml a b` the same
induction visits, and there its own `ihB` is precisely the branch verdict for it. The information
never has to be transported to the root.

So continuity can be carried as a **second conjunct of the induction's own conclusion**
(`EvSign t.eval ∧ EvCont t.eval`) and proved with immediate-children hypotheses alone
(`evSignCont_of_cts`). Nothing about `SignHardCase` is strengthened to get it; on the contrary, the
skeleton's hypothesis `SignHardCts` is `SignHardCase` **plus** a continuity hypothesis at the node,
hence implied by it (`signHardCts_of_hard`) — a weaker demand.

## Why this is weaker than `EMLNoCrossingAt`, and where

`EMLNoCrossingAt` asks `t2.eval x ≠ 0` pointwise. `EvSign` gives a branch verdict on a ray, and each
branch is continuous for a *different* reason:

| branch | why `log ∘ B` is continuous | `EMLNoCrossingAt` |
| --- | --- | --- |
| `0 < B.eval` on the ray | `log` is continuous at positive points; only the single point `x` is used | implied (`> 0` gives `≠ 0`) |
| `B.eval ≤ 0` on the ray | `log ∘ B ≡ 0` there, so it is *locally constant* | **fails** at any `B.eval x = 0` |

The clamped row is the one that matters: the totalisation makes `log ∘ B` constant, so exact zeros of
`B` are harmless, and a condition phrased as non-vanishing rejects a case that is perfectly well
behaved. Note the asymmetry in what each branch consumes — the positive branch needs the verdict at
one point, the clamped branch needs it on a whole neighbourhood. That is what forces §2's shift.

## The endpoint shift is load-bearing

`EvSign` and `EvCont` rays are **closed** (`X₀ ≤ x`), and `ContinuousAt` is a **two-sided** property.
At the endpoint `X₀` itself there is no left neighbourhood on which the clamped branch's local
constancy is known, so the argument is simply false there. `ray_shift_nbhd` states the fix once: the
radius-`1` ball around any `x ≥ X₀ + 1` stays inside `[X₀, ∞)`, so continuity is claimed from
`X₀ + 1` onward. Kept as a named lemma rather than inlined because a silently dropped endpoint is a
failure mode this corpus has already paid for.

## What the module does *not* claim

`SignHardCase` stays **open** and no ledger row moves. Two obligations are stated here and neither is
registered:

* `SignHardNonzero` — pure eventual non-vanishing. **REFUTED** by `not_signHardNonzero`
  (`EMLSignZeroProducer`): `exp ∘ exp ∘ A` is a tree, is positive everywhere, and makes the node value
  identically `0`, so no ray is free of zeros. Everything below taking it as a hypothesis
  (`signHardCts_of_nonzero`, `evSign_of_nonzero`, `evCont_of_nonzero`, `nonzeroOrClamped_of_nonzero`)
  is therefore **vacuous** — true, and useless. Kept as the record of the step. The reading that it is
  "a sufficient condition, stronger than `SignHardCase`" was right about the direction and wrong about
  the value: a false sufficient condition is no obligation at all. The usable form conditions on not
  being eventually zero — `SignHardUniformZeroBound` in `EMLSignZeroProducer`.
* `SignHardNonzeroOrClamped` — the same statement with the clamped case restored as a disjunct. This
  one **is** implied by `SignHardCase` (`nonzeroOrClamped_of_hard`) as well as implying it through
  the skeleton, so it is debt-neutral: the honest form of "all that is missing is zero control".

The genuinely new unconditional-in-the-old-hypothesis fact is `evCont_of_hard`: `SignHardCase` by
itself already makes every EML tree eventually continuous. Continuity was never a second mathematical
frontier.
-/

namespace MachLib

open Real

/-! ## §0 — tree values as functions

`EMLTree.eval` computes by `match`, so `(EMLTree.eml A B).eval` and the explicit lambda are
definitionally equal but not syntactically so. These three `rfl`s let `rw` move between them. -/

private theorem eml_eval_fun (A B : EMLTree) :
    (EMLTree.eml A B).eval = fun x => exp (A.eval x) - log (B.eval x) := by
  funext x; rfl

private theorem const_eval_fun (c : Real) : (EMLTree.const c).eval = fun _ => c := by
  funext x; rfl

private theorem var_eval_fun : (EMLTree.var).eval = fun x => x := by
  funext x; rfl

/-! ## §1 — the stable-clamped continuity lemma

The one piece of genuinely new analysis, and it needs no differentiability of `g`. Where `g ≤ 0`
throughout a neighbourhood the totalised `log ∘ g` *is* the constant `0` on that neighbourhood, so
continuity is immediate — at `g x = 0` exactly as much as at `g x < 0`.

There is no derivative twin: `MachLib.HasDerivAt` is an opaque `axiom`, with no local-congruence rule
to transfer `HasDerivAt (fun _ => 0) 0 x` across an agreement neighbourhood. That is the concrete
reason `EvCont` below carries `ContinuousAt` and not `HasDerivAt` — the existing derivative-based
node lemma `eml_hasDerivAt_away_from_crossing` cannot serve the clamped branch at all. -/

/-- **Stable-clamped continuity.** If `g ≤ 0` throughout the ball of radius `r` about `x`, then
`fun y => log (g y)` is continuous at `x`. Includes the boundary case `g x = 0`, which is exactly
where `EMLNoCrossingAt` gives up. -/
theorem continuousAt_log_comp_of_nonpos_nbhd {g : Real → Real} {x r : Real}
    (hr : 0 < r) (hnp : ∀ y : Real, abs (y - x) < r → g y ≤ 0) :
    ContinuousAt (fun y => log (g y)) x := by
  intro ε hε
  refine ⟨r, hr, fun y hy => ?_⟩
  show abs (log (g y) - log (g x)) < ε
  have hx0 : abs (x - x) < r := by rw [sub_self, abs_zero]; exact hr
  rw [log_nonpos (hnp y hy), log_nonpos (hnp x hx0), sub_self, abs_zero]
  exact hε

/-! ## §2 — `EvCont`, ray joins, and the endpoint shift -/

/-- **Eventually continuous** — continuous at every point of some ray `[X₀, ∞)`, `X₀ ≥ 1`. Same ray
convention as `EvSign`, so the two conjuncts of the induction below join without conversion. -/
def EvCont (f : Real → Real) : Prop :=
  ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → ContinuousAt f x

/-- Two rays with base `≥ 1` have a common refinement. -/
private theorem ray_join2 {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

/-- `X ≤ X + 1`. -/
private theorem le_add_one (X : Real) : X ≤ X + 1 := by
  have v := add_le_add_wit (le_refl X) (le_of_lt zero_lt_one_ax)
  have e : X + 0 = X := by mach_ring
  rw [e] at v; exact v

/-- **The endpoint shift.** A fact known on the *closed* ray `[X, ∞)` is available on a genuine
two-sided neighbourhood of every point of `[X + 1, ∞)`: the radius-`1` ball about `x ≥ X + 1` stays
inside `[X, ∞)`.

`ContinuousAt` is two-sided, so this is not bookkeeping. At `x = X` itself the clamped branch's
local-constancy argument has no left neighbourhood to run on and is false as stated. -/
theorem ray_shift_nbhd {X x y : Real} (hx : X + 1 ≤ x) (hy : abs (y - x) < 1) : X ≤ y := by
  obtain ⟨_, hlow⟩ := abs_lt_split hy
  have v := add_lt_add_left hlow x
  have e1 : x + -(1 : Real) = x - 1 := by mach_ring
  have e2 : x + (y - x) = y := by mach_mpoly [x, y]
  rw [e1, e2] at v
  have hX : X ≤ x - 1 := by
    have w := add_le_add_wit hx (le_refl (-(1 : Real)))
    have e3 : X + 1 + -(1 : Real) = X := by mach_ring
    have e4 : x + -(1 : Real) = x - 1 := by mach_ring
    rw [e3, e4] at w; exact w
  exact le_of_lt (lt_of_le_of_lt hX v)

/-! ## §3 — the node step -/

/-- Difference of continuous functions. `continuousAt_sub` exists in `GaussianConjugacy` but is
`private`; reproved here from the public `continuousAt_add`/`continuousAt_neg`. -/
private theorem continuousAt_sub' {f g : Real → Real} {x : Real}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => f y - g y) x := by
  have e : (fun y => f y - g y) = (fun y => f y + -(g y)) := by
    funext y; mach_ring
  rw [e]
  exact continuousAt_add hf (continuousAt_neg hg)

/-- **The weaker continuity lemma.** One `eml` node is eventually continuous given both children's
eventual continuity and the **right** child's eventual sign verdict — the branch verdict, not
non-vanishing.

This is the replacement for the `EMLNoCrossingAt` route. Contrast the two branches: the positive one
consumes the verdict at the single point `x`, the clamped one on the whole radius-`1` ball, which is
why the conclusion's ray is `X + 1` and not `X`. -/
theorem evCont_eml_of_evSign_right {A B : EMLTree}
    (hA : EvCont A.eval) (hB : EvCont B.eval) (hsB : EvSign B.eval) :
    EvCont (EMLTree.eml A B).eval := by
  obtain ⟨XA, hXA1, hcA⟩ := hA
  obtain ⟨XB, hXB1, hcB⟩ := hB
  obtain ⟨XS, hXS1, hsign⟩ : ∃ X : Real, 1 ≤ X ∧
      ((∀ x : Real, X ≤ x → 0 < B.eval x) ∨ (∀ x : Real, X ≤ x → B.eval x ≤ 0)) := by
    rcases hsB with ⟨X, h1, hp⟩ | ⟨X, h1, hn⟩
    · exact ⟨X, h1, Or.inl hp⟩
    · exact ⟨X, h1, Or.inr hn⟩
  obtain ⟨X1, hX11, hX1A, hX1B⟩ := ray_join2 hXA1 hXB1
  obtain ⟨X, hX1, hXX1, hXXS⟩ := ray_join2 hX11 hXS1
  refine ⟨X + 1, le_trans hX1 (le_add_one X), ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_add_one X) hx
  have hxA : ContinuousAt A.eval x := hcA x (le_trans hX1A (le_trans hXX1 hxX))
  have hxB : ContinuousAt B.eval x := hcB x (le_trans hX1B (le_trans hXX1 hxX))
  have hexp : ContinuousAt (fun y => exp (A.eval y)) x :=
    continuousAt_comp hxA (hasDerivAt_continuousAt (HasDerivAt_exp (A.eval x)))
  have hlog : ContinuousAt (fun y => log (B.eval y)) x := by
    rcases hsign with hp | hn
    · exact continuousAt_comp hxB
        (hasDerivAt_continuousAt (HasDerivAt_log_pos _ (hp x (le_trans hXXS hxX))))
    · exact continuousAt_log_comp_of_nonpos_nbhd zero_lt_one_ax
        (fun y hy => hn y (le_trans hXXS (ray_shift_nbhd hx hy)))
  rw [eml_eval_fun A B]
  exact continuousAt_sub' hexp hlog

/-! ## §4 — the conjunctive induction, once

`SignHardCts` is `SignHardCase` with a continuity hypothesis added at the node. More hypotheses, same
conclusion: it is **implied by** `SignHardCase`, so nothing is strengthened by routing through it. The
skeleton discharges that hypothesis itself, which is the whole point — continuity is manufactured,
not assumed. -/

/-- **`SignHardCase`, handed the continuity it needs.** Weaker than `SignHardCase` (see
`signHardCts_of_hard`); the skeleton below supplies the extra hypothesis at every call site. -/
def SignHardCts : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    EvCont (fun x => exp (A.eval x) - log (B.eval x)) →
    EvSign (fun x => exp (A.eval x) - log (B.eval x))

/-- **The skeleton.** `EvSign` and `EvCont` advance together, node by node. Only immediate-children
hypotheses are used: the `EvCont` conjunct at an `eml` node takes both children's continuity and the
right child's *own* sign verdict, so no nested information is ever transported upward.

`ihA` — discarded in `evSign_of_hard`, because the left child's sign is genuinely irrelevant there —
is used here for the left child's *continuity*. -/
theorem evSignCont_of_cts (h : SignHardCts) :
    ∀ t : EMLTree, EvSign t.eval ∧ EvCont t.eval := by
  intro t
  induction t with
  | const c =>
      refine ⟨?_, ?_⟩
      · rcases lt_total 0 c with hc | hc | hc
        · exact Or.inl ⟨1, le_refl 1, fun x _ => hc⟩
        · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_eq hc.symm⟩
        · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_lt hc⟩
      · refine ⟨1, le_refl 1, fun x _ => ?_⟩
        rw [const_eval_fun c]
        exact continuousAt_const c x
  | var =>
      refine ⟨Or.inl ⟨1, le_refl 1, fun x hx => lt_of_lt_of_le zero_lt_one_ax hx⟩, ?_⟩
      refine ⟨1, le_refl 1, fun x _ => ?_⟩
      rw [var_eval_fun]
      exact hasDerivAt_continuousAt (HasDerivAt_id x)
  | eml A B ihA ihB =>
      obtain ⟨_, hcA⟩ := ihA
      obtain ⟨hsB, hcB⟩ := ihB
      have hcN : EvCont (EMLTree.eml A B).eval := evCont_eml_of_evSign_right hcA hcB hsB
      refine ⟨?_, hcN⟩
      rcases hsB with ⟨XB, hXB1, hpos⟩ | ⟨XB, hXB1, hnp⟩
      · -- the hard branch: continuity is now in hand, so the obligation need not ask for it
        rw [eml_eval_fun A B] at hcN ⊢
        exact h A B XB hXB1 hpos hcN
      · -- the clamped branch, exactly as in `evSign_of_hard`: the node is `exp (A x)`, positive
        refine Or.inl ⟨XB, hXB1, ?_⟩
        intro x hx
        show 0 < exp (A.eval x) - log (B.eval x)
        rw [log_nonpos (hnp x hx)]
        have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
        rw [e]
        exact exp_pos _

/-! ## §5 — instances

Three obligations feed the skeleton. `SignHardCase` is the existing one; the other two are stated
here and **neither is registered in the ledger**. -/

/-- `SignHardCase` implies the continuity-enriched form — drop the extra hypothesis. -/
theorem signHardCts_of_hard (h : SignHardCase) : SignHardCts :=
  fun A B X₀ hX₀ hpos _ => h A B X₀ hX₀ hpos

/-- **Continuity was never a second frontier.** The *existing* obligation already makes every EML
tree eventually continuous, with nothing added. -/
theorem evCont_of_hard (h : SignHardCase) : ∀ t : EMLTree, EvCont t.eval :=
  fun t => (evSignCont_of_cts (signHardCts_of_hard h) t).2

/-- **Pure eventual non-vanishing** — the shape a zero-counting engine produces, and the same shape
`OneQueryDichotomy` needs.

**REFUTED — see `not_signHardNonzero` (`EMLSignZeroProducer`).** `expExpTree A` is positive
everywhere and drives the node value to `0` everywhere, so no ray is free of zeros. Every theorem
below that assumes this is vacuous; use `SignHardNonzeroOrClamped`, whose second disjunct absorbs
exactly that counterexample, or the conditioned `SignHardUniformZeroBound`.

Retained because the step is worth recording: the obligation was not merely stronger than
`SignHardCase` (which it is), it was unsatisfiable. -/
def SignHardNonzero : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    ∃ R : Real, 1 ≤ R ∧ ∀ x : Real, R ≤ x → exp (A.eval x) - log (B.eval x) ≠ 0

/-- Non-vanishing plus the manufactured continuity, through `evSign_of_continuous_nonzero_on_ray`. -/
theorem signHardCts_of_nonzero (h : SignHardNonzero) : SignHardCts := by
  intro A B X₀ hX₀ hpos hcont
  obtain ⟨R, hR1, hne⟩ := h A B X₀ hX₀ hpos
  obtain ⟨Xc, hXc1, hcc⟩ := hcont
  obtain ⟨S, hS1, hSR, hSc⟩ := ray_join2 hR1 hXc1
  exact evSign_of_continuous_nonzero_on_ray hS1
    (fun x hx => hne x (le_trans hSR hx))
    (fun x hx => hcc x (le_trans hSc hx))

/-- The drop-in analogue of `evSign_of_hard` with the sign obligation replaced by a non-vanishing one
— **vacuous**, since `SignHardNonzero` is refuted (`not_signHardNonzero`). The live version is
`evSign_of_uniformBounds` in `EMLSignZeroProducer`. -/
theorem evSign_of_nonzero (h : SignHardNonzero) : ∀ t : EMLTree, EvSign t.eval :=
  fun t => (evSignCont_of_cts (signHardCts_of_nonzero h) t).1

/-- The continuity half of the same instance — likewise vacuous. -/
theorem evCont_of_nonzero (h : SignHardNonzero) : ∀ t : EMLTree, EvCont t.eval :=
  fun t => (evSignCont_of_cts (signHardCts_of_nonzero h) t).2

/-- **The form that survives.** Eventual non-vanishing *or* the clamped case, restored as a disjunct.
The identically-zero counterexample that refutes `SignHardNonzero` satisfies the **second** disjunct
rather than falsifying this, so the disjunct is load-bearing, not decorative.
Unlike `SignHardNonzero` this is implied by `SignHardCase` (`nonzeroOrClamped_of_hard`) as well as
implying it via the skeleton, so it neither strengthens nor weakens the obligation — it says exactly
"all that is missing is zero control, on the branch where zero control is what is missing". -/
def SignHardNonzeroOrClamped : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    ∃ R : Real, 1 ≤ R ∧
      ((∀ x : Real, R ≤ x → exp (A.eval x) - log (B.eval x) ≠ 0)
        ∨ (∀ x : Real, R ≤ x → exp (A.eval x) - log (B.eval x) ≤ 0))

/-- The disjunctive form also feeds the skeleton: the first disjunct through the IVT bridge, the
second directly into `EvSign`'s own second disjunct. -/
theorem signHardCts_of_nonzeroOrClamped (h : SignHardNonzeroOrClamped) : SignHardCts := by
  intro A B X₀ hX₀ hpos hcont
  obtain ⟨R, hR1, hd⟩ := h A B X₀ hX₀ hpos
  rcases hd with hne | hnp
  · obtain ⟨Xc, hXc1, hcc⟩ := hcont
    obtain ⟨S, hS1, hSR, hSc⟩ := ray_join2 hR1 hXc1
    exact evSign_of_continuous_nonzero_on_ray hS1
      (fun x hx => hne x (le_trans hSR hx))
      (fun x hx => hcc x (le_trans hSc hx))
  · exact Or.inr ⟨R, hR1, hnp⟩

/-- And it is implied by `SignHardCase` — the direction `SignHardNonzero` does **not** have. The
positive disjunct of `EvSign` gives non-vanishing; the non-positive disjunct is carried across
verbatim. -/
theorem nonzeroOrClamped_of_hard (h : SignHardCase) : SignHardNonzeroOrClamped := by
  intro A B X₀ hX₀ hpos
  rcases h A B X₀ hX₀ hpos with ⟨R, hR1, hp⟩ | ⟨R, hR1, hn⟩
  · refine ⟨R, hR1, Or.inl (fun x hx he => ?_)⟩
    have hlt : 0 < exp (A.eval x) - log (B.eval x) := hp x hx
    rw [he] at hlt
    exact lt_irrefl_ax 0 hlt
  · exact ⟨R, hR1, Or.inr hn⟩

/-- `SignHardNonzero` is the stronger of the two zero-control forms — vacuously, now that it is
refuted. The content of the pair is entirely in `nonzeroOrClamped_of_hard`. -/
theorem nonzeroOrClamped_of_nonzero (h : SignHardNonzero) : SignHardNonzeroOrClamped := by
  intro A B X₀ hX₀ hpos
  obtain ⟨R, hR1, hne⟩ := h A B X₀ hX₀ hpos
  exact ⟨R, hR1, Or.inl hne⟩

end MachLib
