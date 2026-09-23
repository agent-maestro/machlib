import MachLib.EMLGermInvariance

/-!
# The comparability preorder — and why it has no bottom

`EmlGermApproachResearch.md` §5(3): *a Hardy-field valuation / comparability class rather than a
height integer.* §7 says why the idea is the right shape — EML germs are Hardy
logarithmico-exponential germs, and the comparability class is the invariant that theory actually
uses. This file defines the relation and runs the discipline §5 asks for: **well-foundedness
first, fixtures second, floor last.**

```
CompLe g h  :=  ∃ c > 0, ∃ X ≥ 1, ∀ x ≥ X,  log (g x) ≤ c · log (h x)
```

— the `log |g| = O(log |h|)` of the note, with the corpus's totalised `log` in place of `log | · |`
(which is what the EML grammar supplies, and what makes `§4`'s meeting fixture readable at all).
`CompLt g h := CompLe g h ∧ ¬ CompLe h g`.

## Verdict 1 — it is a preorder, and its strict part is NOT well-founded

`compLe_refl` and `compLe_trans` make it a genuine preorder, so `CompLt` is irreflexive and is a
candidate strict order rather than something degenerate.

And then it fails the first test:

```
compLt_deepDecay :  CompLt (deepDecay (m+1)).eval (deepDecay m).eval,  for every m
compLt_not_wf    :  ¬ WellFounded CompLt
```

> **`deepDecay` is an infinite strictly descending chain.** The family §3 built to pin the floor
> height from below — `exp (1 − towerFn (m+1) x)`, depth `m + 4` — is, read in the comparability
> order, exactly an `ω*`. So the order has no bottom and no induction on it terminates.

This is the concrete form of the warning §5 carries: *the corpus has a recorded instance of a
dense comparability structure being assumed discrete.* The classes here are not merely dense; they
descend forever, and the thing that indexes the descent is the very floor height the conjecture
asks for.

**What the separation costs, and it is one lemma.** `lin_lt_exp` — `exp` outruns every line, with
the constant given in advance — is the only asymptotic input, and it is where the arbitrary
multiplier `c` in `O(·)` is paid for. It is proved from `exp_gt_two_x` and `exp_log`, no new
axiom and no division: write `c · exp T = exp (log c + T)` and use `exp w > w + w`.

## Verdict 2 — descent is already closed, one file earlier

A comparability class is a function of the germ, so `EMLGermInvariance`'s
`no_germInvariant_wfDescent` applies to it before well-foundedness is ever reached: **no
germ-invariant parameter descends to both children of an `eml` node in any well-founded order.**
The non-well-foundedness above is therefore a second, independent closure of the same route, not
the first one.

The fixtures say the same thing from the inside:

* `compLt_capNode_right` — `capNode n` sits **strictly below its own right child**, at every `n`.
  The node's germ `1 − towerFn n x` is non-positive, so totalised `log` sends it to `0`, while the
  child's log is `towerFn n x`. This is `tower_height_does_not_descend_right` reappearing
  unchanged in the valuation; the class does not descend on the right any more than the growth
  rate did.
* `compEquiv_zero_one` — the meeting boundary is **invisible**. The gap of `eTree (eTree A)` is
  identically `0` (`exact_meeting_gap_zero`) and has no floor at all; the gap of `gapTarget n 1` is
  the constant `1` (`gapTarget_gap`) and meets the height-`0` floor. Totalised `log` sends both to
  `0`, so comparability puts them in the **same class**. A class cannot determine a floor that one
  member has and another does not.

## What the relation does get right, and why it is still not progress

`compLe_floor_of_floor` is one line: a tower floor for `t` **is** a comparability lower bound for
`t`, with `c = 1` and the same `X₁`. So *"`DecayFloor` at depth `j`"* and *"the comparability class
of every eventually-positive depth-`j` germ is bounded below by a tower-reciprocal class,
uniformly in `j`"* say the same thing — the second is the first reindexed. Per §9 that is
bookkeeping, and the converse (absorbing the multiplier `c` by raising the tower height one rung)
is exactly what `lin_lt_exp` supplies, so the reindexing is two-way in the same sense
`reindexing_is_two_way` is. **Candidate 3 does not make the conjecture smaller; it renames it, in
a structure that cannot carry an induction.**

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open. `CompLt` is shown to separate before it is
shown not to well-found (`compLt_deepDecay_one`, the descending chain itself): an order that
related nothing would fail well-foundedness trivially and would prove nothing about the route.
-/

namespace MachLib

open Real

/-! ## §1 — the relation -/

/-- **Comparability.** `log ∘ g` is eventually dominated by a constant multiple of `log ∘ h`. The
germ vocabulary §7 names, transported to the corpus's totalised `log`. -/
def CompLe (g h : Real → Real) : Prop :=
  ∃ c X : Real, 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → log (g x) ≤ c * log (h x)

/-- Same comparability class. -/
def CompEquiv (g h : Real → Real) : Prop := CompLe g h ∧ CompLe h g

/-- Strictly lower class — the relation an induction would descend along. -/
def CompLt (g h : Real → Real) : Prop := CompLe g h ∧ ¬ CompLe h g

theorem compLe_refl (g : Real → Real) : CompLe g g := by
  refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
  intro x _
  rw [one_mul_thm]
  exact le_refl _

theorem compLe_trans {g h k : Real → Real} (h1 : CompLe g h) (h2 : CompLe h k) : CompLe g k := by
  obtain ⟨c1, X1, hc1, hX1, hf1⟩ := h1
  obtain ⟨c2, X2, hc2, hX2, hf2⟩ := h2
  refine ⟨c1 * c2, max X1 X2, mul_pos hc1 hc2, le_trans hX1 (le_max_left _ _), ?_⟩
  intro x hx
  have s1 := hf1 x (le_trans (le_max_left X1 X2) hx)
  have s2 := hf2 x (le_trans (le_max_right X1 X2) hx)
  have s3 : c1 * log (h x) ≤ c1 * (c2 * log (k x)) := mul_le_mul_of_nonneg_left s2 (le_of_lt hc1)
  have e : c1 * (c2 * log (k x)) = c1 * c2 * log (k x) := by mach_ring
  rw [e] at s3
  exact le_trans s1 s3

/-- **So `CompLt` is irreflexive**, and the non-well-foundedness below is not the degenerate kind.
-/
theorem compLt_irrefl (g : Real → Real) : ¬ CompLt g g := fun h => h.2 (compLe_refl g)

/-! ## §2 — the one asymptotic input: `exp` outruns every line

The arbitrary positive multiplier in `O(·)` has to be paid for somewhere, and this is where. No
division, no new axiom: `c · exp T = exp (log c + T)` by `exp_log` and `exp_add`, and
`exp w > w + w` is the corpus's `exp_gt_two_x`. -/

/-- **For every constant `K` and every `c > 0`, `K + T < c · exp T` once `T` is large enough.** -/
theorem lin_lt_exp (c K : Real) (hc : 0 < c) :
    ∃ T₀ : Real, ∀ T : Real, T₀ ≤ T → K + T < c * exp T := by
  refine ⟨max (K - log c) 0 + 1 - log c, ?_⟩
  intro T hT
  have hL : exp (log c) = c := exp_log hc
  have hMw : max (K - log c) 0 + 1 ≤ log c + T := by
    have u := add_le_add_wit (le_refl (log c)) hT
    have e1 : log c + (max (K - log c) 0 + 1 - log c) = max (K - log c) 0 + 1 := by mach_ring
    rw [e1] at u
    exact u
  have hKM : K - log c ≤ max (K - log c) 0 := le_max_left _ _
  have hstep : K - log c + 1 ≤ log c + T :=
    le_trans (add_le_add_wit hKM (le_refl (1 : Real))) hMw
  have hlt1 : K - log c < K - log c + 1 := by
    have u := add_lt_add_left zero_lt_one_ax (K - log c)
    have e0 : K - log c + 0 = K - log c := by mach_ring
    rw [e0] at u
    exact u
  have hKw : K - log c < log c + T := lt_of_lt_of_le hlt1 hstep
  have hsum : K + T < (log c + T) + (log c + T) := by
    have u := add_lt_add_left hKw (log c + T)
    have e1 : (log c + T) + (K - log c) = K + T := by mach_ring
    rw [e1] at u
    exact u
  have hexp : (1 + 1) * (log c + T) < exp (log c + T) := exp_gt_two_x (log c + T)
  have e2 : (1 + 1) * (log c + T) = (log c + T) + (log c + T) := by mach_ring
  rw [e2] at hexp
  have hfin : c * exp T = exp (log c + T) := by rw [exp_add, hL]
  rw [hfin]
  exact lt_of_lt_of_le hsum (le_of_lt hexp)

/-! ## §3 — well-foundedness, refuted -/

/-- `towerFn` is above the identity on the ray. `EMLDecayLadderStep.towerFn_ge_self` says the
same thing but sits further down the import order than this file. -/
private theorem towerFn_ge_self' (m : Nat) {x : Real} (hx : 1 ≤ x) :
    x ≤ EMLTree.towerFn m x := by
  have h := towerFn_mono 0 m hx
  have e : (0 : Nat) + m = m := by omega
  rw [e] at h
  exact h

/-- A well-founded relation admits no infinite descending sequence. -/
theorem no_descending_chain {α : Type} {R : α → α → Prop} (hwf : WellFounded R)
    (f : Nat → α) (hf : ∀ n : Nat, R (f (n + 1)) (f n)) : False := by
  have key : ∀ a : α, ∀ n : Nat, f n ≠ a := by
    intro a
    refine hwf.induction (C := fun a => ∀ n : Nat, f n ≠ a) a ?_
    intro x ih n hn
    have hstep : R (f (n + 1)) x := by rw [← hn]; exact hf n
    exact ih (f (n + 1)) hstep (n + 1) rfl
  exact key (f 0) 0 rfl

theorem log_deepDecay (m : Nat) (x : Real) :
    log ((deepDecay m).eval x) = 1 - EMLTree.towerFn (m + 1) x := by
  rw [deepDecay_eval, log_exp]

/-- **Down one rung.** `deepDecay (m+1)` decays faster, so its log is further below. -/
theorem compLe_deepDecay_succ (m : Nat) :
    CompLe (deepDecay (m + 1)).eval (deepDecay m).eval := by
  refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
  intro x hx
  rw [log_deepDecay, log_deepDecay, one_mul_thm]
  have h := towerFn_le_succ (m + 1) hx
  have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit h)
  have e1 : (1 : Real) + -(EMLTree.towerFn (m + 1 + 1) x)
      = 1 - EMLTree.towerFn (m + 1 + 1) x := by mach_ring
  have e2 : (1 : Real) + -(EMLTree.towerFn (m + 1) x)
      = 1 - EMLTree.towerFn (m + 1) x := by mach_ring
  rw [e1, e2] at u
  exact u

/-- The point separation, with the tower value abstracted so the proof is readable. -/
private theorem deepDecay_sep_point {c T : Real} (hkey : c - 1 + T < c * exp T) :
    c * (1 - exp T) < 1 - T := by
  have u := add_lt_add_left hkey (1 - T - c * exp T)
  have e1 : (1 - T - c * exp T) + (c - 1 + T) = c - c * exp T := by mach_ring
  have e2 : (1 - T - c * exp T) + c * exp T = 1 - T := by mach_ring
  rw [e1, e2] at u
  have e3 : c * (1 - exp T) = c - c * exp T := by mach_ring
  rw [e3]
  exact u

/-- **…and not back up.** No constant multiple of `deepDecay (m+1)`'s log reaches `deepDecay m`'s:
that would need `exp` to be dominated by a line, and `lin_lt_exp` says it is not. -/
theorem not_compLe_deepDecay (m : Nat) :
    ¬ CompLe (deepDecay m).eval (deepDecay (m + 1)).eval := by
  rintro ⟨c, X, hc, hX, hf⟩
  obtain ⟨T₀, hT₀⟩ := lin_lt_exp c (c - 1) hc
  obtain ⟨x, hxX, hx1, hxT⟩ : ∃ x : Real, X ≤ x ∧ (1 : Real) ≤ x ∧ T₀ ≤ x :=
    ⟨max X (max T₀ 1), le_max_left _ _,
      le_trans (le_max_right T₀ 1) (le_max_right X (max T₀ 1)),
      le_trans (le_max_left T₀ 1) (le_max_right X (max T₀ 1))⟩
  have hkey := hT₀ (EMLTree.towerFn (m + 1) x) (le_trans hxT (towerFn_ge_self' (m + 1) hx1))
  have hh := hf x hxX
  rw [log_deepDecay, log_deepDecay] at hh
  have hT2 : EMLTree.towerFn (m + 1 + 1) x = exp (EMLTree.towerFn (m + 1) x) := rfl
  rw [hT2] at hh
  exact (ne_of_lt (lt_of_lt_of_le (deepDecay_sep_point hkey) hh)) rfl

/-- **One rung of the infinite descent**, for every `m`. -/
theorem compLt_deepDecay (m : Nat) :
    CompLt (deepDecay (m + 1)).eval (deepDecay m).eval :=
  ⟨compLe_deepDecay_succ m, not_compLe_deepDecay m⟩

/-- **The comparability order is not well-founded on EML germs.** `deepDecay` is an `ω*`, and it
is the same family that pins the floor height from below at every depth. A relation that is not
well-founded buys nothing, so candidate 3 fails its first test — before any question about the
floor is reached. -/
theorem compLt_not_wf : ¬ WellFounded CompLt := by
  intro hwf
  exact no_descending_chain hwf (fun n => (deepDecay n).eval) compLt_deepDecay

/-! ## §4 — the instrument separates, so the negative verdict is readable

An order relating nothing would fail well-foundedness for free. This one does separate, and it
separates on exactly the axis the conjecture measures: the decaying families sit strictly below
the constants, ordered by their floor height. -/

/-- **Every `deepDecay` is strictly below the constant class.** So the descending chain is a chain
*below* a real element and not an artefact of an empty order. -/
theorem compLt_deepDecay_one (m : Nat) :
    CompLt (deepDecay m).eval (fun _ : Real => (1 : Real)) := by
  constructor
  · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x hx
    rw [log_deepDecay]
    show (1 : Real) - EMLTree.towerFn (m + 1) x ≤ 1 * log (1 : Real)
    rw [log_one, one_mul_thm]
    have h1 : (1 : Real) ≤ EMLTree.towerFn (m + 1) x := towerFn_ge_one (m + 1) hx
    have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit h1)
    have e1 : (1 : Real) + -(EMLTree.towerFn (m + 1) x)
        = 1 - EMLTree.towerFn (m + 1) x := by mach_ring
    have e2 : (1 : Real) + -(1 : Real) = 0 := by mach_ring
    rw [e1, e2] at u
    exact u
  · rintro ⟨c, X, hc, hX, hf⟩
    obtain ⟨x, hxX, hx1⟩ : ∃ x : Real, X ≤ x ∧ (1 : Real) ≤ x :=
      ⟨max X 1, le_max_left _ _, le_max_right _ _⟩
    have hh := hf x hxX
    rw [log_deepDecay] at hh
    show False
    -- `log 1 = 0 ≤ c · (1 − towerFn (m+1) x)`, but the right factor is strictly negative.
    have hT : (1 : Real) < EMLTree.towerFn (m + 1) x := by
      have h0 : (1 : Real) ≤ EMLTree.towerFn m x := towerFn_ge_one m hx1
      have h1 : (0 : Real) < EMLTree.towerFn m x := lt_of_lt_of_le zero_lt_one_ax h0
      have h2 : 1 + EMLTree.towerFn m x < exp (EMLTree.towerFn m x) :=
        exp_gt_one_plus_self _ h1
      have h3 : (1 : Real) < 1 + EMLTree.towerFn m x := by
        have u := add_lt_add_left h1 (1 : Real)
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at u
        exact u
      have hTe : EMLTree.towerFn (m + 1) x = exp (EMLTree.towerFn m x) := rfl
      rw [hTe]
      exact lt_of_lt_of_le h3 (le_of_lt h2)
    have hneg : (1 : Real) - EMLTree.towerFn (m + 1) x < 0 := by
      have u := add_lt_add_left hT (1 - EMLTree.towerFn (m + 1) x - 1)
      have e1 : (1 - EMLTree.towerFn (m + 1) x - 1) + 1
          = 1 - EMLTree.towerFn (m + 1) x - 0 := by mach_ring
      have e2 : (1 - EMLTree.towerFn (m + 1) x - 1) + EMLTree.towerFn (m + 1) x = 0 := by
        mach_ring
      rw [e1, e2] at u
      have e3 : (1 : Real) - EMLTree.towerFn (m + 1) x - 0
          = 1 - EMLTree.towerFn (m + 1) x := by mach_ring
      rw [e3] at u
      exact u
    have hprod : c * (1 - EMLTree.towerFn (m + 1) x) < c * 0 :=
      mul_lt_mul_of_pos_left hneg hc
    rw [mul_zero] at hprod
    rw [log_one] at hh
    exact (ne_of_lt (lt_of_lt_of_le hprod hh)) rfl

/-! ## §5 — the §3 fixtures, measured in the valuation -/

theorem log_towerTree_succ (n : Nat) (x : Real) :
    log ((EMLTree.towerTree (n + 1)).eval x) = EMLTree.towerFn n x := by
  rw [EMLTree.towerTree_eval]
  show log (exp (EMLTree.towerFn n x)) = _
  rw [log_exp]

theorem log_capNode (n : Nat) {x : Real} (hx : 1 ≤ x) : log ((capNode n).eval x) = 0 :=
  log_nonpos (capNode_nonpos n hx)

/-- **`capNode` — the class does not descend to the right child either.** The node is *strictly
below* its own right child at every `n`: totalised `log` sends the non-positive node germ to `0`
while the child's log is `towerFn n x`. This is `tower_height_does_not_descend_right` in the
valuation, unchanged — the fixture that killed the germ-growth measure kills the comparability
class for the same reason and at the same place. -/
theorem compLt_capNode_right (n : Nat) :
    CompLt (capNode n).eval (EMLTree.towerTree (n + 1)).eval := by
  constructor
  · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x hx
    rw [log_capNode n hx, log_towerTree_succ, one_mul_thm]
    exact le_trans (le_of_lt zero_lt_one_ax) (towerFn_ge_one n hx)
  · rintro ⟨c, X, hc, hX, hf⟩
    obtain ⟨x, hxX, hx1⟩ : ∃ x : Real, X ≤ x ∧ (1 : Real) ≤ x :=
      ⟨max X 1, le_max_left _ _, le_max_right _ _⟩
    have hh := hf x hxX
    rw [log_towerTree_succ, log_capNode n hx1, mul_zero] at hh
    exact (ne_of_lt (lt_of_lt_of_le
      (lt_of_lt_of_le zero_lt_one_ax (towerFn_ge_one n hx1)) hh)) rfl

/-- **`gapTarget n 1` — the gap is the constant `1`**, at every tower height `n`
(`gapTarget_gap`), so its class is the constant class while the operands live at height `n + 1`.
Approach is not controlled by the class any more than it was by the growth rate. -/
theorem gapTarget_gap_germ (n : Nat) :
    (fun x => exp ((EMLTree.towerTree n).eval x) - (gapTarget n 1).eval x)
      = (fun _ : Real => (1 : Real)) :=
  funext (fun x => gapTarget_gap n 1 x)

/-- **`eTree (eTree A)` — the meeting boundary is invisible to the class.** The exact-meeting gap
is identically `0` (`exact_meeting_gap_zero`) and has no floor at all; the `gapTarget` gap is the
constant `1` and meets the height-`0` floor. Totalised `log` sends both to `0`, so comparability
puts them in the **same class**.

A class therefore cannot determine a floor: one member of this class has one and the other does
not. This is the valuation's version of `measure_blind_at_meeting`, and it is worse — there two
*syntactic* measures agreed on germs that differ; here the germs' own invariant agrees. -/
theorem compEquiv_zero_one :
    CompEquiv (fun _ : Real => (0 : Real)) (fun _ : Real => (1 : Real)) := by
  constructor
  · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _
    show log (0 : Real) ≤ 1 * log (1 : Real)
    rw [log_nonpos (le_refl (0 : Real)), log_one, one_mul_thm]
    exact le_refl _
  · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _
    show log (1 : Real) ≤ 1 * log (0 : Real)
    rw [log_nonpos (le_refl (0 : Real)), log_one, one_mul_thm]
    exact le_refl _

/-- The exact-meeting gap, as a germ, is the one `compEquiv_zero_one` puts beside the constant. -/
theorem meeting_gap_germ (A : EMLTree) :
    (fun x => exp (A.eval x) - (eTree A).eval x) = (fun _ : Real => (0 : Real)) :=
  funext (fun x => exact_meeting_gap_zero A x)

/-! ## §6 — a floor IS a comparability bound, which is why this is a reindexing -/

/-- **One line, and it is the whole of candidate 3's positive content.** A tower floor for `t` is
a comparability lower bound for `t` by the class of `exp ∘ (−towerFn k)`, with `c = 1` and the same
`X₁`. So *"`DecayFloor` at depth `j`"* and *"every eventually-positive depth-`j` germ has a class
bounded below by a tower-reciprocal, uniformly in `j`"* are the same statement.

Per `EmlGermApproachResearch.md` §9 an equivalence with a converse is not progress, and this one
has a converse: the multiplier `c` is absorbed by one extra tower rung, which is exactly what
`lin_lt_exp` provides. The reindexing is two-way, in the same sense `reindexing_is_two_way` is for
the polarity pair. -/
theorem compLe_floor_of_floor (t : EMLTree) (k : Nat) (X₁ : Real) (hX₁ : 1 ≤ X₁)
    (h : ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ t.eval x) :
    CompLe (fun x => exp (-(EMLTree.towerFn k x))) t.eval := by
  refine ⟨1, X₁, zero_lt_one_ax, hX₁, ?_⟩
  intro x hx
  rw [one_mul_thm]
  have hp : (0 : Real) < exp (-(EMLTree.towerFn k x)) := exp_pos _
  have hstep := log_le_log hp (h x hx)
  rw [log_exp] at hstep
  rw [log_exp]
  exact hstep

end MachLib
