import MachLib.EMLReciprocalDepth2

/-!
# Route A's termination obligations, in Lean — and the two that say the route is worse

`TERMINATION_SCOPE.md` listed four obligations for a termination argument against `1/x ∈ EML`.
**This file discharges A4 and A2's replacement, and produces WITNESSES against two claims the
record currently makes.**

Pre-registration: `monogate-research/exploration/inv_x_termination_route_2026_08_06/`.

## What the record said entering this file

| # | obligation | status claimed |
|---|---|---|
| A1 | case split at each node | closed by `node_pins_a_child` |
| A2 | *"the non-constant-left branch has no pinning"* | **VOIDED** — `pins_right` is unconditional |
| A3 | a measure strictly increasing down the tree | unidentified |
| A4 | leaves reach only `{const c} ∪ {x}` | *"easy"*, unwritten |

**A1 and the A2 void are both correct.** What this file adds is that **neither buys the regress**,
for two separate and independently witnessed reasons.

## The two witnesses

**`pinned_target_not_determined_by_left`** — `pins_right` determines the child but names
`u.eval x` in the pinned value. Two legitimate left children give **different** required
right-child values at the same point. **So the pinned target is a named function only when `u` is
constant-valued** — the regress `1/x → m·x → C·exp(−m·x)` is conditional exactly as
`TERMINATION_SCOPE.md` originally said. **A2 was voided about pinning, and the regress is a
different object.**

**`branch_not_uniform`** — `node_pins_a_child` is a disjunction *at each `x`*, and the disjunct
genuinely differs between points: `eml (const 0) var` is positive at `x = 1` and non-positive at
`x = e`. **So a spine-following induction over `∀ x > 0` cannot fix one child to descend into.**

## What survives, and it is real

**Termination itself needs no measure** (`descent_step`): both branches descend into a *strict
subtree*, so `depth` decreases structurally. **A3's measure is needed for the leaf obstruction, not
for termination** — which is a smaller and better-located obligation than the scoping doc assumed.

**A4 is genuinely easy** (`leaf_excluded`) — but only over **two or more points**.
`leaf_hits_any_value_pointwise` shows why: pointwise, `const g` hits any value at all, so the leaf
obstruction has **zero content at a single point.** That is the formal reason every argument in this
arm is a two-point argument.
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## A4 — leaves reach only constants and `x` -/

/-- Depth `0` forces a leaf. The `eml` case dies on `1 + max _ _ = 0`. -/
theorem depth_zero_cases {t : EMLTree} (ht : t.depth = 0) :
    (∃ c : Real, t = EMLTree.const c) ∨ t = EMLTree.var := by
  cases t with
  | const c => exact Or.inl ⟨c, rfl⟩
  | var => exact Or.inr rfl
  | eml t1 t2 =>
    exfalso
    have h : (EMLTree.eml t1 t2).depth = 1 + Nat.max t1.depth t2.depth := rfl
    rw [h] at ht
    omega

/-- **A4.** A leaf is a constant function or the identity — there is no third behaviour. -/
theorem leaf_reaches_only_const_or_id {t : EMLTree} (ht : t.depth = 0) :
    (∃ c : Real, ∀ x : Real, t.eval x = c) ∨ (∀ x : Real, t.eval x = x) := by
  rcases depth_zero_cases ht with ⟨c, hc⟩ | hv
  · exact Or.inl ⟨c, fun x => by rw [hc]; rfl⟩
  · exact Or.inr (fun x => by rw [hv]; rfl)

/-- **A4 in usable form.** A leaf cannot hit a target that is both non-constant (witnessed at two
points) and not the identity (witnessed at one).

**Both witnesses are necessary and neither is redundant:** dropping `hncon` admits `t = const c`,
dropping `hnid` admits `t = var`. -/
theorem leaf_excluded {t : EMLTree} (ht : t.depth = 0) {g : Real → Real}
    (h : ∀ x : Real, t.eval x = g x)
    {a b p : Real} (hncon : g a ≠ g b) (hnid : g p ≠ p) :
    False := by
  rcases leaf_reaches_only_const_or_id ht with ⟨c, hc⟩ | hid
  · -- constant: g a = c = g b
    apply hncon
    rw [← h a, ← h b, hc a, hc b]
  · -- identity: g p = p
    apply hnid
    rw [← h p, hid p]

/-- **Ablation: `hncon` is load-bearing.** Dropping it leaves a satisfiable configuration —
`const 0` against `g ≡ 0` and `p = 1`. So `leaf_excluded` cannot be proved without it. -/
theorem leaf_excluded_hncon_load_bearing :
    ∃ (t : EMLTree) (g : Real → Real) (p : Real),
      t.depth = 0 ∧ (∀ x : Real, t.eval x = g x) ∧ g p ≠ p :=
  ⟨EMLTree.const 0, fun _ => 0, 1, rfl, fun _ => rfl, zero_ne_one_ax⟩

/-- **Ablation: `hnid` is load-bearing.** Dropping it leaves a satisfiable configuration —
`var` against `g = id` and `a = 0`, `b = 1`. -/
theorem leaf_excluded_hnid_load_bearing :
    ∃ (t : EMLTree) (g : Real → Real) (a b : Real),
      t.depth = 0 ∧ (∀ x : Real, t.eval x = g x) ∧ g a ≠ g b :=
  ⟨EMLTree.var, fun x => x, 0, 1, rfl, fun _ => rfl, zero_ne_one_ax⟩

/-- **Why A4 needs at least two points.** Pointwise, a leaf hits ANY value — `const g` does it.

**So the leaf obstruction has no content at a single point**, and a descent tracked at one `x`
proves nothing however far it runs. This is the formal reason every argument in this arm is a
two-point argument. -/
theorem leaf_hits_any_value_pointwise (g x : Real) :
    ∃ s : EMLTree, s.depth = 0 ∧ s.eval x = g :=
  ⟨EMLTree.const g, rfl, rfl⟩

/-! ## T2 — termination is STRUCTURAL, and needs no measure -/

/-- The left child is strictly shallower than its node. -/
theorem depth_left_lt (t1 t2 : EMLTree) : t1.depth < (EMLTree.eml t1 t2).depth := by
  have h : (EMLTree.eml t1 t2).depth = 1 + Nat.max t1.depth t2.depth := rfl
  have hm : t1.depth ≤ Nat.max t1.depth t2.depth := Nat.le_max_left _ _
  rw [h]; omega

/-- The right child is strictly shallower than its node. -/
theorem depth_right_lt (t1 t2 : EMLTree) : t2.depth < (EMLTree.eml t1 t2).depth := by
  have h : (EMLTree.eml t1 t2).depth = 1 + Nat.max t1.depth t2.depth := rfl
  have hm : t2.depth ≤ Nat.max t1.depth t2.depth := Nat.le_max_right _ _
  rw [h]; omega

/-- **The descent step, with its termination.** Every node pins a child, and **whichever branch
holds, the pinned child is a STRICT SUBTREE** — so `depth` decreases and the descent terminates.

> **No complexity measure is involved.** `TERMINATION_SCOPE.md`'s obligation A3 is needed for the
> **leaf obstruction**, not for **termination**. That relocates A3 to a smaller place than the
> scoping assumed. -/
theorem descent_step (u w : EMLTree) {f x : Real} (e : (EMLTree.eml u w).eval x = f) :
    ∃ s : EMLTree, s.depth < (EMLTree.eml u w).depth ∧
      (s.eval x = exp (exp (u.eval x) - f) ∨ s.eval x = log f) := by
  rcases node_pins_a_child u w e with hr | hl
  · exact ⟨w, depth_right_lt u w, Or.inl hr⟩
  · exact ⟨u, depth_left_lt u w, Or.inr hl⟩

/-! ## T0 — the pinned target is NOT named when the left child varies

`pins_right` is unconditional: it determines `w.eval x` for ANY `u`. **But the value it determines
mentions `u.eval x`.** The regress needs a target it can NAME, and the following says it cannot. -/

/-- **The pinned target depends on the left child.** Two legitimate left children — `const 0` and
`const 1` — force **different** right-child values at the same point, for every target `f`.

> **So `pins_right`'s conclusion is a determination, not a named target.** The regress
> `1/x → m·x → C·exp(−m·x)` requires `u` constant-valued to name the next target, exactly as
> `TERMINATION_SCOPE.md` said before A2 was voided. **The void was correct about PINNING and does
> not transfer to the REGRESS.** -/
theorem pinned_target_not_determined_by_left (f x : Real) :
    ∃ u₁ u₂ : EMLTree,
      exp (exp (u₁.eval x) - f) ≠ exp (exp (u₂.eval x) - f) := by
  refine ⟨EMLTree.const 0, EMLTree.const 1, ?_⟩
  show exp (exp (0 : Real) - f) ≠ exp (exp (1 : Real) - f)
  intro hEq
  have h1 : exp (0 : Real) - f = exp (1 : Real) - f := exp_injective hEq
  have h2 : exp (0 : Real) = exp 1 := by
    have e : exp (0 : Real) = (exp (0 : Real) - f) + f := by mach_ring
    rw [e, h1]; mach_ring
  exact zero_ne_one_ax (exp_injective h2)

/-! ## T3 — the pointwise branch does NOT lift to a functional induction -/

/-- **The branch is not uniform in `x`.** `eml (const 0) var` evaluates to `1 − log x`, which is
positive at `x = 1` and **zero** at `x = e`.

> So a tree carrying this as its right child takes `node_pins_a_child`'s POSITIVE branch at `x = 1`
> and its CLAMPED branch at `x = e`. **The disjunction is pointwise and the disjunct genuinely
> moves.**

**Consequence for Route A:** a spine-following induction over `∀ x > 0` cannot fix one child to
descend into — the pinned child at one point need not be the pinned child at another. The
functional descent the route needs does not follow from `node_pins_a_child`. -/
theorem branch_not_uniform :
    0 < (EMLTree.eml (EMLTree.const 0) EMLTree.var).eval 1 ∧
      (EMLTree.eml (EMLTree.const 0) EMLTree.var).eval (exp 1) ≤ 0 := by
  constructor
  · show 0 < exp (0 : Real) - log (1 : Real)
    rw [exp_zero, log_one]
    have e : (1 : Real) - 0 = 1 := by mach_ring
    rw [e]; exact zero_lt_one_ax
  · show exp (0 : Real) - log (exp 1) ≤ 0
    rw [exp_zero, log_exp]
    have e : (1 : Real) - 1 = 0 := by mach_ring
    rw [e]; exact le_refl 0

/-! ## The inequality regress — the one new idea, and it dies at step two

`positive_branch_lower_bound` eliminates `u` one-sidedly: `exp(−f) < w.eval x`, parameter-free.
**The pre-registered question was whether a regress can run on INEQUALITIES where it cannot run on
equations.** It cannot, and the reason is a direction, not a difficulty. -/

/-- `exp ∘ neg` is strictly antitone. **This is the whole obstruction**, isolated. -/
theorem exp_neg_antitone {a b : Real} (h : a < b) : exp (-b) < exp (-a) := by
  have h1 : (-a - b) + a < (-a - b) + b := add_lt_add_left h (-a - b)
  have e1 : (-a - b) + a = -b := by mach_ring
  have e2 : (-a - b) + b = -a := by mach_mpoly [a, b]
  rw [e1, e2] at h1
  exact exp_lt h1

/-- **The inequality regress is vacuous at step two.** Both facts are true; **they point the same
way past the middle quantity and therefore compose to nothing.**

Step one bounds the child from BELOW: `exp(−f) < w.eval x`. Step two, applied to `w = eml u' w'`,
bounds `w'` from below by `exp(−(w.eval x))` — and to turn that into a bound in `f` alone we need a
LOWER bound on `exp(−(w.eval x))`, i.e. an UPPER bound on `w.eval x`. **Step one supplies a lower
bound, and `exp_neg_antitone` converts it to an UPPER bound on `exp(−(w.eval x))` — the wrong
direction.**

```
w'.eval x  >  exp(−(w.eval x))  <  exp(−exp(−f))
```

> **Two `<` facing each other across the middle term. No transitive conclusion exists.**

**So the one-sided elimination of `u` is genuinely one-shot: it works at the step where it is
applied and supplies nothing to the next.** Recorded as a scored negative — the idea was named in
the pre-registration before it was tested. -/
theorem inequality_regress_vacuous {u u' w' : EMLTree} {f x : Real}
    (hw : 0 < (EMLTree.eml u' w').eval x) (hw' : 0 < w'.eval x)
    (e : (EMLTree.eml u (EMLTree.eml u' w')).eval x = f) :
    exp (-f) < (EMLTree.eml u' w').eval x ∧
      exp (-((EMLTree.eml u' w').eval x)) < w'.eval x ∧
      exp (-((EMLTree.eml u' w').eval x)) < exp (-(exp (-f))) := by
  have step1 : exp (-f) < (EMLTree.eml u' w').eval x :=
    positive_branch_lower_bound hw e
  have step2 : exp (-((EMLTree.eml u' w').eval x)) < w'.eval x :=
    positive_branch_lower_bound hw' (rfl : (EMLTree.eml u' w').eval x = _)
  exact ⟨step1, step2, exp_neg_antitone step1⟩

end Real
end MachLib
