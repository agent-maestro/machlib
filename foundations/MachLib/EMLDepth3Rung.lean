import MachLib.EMLHeightInterface

/-!
# The depth-3 rung: everything but one finite case analysis

`decayFloor_upTo_two` has been the top of the ladder for the whole arc. `(de)` refuted `V₃`, the
route that was supposed to lift it, and `(dj)` showed the reciprocal repair consumes `U 5` to produce
`D 3`, which nobody has. So depth 3 has stood untouched.

**Depth 3 is the one place `(di)`'s re-embedding argument does not reach.** `posEmbed` shows the
positive-`B` branch at depth `j+4` contains all of `DecayFloor` at depth `j` — which says nothing at
`j = 3`, because `3 − 4 < 0`. So unlike every higher rung, the depth-3 positive branch is **not known
to be as hard as the general obligation**, and it is worth attacking directly.

This file reduces the whole rung to that one branch, and discharges the other.

```
Depth3NodeFloor        the node case at depth 3, A and B both depth ≤ 2      ← the residue
decayFloorUpTo_three   Depth3NodeFloor ⟹ DecayFloorUpTo 3                    ← proved
depth3_clamped_floor   the clamped half of the residue                       ← proved
```

## Why the reduction costs no axioms

The obvious way to split the node case is on the eventual sign of `B` — which needs `evSign_all`, and
with it the whole analytic block (`rolle_ct`, `analytic_finite_zeros_compact`,
`eml_tree_analytic_on_interval`). **The residue is stated so that no split is needed**: it takes the
node as given and asks only for the floor, so `decayFloorUpTo_three` dispatches on tree *shape*, not
on germ sign. The clamped half is then a separate theorem about the residue rather than a step in the
reduction. Footprint stays clean, and the sign split is paid for only by whoever finishes the branch.

## What the clamped half costs, and what it says about the height

`depth3_clamped_floor` runs on `depth_le_two_lower_on_ray` — a depth-≤2 germ is `≥ −C − x` — so a
clamped node is `exp ∘ A ≥ exp (−C − x)`, and `C + x < exp x` puts that above `exp (−towerFn 1 x)`.

**Height `1`, not height `0`.** That is a property of *this route*, not of depth 3: the linear floor
`−C − x` carries an additive constant, and `exp (−C − x) < exp (−x)` for `C > 0`. The sharper
statement — that a depth-3 clamped node never dips below `exp (−x)` — appears to be true and needs
the depth-≤1 classification rather than the linear envelope: the largest depth-≤1 germ is `exp x + K`,
whose log is `x + log (1 + K e^{−x})`, exceeding `x` by an *exponentially* small amount, while
`exp (P x)` for depth-≤1 `P` decays at worst *polynomially* and so dominates it. **That gap between
`e^{−x}` and `1/x` is the whole margin**, and it is why the conjecture `max (0, d − 3)` survives here
while the cheap route lands one rung above it. Not proved; recorded so the next session does not
mistake `1` for the true value.
-/

namespace MachLib

open Real

/-! ## §1 — lifting a floor to a taller tower -/

/-- A height-`k` floor is a height-`m` floor for any `m ≥ k`: `towerFn` is monotone in height, so the
taller tower gives the *weaker* bound. -/
theorem floor_lift {k d : Nat} (t : EMLTree) {X₁ : Real} (hX₁ : 1 ≤ X₁)
    (h : ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ t.eval x) :
    ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn (k + d) x)) ≤ t.eval x := by
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans hX₁ hx
  have hmono := towerFn_mono k d hx1
  exact le_trans (exp_monotone (neg_le_neg_wit hmono)) (h x hx)

/-! ## §2 — the residue, and the rung that rests on it -/

/-- **The depth-3 node case.** Both children at depth ≤ 2, the node eventually positive, and a
height-`1` floor wanted. No sign hypothesis on `B`: the split belongs to whoever discharges this,
not to the reduction. -/
def Depth3NodeFloor : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), A.depth ≤ 2 → B.depth ≤ 2 → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → 0 < (EMLTree.eml A B).eval x) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn 1 x)) ≤ (EMLTree.eml A B).eval x

/-- **The rung, modulo the residue.** Everything at depth ≤ 2 is `decayFloor_upTo_two`, lifted to
height `1` where the statement needs it; the leaves at depth 3 are depth 0; the node is the residue.
Dispatch is on tree shape alone — no germ-sign analysis, hence no analytic axioms. -/
theorem decayFloorUpTo_three (h : Depth3NodeFloor) : DecayFloorUpTo 3 := by
  intro j hj
  match j, hj with
  | 0, _ =>
      exact ⟨0, fun t X₀ hd hX₀ hpos => decayFloor_upTo_two t X₀ (by omega) hX₀ hpos⟩
  | 1, _ =>
      exact ⟨0, fun t X₀ hd hX₀ hpos => decayFloor_upTo_two t X₀ (by omega) hX₀ hpos⟩
  | 2, _ =>
      exact ⟨0, fun t X₀ hd hX₀ hpos => decayFloor_upTo_two t X₀ (by omega) hX₀ hpos⟩
  | 3, _ =>
      refine ⟨1, ?_⟩
      intro t X₀ hd hX₀ hpos
      cases t with
      | const c =>
          obtain ⟨X₁, hX₁, hf⟩ :=
            decayFloor_upTo_two (EMLTree.const c) X₀ (by simp only [EMLTree.depth]; omega) hX₀ hpos
          exact ⟨X₁, hX₁, floor_lift (d := 1) _ (le_trans hX₀ hX₁) hf⟩
      | var =>
          obtain ⟨X₁, hX₁, hf⟩ :=
            decayFloor_upTo_two EMLTree.var X₀ (by simp only [EMLTree.depth]; omega) hX₀ hpos
          exact ⟨X₁, hX₁, floor_lift (d := 1) _ (le_trans hX₀ hX₁) hf⟩
      | eml A B =>
          have hA : A.depth ≤ 2 := by
            simp only [EMLTree.depth] at hd
            have := Nat.le_max_left A.depth B.depth; omega
          have hB : B.depth ≤ 2 := by
            simp only [EMLTree.depth] at hd
            have := Nat.le_max_right A.depth B.depth; omega
          exact h A B X₀ hA hB hX₀ hpos

/-! ## §3 — the clamped half of the residue, discharged -/

/-- **A clamped depth-3 node meets the height-`1` floor.** Totalised `log` makes the node `exp ∘ A`;
`depth_le_two_lower_on_ray` floors `A` at `−C − x`; and `C + x < exp x` clears the tower.

The ray is pushed to `X₀ + exp C`, which is past both `X₀` and `C` — `exp C > C` does the work, and
avoids needing a `max` on `Real`, which this corpus does not have. -/
theorem depth3_clamped_floor (A B : EMLTree) (X₀ : Real) (hA : A.depth ≤ 2) (hX₀ : 1 ≤ X₀)
    (hclamp : ∀ x : Real, X₀ ≤ x → B.eval x ≤ 0) :
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn 1 x)) ≤ (EMLTree.eml A B).eval x := by
  obtain ⟨C, hC⟩ := depth_le_two_lower_on_ray A hA
  have hgrow : X₀ ≤ X₀ + exp C := le_add_nonneg' (le_of_lt (exp_pos C))
  refine ⟨X₀ + exp C, hgrow, ?_⟩
  intro x hx
  have hXx : X₀ ≤ x := le_trans hgrow hx
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ hXx
  -- `C < x`, because `x ≥ X₀ + exp C ≥ 1 + exp C > exp C > C`
  have hCx : C < x := by
    have h1 : C < exp C := exp_grows_strictly_thm C
    have h2 : exp C ≤ X₀ + exp C := by
      have hX0nn : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX₀
      have u := add_le_add_wit hX0nn (le_refl (exp C))
      have e : (0 : Real) + exp C = exp C := by mach_ring
      rw [e] at u; exact u
    exact lt_of_lt_of_le h1 (le_trans h2 hx)
  -- `C + x < exp x`, from `2x < exp x`
  have hsum : C + x < exp x := by
    have h2 : (1 + 1) * x < exp x := exp_gt_two_x x
    have e : (1 + 1) * x = x + x := by mach_ring
    rw [e] at h2
    have u := add_lt_add_left hCx x
    have e1 : x + C = C + x := by mach_ring
    rw [e1] at u
    exact lt_of_lt_of_le u (le_of_lt h2)
  -- so `-(exp x) ≤ -C - x ≤ A.eval x`
  have hlow : -(exp x) ≤ A.eval x := by
    have hstep : -(exp x) ≤ -C - x := by
      have u := neg_le_neg_wit (le_of_lt hsum)
      have e : -(C + x) = -C - x := by mach_ring
      rw [e] at u; exact u
    exact le_trans hstep (hC x hx1)
  show exp (-(EMLTree.towerFn 1 x)) ≤ exp (A.eval x) - log (B.eval x)
  rw [log_nonpos (hclamp x hXx)]
  have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
  rw [e]
  have hT : EMLTree.towerFn 1 x = exp (EMLTree.towerFn 0 x) := rfl
  have hT0 : EMLTree.towerFn 0 x = x := rfl
  rw [hT, hT0]
  exact exp_monotone hlow

end MachLib
