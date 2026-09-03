import MachLib.EMLDecayLadderStep
import MachLib.EMLDepthTameness
import MachLib.OperatorBasisComplete

/-!
# `log` of a depth-≤2 tree has an exponential floor — unconditionally

`EMLDecayLadderStep`'s route map names two missing lemmas as what the depth-4 decay rung waits on,
both about `log` of a depth-≤2 function. **This is the first of the two.** The companion,
`depth_le_two_log_le_linear`, is still missing and the rung is not closed by this file alone.

## What it says, and why "unconditional" is the whole difficulty

```
∃ Cl X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀,  −(Cl + exp x) ≤ log (B.eval x)
```

for every `B` of depth ≤ 2 — with **no positivity hypothesis on `B`**. That is what makes it the
depth-2 analogue of `depth_le_one_log_lower_at_infinity` and what stops `decayFloorUpTo_two` from
supplying it: the floor's hypothesis is *eventual positivity* (`∀ x ≥ X₀, 0 < t.eval x`), so it says
nothing about a `B` that oscillates in sign. The totalisation carries those stretches instead —
`log b = 0` for `b ≤ 0`, which is *above* the floor, so the non-positive case is free.

## The three branches

Casing on the constructor rather than through `depth_le_two_normal_form` is what makes it work: the
normal form hands back `Depth1Form` **functions** and discards the trees, and both tools this proof
needs (`nodeDecayBound_two`, `depth_le_one_lower_on_ray`) are stated on trees.

For `B = eml A C`, with `v = exp (A.eval x) − log (C.eval x)`:

* `v ≤ 0` — `log v = 0` by totalisation, and `−(Cl + exp x) ≤ 0`. Free.
* `v > 0`, `log (C.eval x) ≤ 0` — then `v ≥ exp (A.eval x)`, so `log v ≥ A.eval x`, and
  `depth_le_one_lower_on_ray` floors that at `−C₁ − log x ≥ −(Cl + exp x)`.
* `v > 0`, `log (C.eval x) > 0` — exactly `NodeDecayBound`'s hypotheses, and
  `nodeDecayBound_two` applies because the predicate is **monotone in depth**: a depth-≤1 child is a
  depth-≤2 child, so `NodeDecayBound 2 1` gives the depth-1 instance for free.

The floor is `exp`, not linear: `NodeDecayBound _ 1` has height `towerFn 1 = exp`, so the `log`-side
degradation from depth 1 to depth 2 is a full tower level rather than one algebraic step.
-/

namespace MachLib

open Real

private theorem log_nonneg_of_one_le {x : Real} (hx : 1 ≤ x) : (0 : Real) ≤ log x := by
  have h := log_mono (a := 1) (b := x) zero_lt_one_ax hx
  rw [log_one] at h; exact h

theorem depth_le_two_log_lower_at_infinity (B : EMLTree) (hB : B.depth ≤ 2) :
    ∃ Cl X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → -(Cl + exp x) ≤ log (B.eval x) := by
  cases B with
  | const c =>
      refine ⟨-log c, 1, le_refl 1, fun x _ => ?_⟩
      show -(-log c + exp x) ≤ log c
      have u := add_le_add_wit (le_refl (log c)) (neg_le_neg_wit (le_of_lt (exp_pos x)))
      have e1 : -(-log c + exp x) = log c + -exp x := by mach_ring
      have e2 : log c + -(0 : Real) = log c := by mach_ring
      rw [e1]; rw [e2] at u; exact u
  | var =>
      refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
      show -((0 : Real) + exp x) ≤ log x
      have h0 : (0 : Real) ≤ log x := log_nonneg_of_one_le hx
      have hneg : -((0 : Real) + exp x) ≤ 0 := by
        have := le_of_lt (exp_pos x)
        have e : -((0 : Real) + exp x) = -exp x := by mach_ring
        rw [e]
        have u := neg_le_neg_wit this
        have e2 : -(0 : Real) = 0 := by mach_ring
        rw [e2] at u; exact u
      exact le_trans hneg h0
  | eml A C =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_left A.depth C.depth; omega
      have hC : C.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_right A.depth C.depth; omega
      obtain ⟨C₁, hC₁⟩ := depth_le_one_lower_on_ray A hA
      obtain ⟨Cn, Xn, hXn, hnd⟩ :=
        nodeDecayBound_two A C (by omega) (by omega)
      refine ⟨max (max C₁ Cn) 0, max 1 Xn, le_max_left 1 Xn, fun x hx => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans (le_max_left 1 Xn) hx
      have hxn : Xn ≤ x := le_trans (le_max_right 1 Xn) hx
      have hCl0 : (0 : Real) ≤ max (max C₁ Cn) 0 := le_max_right _ _
      have hClC1 : C₁ ≤ max (max C₁ Cn) 0 := le_trans (le_max_left C₁ Cn) (le_max_left _ _)
      have hClCn : Cn ≤ max (max C₁ Cn) 0 := le_trans (le_max_right C₁ Cn) (le_max_left _ _)
      show -(max (max C₁ Cn) 0 + exp x) ≤ log (exp (A.eval x) - log (C.eval x))
      rcases lt_total 0 (exp (A.eval x) - log (C.eval x)) with hv | hv | hv
      · rcases lt_total 0 (log (C.eval x)) with hlc | hlc | hlc
        · -- the NodeDecayBound branch
          have hb := hnd x hxn hlc hv
          have htw : EMLTree.towerFn 1 x = exp x := rfl
          rw [htw] at hb
          have u := add_le_add_wit hClCn (le_refl (exp x))
          have hstep : Cn + exp x ≤ max (max C₁ Cn) 0 + exp x := u
          have hfin := le_trans hb hstep
          have w := neg_le_neg_wit hfin
          have e : - -log (exp (A.eval x) - log (C.eval x))
              = log (exp (A.eval x) - log (C.eval x)) := by mach_ring
          rw [e] at w; exact w
        · -- log C = 0: node ≥ exp A
          have hge : exp (A.eval x) ≤ exp (A.eval x) - log (C.eval x) := by
            rw [← hlc]; have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
            rw [e]; exact le_refl _
          exact le_trans (by
            have hAlow := hC₁ x hx1
            have hlx : log x ≤ exp x := le_trans (log_le_self_ge_one hx1)
              (le_of_lt (exp_grows_strictly_thm x))
            have u := add_le_add_wit hClC1 hlx
            have w := neg_le_neg_wit u
            have e1 : -(C₁ + log x) = -C₁ - log x := by mach_ring
            rw [e1] at w
            exact le_trans w hAlow) (by
            have hlm := log_mono (exp_pos (A.eval x)) hge
            rw [log_exp] at hlm; exact hlm)
        · -- log C < 0: node ≥ exp A likewise
          have hge : exp (A.eval x) ≤ exp (A.eval x) - log (C.eval x) := by
            have u := add_le_add_wit (le_refl (exp (A.eval x))) (neg_le_neg_wit (le_of_lt hlc))
            have e1 : exp (A.eval x) + -log (C.eval x)
                = exp (A.eval x) - log (C.eval x) := by mach_ring
            have e2 : exp (A.eval x) + -(0 : Real) = exp (A.eval x) := by mach_ring
            rw [e1, e2] at u; exact u
          exact le_trans (by
            have hAlow := hC₁ x hx1
            have hlx : log x ≤ exp x := le_trans (log_le_self_ge_one hx1)
              (le_of_lt (exp_grows_strictly_thm x))
            have u := add_le_add_wit hClC1 hlx
            have w := neg_le_neg_wit u
            have e1 : -(C₁ + log x) = -C₁ - log x := by mach_ring
            rw [e1] at w
            exact le_trans w hAlow) (by
            have hlm := log_mono (exp_pos (A.eval x)) hge
            rw [log_exp] at hlm; exact hlm)
      · -- node = 0: totalised log gives 0
        rw [← hv, log_nonpos (le_refl 0)]
        have u := add_le_add_wit hCl0 (le_of_lt (exp_pos x))
        have e : (0 : Real) + 0 = 0 := by mach_ring
        rw [e] at u
        have w := neg_le_neg_wit u
        have e2 : -(0 : Real) = 0 := by mach_ring
        rw [e2] at w; exact w
      · -- node < 0: totalised log gives 0
        rw [log_nonpos (le_of_lt hv)]
        have u := add_le_add_wit hCl0 (le_of_lt (exp_pos x))
        have e : (0 : Real) + 0 = 0 := by mach_ring
        rw [e] at u
        have w := neg_le_neg_wit u
        have e2 : -(0 : Real) = 0 := by mach_ring
        rw [e2] at w; exact w

end MachLib
