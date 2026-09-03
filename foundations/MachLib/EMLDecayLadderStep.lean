import MachLib.EMLDepth3Rung

/-!
# The rung, as a step — so the next one costs only its own input

`(dt)` proved `DecayFloorUpTo 3` from two ingredients that happened to be lying around. This turns
that proof into a **general step**, so depth 4 costs exactly one new theorem instead of a fresh
argument, and so the shape of every future rung is visible in advance.

```
decayFloorUpTo_succ :  DecayFloorUpTo j → NodeDecayBound j m → LowerEnvBound j m
                         → DecayFloorUpTo (j + 1)          -- at height m + 1
```

Instantiated at `j = 2, m = 1` it re-derives `(dt)` exactly — `NodeDecayBound 2 1` **is**
`Depth3DecayExp`, `LowerEnvBound 2 1` follows from `depth_le_two_lower_on_ray`, and the height comes
out `2`. That the step reproduces the hand proof, height and all, is the evidence that it is the
right generalisation rather than a repackaging.

## What depth 4 now costs

Two inputs at `j = 3`. One of them is **not** a research problem:

* `LowerEnvBound 3 m` — a lower envelope for depth-≤3 germs. The ingredients exist:
  `node_lower_of_right_upper` derives a lower bound at depth `j+1` from an **upper** bound at depth
  `j`, and `depth_le_two_growth_envelope` is that upper bound (giving `m = 3`, since
  `exp (exp x + K) + M` needs `towerFn 3` to dominate it). **One friction, flagged rather than
  waved at:** `LowerEnvBound` as defined here quantifies over all `x ≥ 1` with no per-tree ray, and
  the depth-2 growth envelope holds only past a tree-dependent `X₀`. Either the constant absorbs the
  ray or the definition grows one, and which is cheaper has not been checked. Not discovery, but not
  nothing either.
* `NodeDecayBound 3 m` — **the residue.** The depth-4 analogue of `Depth3DecayExp`: how small can
  `exp (A x) − log (B x)` be, positive, with `A` and `B` at depth ≤ 3.

So depth 4 reduces to one named proposition, and it is the same proposition `Depth3DecayExp` was one
rung down.

## Correcting what `(dt)`'s summary said about `(di)`

`(di)` is often quoted as "the positive branch contains the whole problem", and `(dt)`'s summary read
that as blocking depth 4. **It does not.** `posEmbed t` has depth `t.depth + 4`, so the precise
statement is that the positive branch at depth `k` is at least as hard as `DecayFloor` at depth
`k − 4`. With depth ≤ 3 discharged, the branch at depths **4, 5, 6 and 7** re-embeds only problems
that are already solved. **The re-embedding first bites at depth 8.**

That is a moving boundary, not a fixed one — every rung proved pushes it up by one — and it is worth
stating because the pessimistic reading costs nothing to believe and would have retired four rungs
without an argument.
-/

namespace MachLib

open Real

/-! ## §1 — the two inputs a rung needs -/

/-- **The decay bound**: children at depth ≤ `j`, node value floored via a tower-height-`m` bound on
`−log`. `NodeDecayBound 2 1` is `Depth3DecayExp` verbatim.

The hypotheses `0 < log (B x)` and `0 < node` are **pointwise**, inside the `∀ x`, exactly as in
`Depth3DecayExp` — which is what lets the rung split without `evSign_all`. Stating it any other way
would drag in the analytic block; see `(dt)`. -/
def NodeDecayBound (j m : Nat) : Prop :=
  ∀ A B : EMLTree, A.depth ≤ j → B.depth ≤ j →
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (B.eval x) →
      0 < exp (A.eval x) - log (B.eval x) →
        -log (exp (A.eval x) - log (B.eval x)) ≤ C + EMLTree.towerFn m x

/-- **The lower envelope**, for the clamped and negative-log branches, where the node is at least
`exp ∘ A` and the floor is a lower bound on `A`. -/
def LowerEnvBound (j m : Nat) : Prop :=
  ∀ A : EMLTree, A.depth ≤ j → ∃ C XL : Real, 1 ≤ XL ∧ ∀ x : Real, XL ≤ x →
    -(C + EMLTree.towerFn m x) ≤ A.eval x

/-! ## §2 — two facts about the tower -/

/-- `towerFn` is above the identity on the ray, at every height. -/
theorem towerFn_ge_self (m : Nat) {x : Real} (hx : 1 ≤ x) :
    x ≤ EMLTree.towerFn m x := by
  have h := towerFn_mono 0 m hx
  have e : (0 : Nat) + m = m := by omega
  rw [e] at h
  exact h

/-- **One rung of tower absorbs any constant, past that constant.** `towerFn (m+1) = exp ∘ towerFn m`
and `exp T > 2T`, so `C + towerFn m x ≤ towerFn (m+1) x` as soon as `C < x`. -/
theorem const_add_tower_le_succ {C x : Real} (m : Nat) (hCx : C < x) (hx : 1 ≤ x) :
    C + EMLTree.towerFn m x ≤ EMLTree.towerFn (m + 1) x := by
  have hxT : x ≤ EMLTree.towerFn m x := towerFn_ge_self m hx
  have hCT : C < EMLTree.towerFn m x := lt_of_lt_of_le hCx hxT
  have h2 : (1 + 1) * EMLTree.towerFn m x < exp (EMLTree.towerFn m x) :=
    exp_gt_two_x (EMLTree.towerFn m x)
  have e2 : (1 + 1) * EMLTree.towerFn m x
      = EMLTree.towerFn m x + EMLTree.towerFn m x := by mach_ring
  rw [e2] at h2
  have u := add_lt_add_left hCT (EMLTree.towerFn m x)
  have ec : EMLTree.towerFn m x + C = C + EMLTree.towerFn m x := by mach_ring
  rw [ec] at u
  have hT : EMLTree.towerFn (m + 1) x = exp (EMLTree.towerFn m x) := rfl
  rw [hT]
  exact le_of_lt (lt_of_lt_of_le u (le_of_lt h2))

/-- `floor_lift` indexed by `≤` rather than by a difference — `k + d` is not definitionally the
target height when `d` is a variable, and every use site here has a `≤`. -/
theorem floor_lift_le {k m : Nat} (hkm : k ≤ m) (t : EMLTree) {X₁ : Real} (hX₁ : 1 ≤ X₁)
    (h : ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ t.eval x) :
    ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn m x)) ≤ t.eval x := by
  have e : k + (m - k) = m := by omega
  have h' := floor_lift (k := k) (d := m - k) t hX₁ h
  rw [e] at h'
  exact h'

/-! ## §3 — the step -/

/-- **One rung of the ladder.** Given the rung below and the two inputs at depth `j`, the rung at
`j + 1` follows at tower height `m + 1`, by the pointwise trichotomy of `(dt)`.

No `evSign_all`, no analytic block: the split is on the sign of `log (B x)` **at each point**. -/
theorem decayFloorUpTo_succ {j m : Nat} (hprev : DecayFloorUpTo j)
    (hnode : NodeDecayBound j m) (hlow : LowerEnvBound j m) :
    DecayFloorUpTo (j + 1) := by
  intro i hi
  rcases Nat.lt_or_ge i (j + 1) with hlt | hge
  · exact hprev i (by omega)
  -- i = j + 1
  have hij : i = j + 1 := by omega
  subst hij
  refine ⟨m + 1, ?_⟩
  intro t X₀ hd hX₀ hpos
  cases t with
  | const c =>
      obtain ⟨X₁, hX₁, hf⟩ :=
        decayFloor_upTo_two (EMLTree.const c) X₀ (by simp only [EMLTree.depth]; omega) hX₀ hpos
      exact ⟨X₁, hX₁, floor_lift_le (Nat.zero_le _) _ (le_trans hX₀ hX₁) hf⟩
  | var =>
      obtain ⟨X₁, hX₁, hf⟩ :=
        decayFloor_upTo_two EMLTree.var X₀ (by simp only [EMLTree.depth]; omega) hX₀ hpos
      exact ⟨X₁, hX₁, floor_lift_le (Nat.zero_le _) _ (le_trans hX₀ hX₁) hf⟩
  | eml A B =>
      have hA : A.depth ≤ j := by
        simp only [EMLTree.depth] at hd
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ j := by
        simp only [EMLTree.depth] at hd
        have := Nat.le_max_right A.depth B.depth; omega
      obtain ⟨C₂, XL, hXL, hL⟩ := hlow A hA
      obtain ⟨C₁, XD, hXD, hD⟩ := hnode A B hA hB
      have hXDp : (0 : Real) ≤ XD := le_trans (le_of_lt zero_lt_one_ax) hXD
      have he1 : (0 : Real) ≤ exp C₁ := le_of_lt (exp_pos C₁)
      have he2 : (0 : Real) ≤ exp C₂ := le_of_lt (exp_pos C₂)
      have hX0p : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX₀
      have hXLp : (0 : Real) ≤ XL := le_trans (le_of_lt zero_lt_one_ax) hXL
      -- one ray dominating all five thresholds; `exp C > C` stands in for the `max` this base lacks
      have hpos4 : (0 : Real) ≤ XD + exp C₁ + exp C₂ + XL := by
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hXDp he1) he2) hXLp
        have e : (0 : Real) + 0 + 0 + 0 = 0 := by mach_ring
        rw [e] at u; exact u
      refine ⟨X₀ + (XD + exp C₁ + exp C₂ + XL), le_add_nonneg' hpos4, ?_⟩
      intro x hx
      have hxX₀ : X₀ ≤ x := le_trans (le_add_nonneg' hpos4) hx
      have hxXD : XD ≤ x := by
        have e : X₀ + (XD + exp C₁ + exp C₂ + XL) = XD + (X₀ + exp C₁ + exp C₂ + XL) := by mach_ring
        rw [e] at hx
        refine le_trans (le_add_nonneg' ?_) hx
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hX0p he1) he2) hXLp
        have e2 : (0 : Real) + 0 + 0 + 0 = 0 := by mach_ring
        rw [e2] at u; exact u
      have hxXL : XL ≤ x := by
        have e : X₀ + (XD + exp C₁ + exp C₂ + XL) = XL + (X₀ + XD + exp C₁ + exp C₂) := by mach_ring
        rw [e] at hx
        refine le_trans (le_add_nonneg' ?_) hx
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hX0p hXDp) he1) he2
        have e2 : (0 : Real) + 0 + 0 + 0 = 0 := by mach_ring
        rw [e2] at u; exact u
      have hxC₁ : C₁ < x := by
        have e : X₀ + (XD + exp C₁ + exp C₂ + XL) = exp C₁ + (X₀ + XD + exp C₂ + XL) := by mach_ring
        rw [e] at hx
        refine lt_of_lt_of_le (exp_grows_strictly_thm C₁) (le_trans (le_add_nonneg' ?_) hx)
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hX0p hXDp) he2) hXLp
        have e2 : (0 : Real) + 0 + 0 + 0 = 0 := by mach_ring
        rw [e2] at u; exact u
      have hxC₂ : C₂ < x := by
        have e : X₀ + (XD + exp C₁ + exp C₂ + XL) = exp C₂ + (X₀ + XD + exp C₁ + XL) := by mach_ring
        rw [e] at hx
        refine lt_of_lt_of_le (exp_grows_strictly_thm C₂) (le_trans (le_add_nonneg' ?_) hx)
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hX0p hXDp) he1) hXLp
        have e2 : (0 : Real) + 0 + 0 + 0 = 0 := by mach_ring
        rw [e2] at u; exact u
      have hx1 : (1 : Real) ≤ x := le_trans hX₀ hxX₀
      have hnodepos : 0 < exp (A.eval x) - log (B.eval x) := hpos x hxX₀
      show exp (-(EMLTree.towerFn (m + 1) x)) ≤ exp (A.eval x) - log (B.eval x)
      rcases lt_total 0 (log (B.eval x)) with hlp | hlz | hln
      · have hb := hD x hxXD hlp hnodepos
        have hlog : -(C₁ + EMLTree.towerFn m x)
            ≤ log (exp (A.eval x) - log (B.eval x)) := by
          have u := neg_le_neg_wit hb
          have e : -(-log (exp (A.eval x) - log (B.eval x)))
              = log (exp (A.eval x) - log (B.eval x)) := by mach_ring
          rw [e] at u; exact u
        have hstep : exp (-(EMLTree.towerFn (m + 1) x))
            ≤ exp (-(C₁ + EMLTree.towerFn m x)) :=
          exp_monotone (neg_le_neg_wit (const_add_tower_le_succ m hxC₁ hx1))
        have hfin := exp_monotone hlog
        rw [exp_log hnodepos] at hfin
        exact le_trans hstep hfin
      · rw [← hlz]
        have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
        rw [e]
        exact exp_monotone (le_trans
          (neg_le_neg_wit (const_add_tower_le_succ m hxC₂ hx1)) (hL x hxXL))
      · have hgrow : exp (A.eval x) ≤ exp (A.eval x) - log (B.eval x) := by
          have u := add_le_add_wit (le_refl (exp (A.eval x)))
            (neg_le_neg_wit (le_of_lt hln))
          have e1 : exp (A.eval x) + -log (B.eval x)
              = exp (A.eval x) - log (B.eval x) := by mach_ring
          have e2 : exp (A.eval x) + -(0 : Real) = exp (A.eval x) := by mach_ring
          rw [e1, e2] at u; exact u
        refine le_trans ?_ hgrow
        exact exp_monotone (le_trans
          (neg_le_neg_wit (const_add_tower_le_succ m hxC₂ hx1)) (hL x hxXL))

/-! ## §4 — the step reproduces `(dt)`, height and all

An abstraction that does not reproduce the concrete case it was extracted from is a repackaging. -/

/-- `NodeDecayBound 2 1` **is** `Depth3DecayExp` — `towerFn 1 x` is `exp x` definitionally. -/
theorem nodeDecayBound_two : NodeDecayBound 2 1 := by
  intro A B hA hB
  exact depth3DecayExp_holds A B hA hB

/-- `LowerEnvBound 2 1` from the linear depth-2 floor, since `x ≤ exp x`. -/
theorem lowerEnvBound_two : LowerEnvBound 2 1 := by
  intro A hA
  obtain ⟨C, hC⟩ := depth_le_two_lower_on_ray A hA
  refine ⟨C, 1, le_refl 1, fun x hx => le_trans ?_ (hC x hx)⟩
  have hxe : x ≤ exp x := le_of_lt (exp_grows_strictly_thm x)
  have u := neg_le_neg_wit (add_le_add_wit (le_refl C) hxe)
  have e : -(C + x) = -C - x := by mach_ring
  rw [e] at u
  exact u

/-- **`(dt)` re-derived from the step**, at the same height `2`. The hand proof and the general step
agree, which is the evidence that `decayFloorUpTo_succ` is the right generalisation. -/
theorem decayFloorUpTo_three_via_step : DecayFloorUpTo 3 :=
  decayFloorUpTo_succ (j := 2) (m := 1) decayFloorUpTo_two nodeDecayBound_two lowerEnvBound_two

/-! ## §5 — the depth-3 lower envelope, so depth 4 rests on ONE thing

`(du)` flagged a friction and declined to call this assembly. Resolving it took giving
`LowerEnvBound` a **ray**, which is what the corpus does everywhere else and what the depth-2 growth
envelope forces: `depth_le_two_growth_envelope` holds only past a tree-dependent `X₀`, and absorbing
that into the constant would need every EML germ to be bounded on `[1, X₀]` — true, presumably, and
not something this base can prove (no compactness, no continuity).

With the ray, this is assembly after all: `node_lower_of_right_upper` turns an **upper** bound on the
right child into a **lower** bound on the node, and `depth_le_two_growth_envelope` supplies it.

Two details worth keeping. The envelope's `M` may be **negative**, so `E = exp (exp x + K) + M` can
fail `node_lower_of_right_upper`'s `0 ≤ E`; replacing `M` by `exp M` fixes both at once, since
`exp M > M`. And `exp (exp x + K) ≤ towerFn 3 x` is exactly `const_add_tower_le_succ` at `m = 1` —
the lemma written for the step turns out to do the arithmetic here too.

**So depth 4 now rests on `NodeDecayBound 3 m` alone.** -/

/-- **The depth-≤3 lower envelope**, at tower height `3`. -/
theorem lowerEnvBound_three : LowerEnvBound 3 3 := by
  intro A _
  cases A with
  | const c =>
      refine ⟨exp (-c), 1, le_refl 1, fun x hx => ?_⟩
      show -(exp (-c) + EMLTree.towerFn 3 x) ≤ c
      have hTp : (0 : Real) ≤ EMLTree.towerFn 3 x :=
        le_trans (le_of_lt zero_lt_one_ax) (towerFn_ge_one 3 hx)
      have h2 : -exp (-c) ≤ c := by
        have u := neg_le_neg_wit (le_of_lt (exp_grows_strictly_thm (-c)))
        have e : -(-c) = c := by mach_ring
        rw [e] at u; exact u
      exact le_trans (neg_le_neg_wit (le_add_nonneg' hTp)) h2
  | var =>
      refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
      show -((0 : Real) + EMLTree.towerFn 3 x) ≤ x
      have hTp : (0 : Real) ≤ EMLTree.towerFn 3 x :=
        le_trans (le_of_lt zero_lt_one_ax) (towerFn_ge_one 3 hx)
      have e : (0 : Real) + EMLTree.towerFn 3 x = EMLTree.towerFn 3 x := by mach_ring
      rw [e]
      have u := neg_le_neg_wit hTp
      have e2 : -(0 : Real) = 0 := by mach_ring
      rw [e2] at u
      exact le_trans u (le_trans (le_of_lt zero_lt_one_ax) hx)
  | eml P Q =>
      have hQ : Q.depth ≤ 2 := by
        simp only [EMLTree.depth] at *
        have := Nat.le_max_right P.depth Q.depth; omega
      obtain ⟨K, M, XU, hXU, hU⟩ := depth_le_two_growth_envelope Q hQ
      have hKp : (0 : Real) ≤ exp K := le_of_lt (exp_pos K)
      refine ⟨exp M, XU + exp K, le_trans hXU (le_add_nonneg' hKp), fun x hx => ?_⟩
      have hxXU : XU ≤ x := le_trans (le_add_nonneg' hKp) hx
      have hx1 : (1 : Real) ≤ x := le_trans hXU hxXU
      have hxK : K < x := by
        have e : XU + exp K = exp K + XU := by mach_ring
        rw [e] at hx
        refine lt_of_lt_of_le (exp_grows_strictly_thm K) (le_trans (le_add_nonneg' ?_) hx)
        exact le_trans (le_of_lt zero_lt_one_ax) hXU
      have hE0 : ∀ y : Real, XU ≤ y → (0 : Real) ≤ exp (exp y + K) + exp M := fun y _ =>
        le_of_lt (lt_of_lt_of_le (exp_pos _) (le_add_nonneg' (le_of_lt (exp_pos M))))
      have hEup : ∀ y : Real, XU ≤ y → Q.eval y ≤ exp (exp y + K) + exp M := by
        intro y hy
        exact le_trans (hU y hy)
          (add_le_add_wit (le_refl (exp (exp y + K))) (le_of_lt (exp_grows_strictly_thm M)))
      have hlow :=
        node_lower_of_right_upper P Q (fun y => exp (exp y + K) + exp M) XU hE0 hEup x hxXU
      refine le_trans (neg_le_neg_wit ?_) hlow
      -- exp (exp x + K) + exp M ≤ exp M + towerFn 3 x
      have habs : K + EMLTree.towerFn 1 x ≤ EMLTree.towerFn 2 x :=
        const_add_tower_le_succ 1 hxK hx1
      have e1 : K + EMLTree.towerFn 1 x = exp x + K := by
        show K + exp x = exp x + K
        mach_ring
      rw [e1] at habs
      have hmono : exp (exp x + K) ≤ EMLTree.towerFn 3 x := exp_monotone habs
      have u := add_le_add_wit hmono (le_refl (exp M))
      have e3 : EMLTree.towerFn 3 x + exp M = exp M + EMLTree.towerFn 3 x := by mach_ring
      rw [e3] at u
      exact u

/-! ### Route map: the two depth-4 conditions are NOT equidistant

`decayFloorUpTo_four_of_nodeDecay` (here) and `decayFloorUpTo_four_of_valueGap`
(`EMLValueGap:297`) both deliver `DecayFloorUpTo 4`, and reading them side by side suggests a
choice between two comparable routes. Measured against what is actually proved, they are not
comparable at all:

| condition | proved at | needed for depth 4 | rungs away |
|---|---|---|---|
| `NodeDecayBound` | `2 1` (`nodeDecayBound_two`, below) | `3 3` | **one** |
| `ValueGapBound`  | `0 0` (`valueGapBound_zero`) | `3 7` | **three** |

They are the same cancellation question in different coordinates —
`exp (A x) − log (B x) > 0` iff `B x < exp (exp (A x))` — so neither is intrinsically the easier
statement. What differs is only how far each has been carried, and nothing in either file says so.
Anyone picking up depth 4 should attack `NodeDecayBound 3 3`.

**And the next rung has one named missing artifact.** `nodeDecayBound_two` is not a general
argument: it *is* `depth3DecayExp_holds`, which runs off `depth_le_two_normal_form`
(`EMLDepthTameness:5896`) — the classification of depth-≤2 values. The method at each rung is
"classify the values at that depth", and **there is no `depth_le_three_normal_form` in the
corpus**. That, not the ladder step, is what depth 4 is waiting on: `decayFloorUpTo_succ` is
already general, and `lowerEnvBound_three` is already proved.

(Prose, not a theorem. "One rung away" is a statement about this corpus's current contents, not
about mathematics, and it stops being true the moment someone proves either condition.) -/

/-- **Depth 4 rests on one proposition.** Supply `NodeDecayBound 3 m` for any `m ≥ 3` and the rung
follows; the lower envelope is no longer part of the debt. -/
theorem decayFloorUpTo_four_of_nodeDecay (h : NodeDecayBound 3 3) : DecayFloorUpTo 4 :=
  decayFloorUpTo_succ (j := 3) (m := 3) decayFloorUpTo_three h lowerEnvBound_three

end MachLib
