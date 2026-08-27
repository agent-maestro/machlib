import MachLib.EMLDecayLadderStep

/-!
# The convexity transfer, once, at every depth

`(dv)` left depth 4 resting on `NodeDecayBound 3 3`. This factors *that* obligation the way `(du)`
factored the rung: the node-level statement splits into a **value-level gap** plus a **growth bound**,
and the transfer between them is proved once for all depths.

```
nodeDecayBound_of_valueGap : ValueGapBound j m → ExpUpperBound j m → NodeDecayBound j (m + 1)
```

## Why value level is the right vocabulary

`exp (A x) − log (B x) > 0` is exactly `B x < exp (exp (A x))`, so the node's positivity is a
*value-level* statement about `B` staying under `exp ∘ exp ∘ A`. Every discharged piece of
`Depth3DecayExp` — `ExpExpGapBelow`, `BoundedCellApproach`, `BoundedEmlCellApproach`,
`BoundedEmlCellApproachLarge` — is written at that level. So this is not a re-encoding for its own
sake: it is the vocabulary the corpus already proves things in, and depth 4's residue lands in it.

## The transfer, and the shape that makes it division-free

The relation wanted is `E − q ≤ node · E` with `E = exp (exp (A x))` and `q = B x` — a value gap
becomes a node gap, losing only the factor `E`. The corpus states it that way for `A = var` inside
`depth_three_decayExp_var_left_of_gap`, calling it "reverse convexity".

The clean derivation is not the one that stares at `E`. Put `d = node = u − log q` with
`u = exp (A x)`; then `q · exp d = exp u = E`, and the whole claim collapses to

```
exp d − 1 ≤ d · exp d
```

which follows from `log_le_sub_one` applied at `exp (−d)`: `−d ≤ exp (−d) − 1`, so
`(1 − d) · exp d ≤ exp (−d) · exp d = 1`. **No division anywhere**, which matters in a base that has
`/` but almost no lemmas about it.

## What depth 4 costs after this

`ValueGapBound 3 m` and `ExpUpperBound 3 m`. The second is the same kind of assembly
`lowerEnvBound_three` turned out to be; the first is the residue, now stated in the vocabulary the
depth-3 cell decomposition already speaks.
-/

namespace MachLib

open Real

/-! ## §1 — the transfer -/

/-- `exp d − 1 ≤ d · exp d`, for every `d`. From `log_le_sub_one` at `exp (−d)`, which gives
`1 − d ≤ exp (−d)`; multiply by `exp d`. -/
theorem exp_sub_one_le_mul (d : Real) : exp d - 1 ≤ d * exp d := by
  have h := log_le_sub_one (exp_pos (-d))
  rw [log_exp] at h
  have h2 : 1 - d ≤ exp (-d) := by
    have u := add_le_add_wit (le_refl (1 : Real)) h
    have e1 : (1 : Real) + -d = 1 - d := by mach_ring
    have e2 : (1 : Real) + (exp (-d) - 1) = exp (-d) := by mach_ring
    rw [e1, e2] at u; exact u
  have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (exp_pos d))
  have e3 : exp (-d) * exp d = 1 := by
    rw [← exp_add]
    have e : -d + d = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  rw [e3] at h3
  have e4 : (1 - d) * exp d = exp d - d * exp d := by mach_ring
  rw [e4] at h3
  have u := add_le_add_wit h3 (le_refl (d * exp d - 1))
  have e5 : exp d - d * exp d + (d * exp d - 1) = exp d - 1 := by mach_ring
  have e6 : (1 : Real) + (d * exp d - 1) = d * exp d := by mach_ring
  rw [e5, e6] at u; exact u

/-- **Reverse convexity, at any left child.** A gap at the *value* level becomes a gap at the *node*
level, losing only the factor `exp u`. -/
theorem value_gap_le_node_mul (u q : Real) (hq : 0 < q) :
    exp u - q ≤ (u - log q) * exp u := by
  have hd := exp_sub_one_le_mul (u - log q)
  have hE : q * exp (u - log q) = exp u := by
    calc q * exp (u - log q)
        = exp (log q) * exp (u - log q) := by rw [exp_log hq]
      _ = exp (log q + (u - log q)) := by rw [exp_add]
      _ = exp u := by
            have e : log q + (u - log q) = u := by mach_ring
            rw [e]
  have h3 := mul_le_mul_of_nonneg_left hd (le_of_lt hq)
  have eL : q * (exp (u - log q) - 1) = q * exp (u - log q) - q := by mach_ring
  have eR : q * ((u - log q) * exp (u - log q))
      = (u - log q) * (q * exp (u - log q)) := by mach_ring
  rw [eL, eR, hE] at h3
  exact h3

/-! ## §2 — the two inputs, at value level -/

/-- **The value-level gap.** `B` stays under `exp ∘ exp ∘ A` by an effective margin — the vocabulary
`ExpExpGapBelow` and the `…CellApproach` family are written in. -/
def ValueGapBound (j m : Nat) : Prop :=
  ∀ A B : EMLTree, A.depth ≤ j → B.depth ≤ j →
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < B.eval x →
      B.eval x < exp (exp (A.eval x)) →
        exp (-(C + EMLTree.towerFn m x)) ≤ exp (exp (A.eval x)) - B.eval x

/-- **The growth bound** the transfer's lost factor needs. -/
def ExpUpperBound (j m : Nat) : Prop :=
  ∀ A : EMLTree, A.depth ≤ j → ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
    exp (A.eval x) ≤ C + EMLTree.towerFn m x

/-! ## §3 — the factoring -/

/-- **`NodeDecayBound` factors into a value gap and a growth bound**, at one extra rung of tower —
the rung paying for `2 · towerFn m x ≤ towerFn (m+1) x`, which is `exp T > 2T`. -/
theorem nodeDecayBound_of_valueGap {j m : Nat}
    (hgap : ValueGapBound j m) (hup : ExpUpperBound j m) : NodeDecayBound j (m + 1) := by
  intro A B hA hB
  obtain ⟨C₁, XG, hXG, hG⟩ := hgap A B hA hB
  obtain ⟨C₂, XU, hXU, hU⟩ := hup A hA
  have hXGp : (0 : Real) ≤ XG := le_trans (le_of_lt zero_lt_one_ax) hXG
  have hXUp : (0 : Real) ≤ XU := le_trans (le_of_lt zero_lt_one_ax) hXU
  refine ⟨C₁ + C₂, XG + XU, le_trans hXG (le_add_nonneg' hXUp), ?_⟩
  intro x hx hlogpos hnodepos
  have hxXG : XG ≤ x := le_trans (le_add_nonneg' hXUp) hx
  have hxXU : XU ≤ x := by
    have e : XG + XU = XU + XG := by mach_ring
    rw [e] at hx
    exact le_trans (le_add_nonneg' hXGp) hx
  have hx1 : (1 : Real) ≤ x := le_trans hXG hxXG
  -- `log (B x) > 0` forces `B x > 0`
  have hBpos : (0 : Real) < B.eval x := by
    rcases lt_total 0 (B.eval x) with hb | hb | hb
    · exact hb
    · rw [log_nonpos (le_of_eq hb.symm)] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
    · rw [log_nonpos (le_of_lt hb)] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
  -- positivity of the node is exactly `B x < exp (exp (A x))`
  have hlt : B.eval x < exp (exp (A.eval x)) := by
    have hloglt : log (B.eval x) < exp (A.eval x) := by
      have v := add_lt_add_left hnodepos (log (B.eval x))
      have e1 : log (B.eval x) + (0 : Real) = log (B.eval x) := by mach_ring
      have e2 : log (B.eval x) + (exp (A.eval x) - log (B.eval x))
          = exp (A.eval x) := by mach_ring
      rw [e1, e2] at v; exact v
    have hm := exp_lt hloglt
    rw [exp_log hBpos] at hm
    exact hm
  -- transfer the value gap to the node
  have htrans := value_gap_le_node_mul (exp (A.eval x)) (B.eval x) hBpos
  have hgapx := hG x hxXG hBpos hlt
  have hchain : exp (-(C₁ + EMLTree.towerFn m x))
      ≤ (exp (A.eval x) - log (B.eval x)) * exp (exp (A.eval x)) :=
    le_trans hgapx htrans
  -- replace the lost factor by its bound
  have hEle : exp (exp (A.eval x)) ≤ exp (C₂ + EMLTree.towerFn m x) :=
    exp_monotone (hU x hxXU)
  have hnodenn : (0 : Real) ≤ exp (A.eval x) - log (B.eval x) := le_of_lt hnodepos
  have hbig : exp (-(C₁ + EMLTree.towerFn m x))
      ≤ (exp (A.eval x) - log (B.eval x)) * exp (C₂ + EMLTree.towerFn m x) :=
    le_trans hchain (mul_le_mul_of_nonneg_left hEle hnodenn)
  -- divide through by the (positive) factor, multiplicatively
  have hmul := mul_le_mul_of_nonneg_right hbig
    (le_of_lt (exp_pos (-(C₂ + EMLTree.towerFn m x))))
  have eR : (exp (A.eval x) - log (B.eval x)) * exp (C₂ + EMLTree.towerFn m x)
        * exp (-(C₂ + EMLTree.towerFn m x))
      = (exp (A.eval x) - log (B.eval x))
        * (exp (C₂ + EMLTree.towerFn m x) * exp (-(C₂ + EMLTree.towerFn m x))) := by mach_ring
  have eOne : exp (C₂ + EMLTree.towerFn m x) * exp (-(C₂ + EMLTree.towerFn m x)) = 1 := by
    rw [← exp_add]
    have e : C₂ + EMLTree.towerFn m x + -(C₂ + EMLTree.towerFn m x) = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  have eL : exp (-(C₁ + EMLTree.towerFn m x)) * exp (-(C₂ + EMLTree.towerFn m x))
      = exp (-(C₁ + EMLTree.towerFn m x) + -(C₂ + EMLTree.towerFn m x)) := by rw [exp_add]
  rw [eR, eOne, eL] at hmul
  have eMul : (exp (A.eval x) - log (B.eval x)) * (1 : Real)
      = exp (A.eval x) - log (B.eval x) := by mach_ring
  rw [eMul] at hmul
  -- one rung of tower absorbs the doubled bound
  have hdouble : C₁ + C₂ + EMLTree.towerFn m x + EMLTree.towerFn m x
      ≤ C₁ + C₂ + EMLTree.towerFn (m + 1) x := by
    have h2 : (1 + 1) * EMLTree.towerFn m x < exp (EMLTree.towerFn m x) :=
      exp_gt_two_x (EMLTree.towerFn m x)
    have e2 : (1 + 1) * EMLTree.towerFn m x
        = EMLTree.towerFn m x + EMLTree.towerFn m x := by mach_ring
    rw [e2] at h2
    have hT : EMLTree.towerFn (m + 1) x = exp (EMLTree.towerFn m x) := rfl
    rw [hT]
    have u := add_le_add_wit (le_refl (C₁ + C₂)) (le_of_lt h2)
    have e3 : C₁ + C₂ + (EMLTree.towerFn m x + EMLTree.towerFn m x)
        = C₁ + C₂ + EMLTree.towerFn m x + EMLTree.towerFn m x := by mach_ring
    rw [e3] at u; exact u
  have hfloor : exp (-(C₁ + C₂ + EMLTree.towerFn (m + 1) x))
      ≤ exp (A.eval x) - log (B.eval x) := by
    refine le_trans (exp_monotone (neg_le_neg_wit hdouble)) ?_
    have e : -(C₁ + C₂ + EMLTree.towerFn m x + EMLTree.towerFn m x)
        = -(C₁ + EMLTree.towerFn m x) + -(C₂ + EMLTree.towerFn m x) := by mach_ring
    rw [e]
    exact hmul
  -- and back to the `-log` form
  have hlog := log_le_log (exp_pos _) hfloor
  rw [log_exp] at hlog
  have u := neg_le_neg_wit hlog
  have e : -(-(C₁ + C₂ + EMLTree.towerFn (m + 1) x))
      = C₁ + C₂ + EMLTree.towerFn (m + 1) x := by mach_ring
  rw [e] at u
  exact u

/-! ## §4 — the growth input is assembly too, so depth 4 rests on ONE value-level residue

`depth_le_three_growth_envelope` gives `A x ≤ exp (exp (exp x + K) + M) + N`. Four applications of
`const_add_tower_le_succ` — one per additive constant, one per `exp` — climb that to `towerFn 6 x`,
and one more `exp` gives the bound on `exp (A x)`.

The height (`7`) is not sharp and does not need to be: `ValueGapBound j m` gets **weaker** as `m`
grows, so asking for it at `7` is asking for less than at `3`. -/

/-- Weakening in the tower height: a lower envelope at height `m` is one at any greater height. -/
theorem lowerEnvBound_mono {j m m' : Nat} (hmm : m ≤ m') (hb : LowerEnvBound j m) :
    LowerEnvBound j m' := by
  intro A hA
  obtain ⟨C, XL, hXL, hL⟩ := hb A hA
  refine ⟨C, XL, hXL, fun x hx => le_trans ?_ (hL x hx)⟩
  have hx1 : (1 : Real) ≤ x := le_trans hXL hx
  have hmono : EMLTree.towerFn m x ≤ EMLTree.towerFn m' x := by
    have e : m + (m' - m) = m' := by omega
    have h := towerFn_mono m (m' - m) hx1
    rw [e] at h; exact h
  exact neg_le_neg_wit (add_le_add_wit (le_refl C) hmono)

/-- **`ExpUpperBound 3 7`**, from the depth-3 growth envelope. -/
theorem expUpperBound_three : ExpUpperBound 3 7 := by
  intro A hA
  obtain ⟨K, M, N, XU, hXU, hU⟩ := depth_le_three_growth_envelope A hA
  have hK : (0 : Real) ≤ exp K := le_of_lt (exp_pos K)
  have hM : (0 : Real) ≤ exp M := le_of_lt (exp_pos M)
  have hN : (0 : Real) ≤ exp N := le_of_lt (exp_pos N)
  have hXUp : (0 : Real) ≤ XU := le_trans (le_of_lt zero_lt_one_ax) hXU
  have hsum : (0 : Real) ≤ exp K + exp M + exp N := by
    have u := add_le_add_wit (add_le_add_wit hK hM) hN
    have e : (0 : Real) + 0 + 0 = 0 := by mach_ring
    rw [e] at u; exact u
  refine ⟨0, XU + (exp K + exp M + exp N), le_trans hXU (le_add_nonneg' hsum), ?_⟩
  intro x hx
  have hxXU : XU ≤ x := le_trans (le_add_nonneg' hsum) hx
  have hx1 : (1 : Real) ≤ x := le_trans hXU hxXU
  have hxK : K < x := by
    have e : XU + (exp K + exp M + exp N) = exp K + (XU + exp M + exp N) := by mach_ring
    rw [e] at hx
    refine lt_of_lt_of_le (exp_grows_strictly_thm K) (le_trans (le_add_nonneg' ?_) hx)
    have u := add_le_add_wit (add_le_add_wit hXUp hM) hN
    have e2 : (0 : Real) + 0 + 0 = 0 := by mach_ring
    rw [e2] at u; exact u
  have hxM : M < x := by
    have e : XU + (exp K + exp M + exp N) = exp M + (XU + exp K + exp N) := by mach_ring
    rw [e] at hx
    refine lt_of_lt_of_le (exp_grows_strictly_thm M) (le_trans (le_add_nonneg' ?_) hx)
    have u := add_le_add_wit (add_le_add_wit hXUp hK) hN
    have e2 : (0 : Real) + 0 + 0 = 0 := by mach_ring
    rw [e2] at u; exact u
  have hxN : N < x := by
    have e : XU + (exp K + exp M + exp N) = exp N + (XU + exp K + exp M) := by mach_ring
    rw [e] at hx
    refine lt_of_lt_of_le (exp_grows_strictly_thm N) (le_trans (le_add_nonneg' ?_) hx)
    have u := add_le_add_wit (add_le_add_wit hXUp hK) hM
    have e2 : (0 : Real) + 0 + 0 = 0 := by mach_ring
    rw [e2] at u; exact u
  -- climb: exp x + K ≤ T2, so exp(exp x + K) ≤ T3
  have s1 : exp x + K ≤ EMLTree.towerFn 2 x := by
    have h := const_add_tower_le_succ 1 hxK hx1
    have e : K + EMLTree.towerFn 1 x = exp x + K := by
      show K + exp x = exp x + K
      mach_ring
    rw [e] at h; exact h
  have s2 : exp (exp x + K) ≤ EMLTree.towerFn 3 x := exp_monotone s1
  -- + M ≤ T4, so exp(…) ≤ T5
  have s3 : exp (exp x + K) + M ≤ EMLTree.towerFn 4 x := by
    have h := const_add_tower_le_succ 3 hxM hx1
    have u := add_le_add_wit s2 (le_refl M)
    have e : EMLTree.towerFn 3 x + M = M + EMLTree.towerFn 3 x := by mach_ring
    rw [e] at u
    exact le_trans u h
  have s4 : exp (exp (exp x + K) + M) ≤ EMLTree.towerFn 5 x := exp_monotone s3
  -- + N ≤ T6
  have s5 : exp (exp (exp x + K) + M) + N ≤ EMLTree.towerFn 6 x := by
    have h := const_add_tower_le_succ 5 hxN hx1
    have u := add_le_add_wit s4 (le_refl N)
    have e : EMLTree.towerFn 5 x + N = N + EMLTree.towerFn 5 x := by mach_ring
    rw [e] at u
    exact le_trans u h
  have s6 : exp (A.eval x) ≤ EMLTree.towerFn 7 x :=
    exp_monotone (le_trans (hU x hxXU) s5)
  have e0 : (0 : Real) + EMLTree.towerFn 7 x = EMLTree.towerFn 7 x := by mach_ring
  rw [e0]
  exact s6

/-- **Depth 4 rests on `ValueGapBound 3 7` alone.** Everything else — the lower envelope, the growth
bound, the convexity transfer, the ladder step — is proved. -/
theorem decayFloorUpTo_four_of_valueGap (hg : ValueGapBound 3 7) : DecayFloorUpTo 4 :=
  decayFloorUpTo_succ (j := 3) (m := 8) decayFloorUpTo_three
    (nodeDecayBound_of_valueGap hg expUpperBound_three)
    (lowerEnvBound_mono (by omega) lowerEnvBound_three)

/-! ## §5 — the transfer runs both ways, so §3 is a REFORMULATION, not a shrink

`(dw)` called §3 a factoring. That word suggests the value-level statement is *easier* than the
node-level one. It is not obviously so, and the reason is that the same substitution gives the
**reverse** inequality for free:

```
value_gap_le_node_mul  :  exp u − q  ≤  (u − log q) * exp u      -- value gap ⟹ node gap
node_mul_le_value_gap  :  q * (u − log q)  ≤  exp u − q          -- node gap ⟹ value gap
```

The two bracket the gap between the factors `q` and `exp u`. So a node floor gives a value floor and
vice versa, **provided the other factor is itself bounded** — `exp u ≤ …` for one direction (that is
`ExpUpperBound`, and §4 proves it) and `q ≥ …` for the other.

**And `q ≥ …` is exactly a `DecayFloor` for `B`** — which at depth ≤ 3 is `decayFloorUpTo_three`, in
hand. So the two obligations are equivalent up to one thing, and it is worth naming precisely:

> The converse needs `B` positive on a **ray**, because `decayFloorUpTo_three` is an eventual
> statement. `ValueGapBound`'s `0 < B.eval x` is **pointwise**, inside the `∀ x`. From positivity at
> one point no ray follows, so the converse does not go through as stated.

That is the same pointwise/eventual distinction that made `(dt)` work, cutting the other way. It was
worth the pointwise form there — it kept `evSign_all` and the analytic block out of the entire ladder
— and it is worth it here too, but the price is that §3 cannot be *proved* to be a genuine reduction,
only observed not to be obviously one.

**So: §3 buys vocabulary, not difficulty.** `ValueGapBound 3 7` is stated where `ExpExpGapBelow` and
the `…CellApproach` family are stated, which is where the depth-≤2 answers live and where a depth-≤3
answer would be found. That was the claim `(dw)` should have made, and this section makes it. -/

/-- `d ≤ exp d − 1`, for **every** `d` — the mirror of `exp_sub_one_le_mul`, and from the same
lemma. Note it needs no sign hypothesis, where `exp_gt_one_plus_self` would demand `0 < d`. -/
theorem le_exp_sub_one (d : Real) : d ≤ exp d - 1 := by
  have h := log_le_sub_one (exp_pos d)
  rw [log_exp] at h
  exact h

/-- **The reverse transfer.** A node gap gives a value gap, losing only the factor `q`. -/
theorem node_mul_le_value_gap (u q : Real) (hq : 0 < q) :
    q * (u - log q) ≤ exp u - q := by
  have hd := le_exp_sub_one (u - log q)
  have hE : q * exp (u - log q) = exp u := by
    calc q * exp (u - log q)
        = exp (log q) * exp (u - log q) := by rw [exp_log hq]
      _ = exp (log q + (u - log q)) := by rw [exp_add]
      _ = exp u := by
            have e : log q + (u - log q) = u := by mach_ring
            rw [e]
  have h3 := mul_le_mul_of_nonneg_left hd (le_of_lt hq)
  have eR : q * (exp (u - log q) - 1) = q * exp (u - log q) - q := by mach_ring
  rw [eR, hE] at h3
  exact h3

/-- **The two transfers bracket the gap**, between the factors `q` and `exp u`. Stated together so
the symmetry is on the record rather than inferred. -/
theorem value_gap_brackets (u q : Real) (hq : 0 < q) :
    q * (u - log q) ≤ exp u - q ∧ exp u - q ≤ (u - log q) * exp u :=
  ⟨node_mul_le_value_gap u q hq, value_gap_le_node_mul u q hq⟩

end MachLib
