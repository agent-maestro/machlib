import MachLib.EMLDecayFloor

/-!
# `DecayFloor` *is* the growth envelope, one reciprocal away

`(di)` showed the positive-`B` branch of `DecayFloor` contains the whole problem. This locates the
whole problem: it is the **growth envelope at infinity** — the very tool the ladder uses to attack
it.

## The ladder, and where it broke

`depth_le_three_growth_envelope` is built exactly the way the programme intends —

```
obtain ⟨K, M, XA, hXA1, hU⟩ := depth_le_two_growth_envelope A hA   -- U₂ for the LEFT child
obtain ⟨C, XB, hXB1, hV⟩    := depth_le_two_decay_on_ray   B hB   -- V₂ for the RIGHT child
```

— that is, `U (j+1) ⟸ U j ∧ V j`, literally. `(de)` then proved **`V₃` is false**: `decayFast`,
`exp (1 − x)` at depth 3, outruns `V`'s log-scale right-hand side. `DecayFloor` is the repair —
`V`'s log-scale floor replaced by a tower-scale one, which `decayFast` and `decayFaster` both meet.

The obvious hope is that the repaired `D` restores the ladder. **It does not**, and one construction
says why.

## The reciprocal is an EML tree, at `+2` depth

```
recipTree t = eml (eml (const 0) t) (const 1)
```

`eml (const 0) t` is `1 − log (t x)`, and the outer node exponentiates it (`log 1 = 0`), so

```
(recipTree t).eval x = exp (1 − log (t x))     = e / t x   when  t x > 0
recipTree_depth      : (recipTree t).depth = t.depth + 2
```

No cleverness is involved: **the grammar already contains `log`**, so a reciprocal costs two nodes.
(Not the `4` that `d(1/x)` costs — that four pins the constant to exactly `1` via the additive
shift. An envelope does not care about constants, so `e/t` serves.)

## Both transfers, division-free

`floor_of_recip_upper` — a **ceiling** on `recipTree t` is a **floor** on `t`:

> `exp (1 − log (t x)) ≤ E x`; take `log`: `1 − log (t x) ≤ log (E x) ≤ E x`; hence
> `log (t x) ≥ −E x`, hence `t x ≥ exp (−E x)`.

`upper_of_recip_floor` — a **floor** on `recipTree t` is a **ceiling** on `t`, one `+1` up:

> `exp (−E x) ≤ exp (1 − log (t x))`; take `log`: `log (t x) ≤ 1 + E x`; hence `t x ≤ exp (1 + E x)`.

Neither divides, and neither inspects the shape of `t`.

## The equivalence, and its price in depth

```
decayFloor_iff_growthEnvelope : DecayFloor ↔ GrowthEnvelope
```

* `GrowthEnvelope → DecayFloor` — `+2` depth, **same tower height `k`**. Apply the envelope to
  `recipTree t`.
* `DecayFloor → GrowthEnvelope` — `+3` depth, height `k+1`. Apply the floor to
  `recipTree (eTree t)`, whose value is `exp (1 − t x)`.

The second direction needs **no sign hypothesis**, which is the point of routing it through
`eTree`: `recipTree (eTree t)` is an `exp`, so it is positive *everywhere* and is a legal input to
`DecayFloor` for every `t`, sign unknown, `t` possibly very negative. That is what keeps this module
clear of `evSign_all` — and so clear of the analytic block (`rolle_ct`,
`analytic_finite_zeros_compact`, `eml_tree_analytic_on_interval`) that `evSign_all` carries. The
first draft of this file did use `evSign_all` for a case split and paid all three; the `eTree` route
costs one extra rung of depth and no axioms.

## The consequence

```
U (j+1)  ⟸  U j  ∧  D j        the step the corpus actually performs
D j      ⟸  U (j+2)             this module
U j      ⟸  D (j+3)             this module
```

> **The repaired step consumes the envelope two levels ABOVE the one it produces.**

Induction on depth cannot close that, in either direction. `D` and `U` are not two obligations of
which one might discharge the other; they are **one obligation** written two ways, and the map that
rewrites either into the other moves *up* the depth ladder both times. Any proof of either must find
an induction parameter that is not depth.

## The transfers are exercised

Both transfers take hypotheses, so both are fired on `decayFast` — `(de)`'s depth-3 witness. Its
reciprocal is `exp` on the nose (`1 − log (exp (1 − x)) = x`), so the ceiling is met with equality.
`decayFast_floor` already gives that tree a *better* floor than the transfer returns; the specimen
shows the machinery fires, not that it improves a bound.

## What this does not do

It bounds nothing and discharges nothing. `DecayFloor` stays **open**, and the ledger gate's
canary 9 — *"an `↔` is not a discharge"* — is precisely the rule that keeps it open. An equivalence
between two open statements relocates the difficulty; it does not remove it. Nor does it make
`DecayFloor` harder: the two were always the same question, and only now is that on the record.

It also explains, after the fact, why the shallow depths were free — and §5 now proves that half
outright. `depth_le_two_decay_on_ray` (`V₂`) is a *log-scale* floor, strictly stronger than the
tower-scale one, and `decayFloor_upTo_two` converts it: **every** eventually-positive tree of depth
≤ 2 is eventually `≥ exp (−x)`, tower height `0`. So `D 0`–`D 2` were in hand before this module.
The reciprocal route, fed the corpus's `U 3`, would reach only `D 1` — and `U 3` is stated in
explicit-constant form (`exp (exp (exp x + K) + M) + N`) rather than `towerFn` form, so even that
needs a conversion nobody has written. **The route buys no new rung either way.** Its content is the
shape of the obstruction, not a bound.
-/

namespace MachLib

open Real

/-! ## §0 — two facts about the tower on the ray -/

/-- `towerFn` is `≥ 1` on `[1, ∞)`, at every height. -/
theorem towerFn_ge_one (k : Nat) {x : Real} (hx : 1 ≤ x) : 1 ≤ EMLTree.towerFn k x := by
  induction k with
  | zero => exact hx
  | succ n ih =>
      show 1 ≤ exp (EMLTree.towerFn n x)
      exact le_trans ih (le_of_lt (exp_grows_strictly_thm _))

/-- `1 + T ≤ exp T` for `T ≥ 1`, from the unconditional `2T < exp T`. This is what the `+1` left
behind by `upper_of_recip_floor` costs: exactly one rung. -/
theorem one_add_le_exp_of_one_le {T : Real} (hT : 1 ≤ T) : 1 + T ≤ exp T := by
  have h2 : (1 + 1) * T < exp T := exp_gt_two_x T
  have hstep : 1 + T ≤ (1 + 1) * T := by
    have u := add_le_add_wit hT (le_refl T)
    have e : (1 + 1) * T = T + T := by mach_ring
    rw [e]; exact u
  exact le_trans hstep (le_of_lt h2)

/-! ## §1 — the reciprocal tree -/

/-- `1 − log (t x)`: the node that puts `t` under a `log`. -/
noncomputable def negLogTree (t : EMLTree) : EMLTree := EMLTree.eml (EMLTree.const 0) t

theorem negLogTree_eval (t : EMLTree) (x : Real) :
    (negLogTree t).eval x = 1 - log (t.eval x) := by
  show exp ((0 : Real)) - log (t.eval x) = 1 - log (t.eval x)
  rw [exp_zero]

/-- **`e / t` as an EML tree.** The grammar already has `log`, so a reciprocal is two nodes: put `t`
under a `log`, then exponentiate. -/
noncomputable def recipTree (t : EMLTree) : EMLTree :=
  EMLTree.eml (negLogTree t) (EMLTree.const 1)

theorem recipTree_eval (t : EMLTree) (x : Real) :
    (recipTree t).eval x = exp (1 - log (t.eval x)) := by
  show exp ((negLogTree t).eval x) - log ((1 : Real)) = _
  rw [negLogTree_eval, log_one]
  mach_ring

/-- The gloss made exact: where `t` is positive, the tree really is `e / t`. Nothing downstream
uses it — the transfers work on `exp (1 − log (t x))` directly, which is why they never divide — but
a file that calls a tree "the reciprocal" should be able to prove it. -/
theorem recipTree_eval_pos (t : EMLTree) (x : Real) (ht : 0 < t.eval x) :
    (recipTree t).eval x = exp 1 * (1 / t.eval x) := by
  rw [recipTree_eval]
  have e : (1 : Real) - log (t.eval x) = 1 + -log (t.eval x) := by mach_ring
  rw [e, exp_add, exp_neg_inv, exp_log ht]

/-- **Two nodes on the nose.** Not `≤`, and not the `4` that `d(1/x)` costs — that four pays for
pinning the constant to `1`, which an envelope never needs. -/
theorem recipTree_depth (t : EMLTree) : (recipTree t).depth = t.depth + 2 := by
  simp only [recipTree, negLogTree, EMLTree.depth]
  omega

/-- The reciprocal tree is positive **everywhere**, with no hypothesis on `t` — it is an `exp`. So
it is always a legal input to `DecayFloor`. -/
theorem recipTree_pos (t : EMLTree) (x : Real) : 0 < (recipTree t).eval x := by
  rw [recipTree_eval]; exact exp_pos _

/-! ## §2 — the two transfers -/

/-- **A ceiling on `recipTree t` is a floor on `t`.** Take `log` of the ceiling, use `log E ≤ E`,
exponentiate back. No division, no shape analysis, and the tower height is *unchanged*. -/
theorem floor_of_recip_upper (t : EMLTree) (E : Real → Real) (X₁ : Real)
    (hE : ∀ x : Real, X₁ ≤ x → 1 ≤ E x)
    (hpos : ∀ x : Real, X₁ ≤ x → 0 < t.eval x)
    (hup : ∀ x : Real, X₁ ≤ x → (recipTree t).eval x ≤ E x) :
    ∀ x : Real, X₁ ≤ x → exp (-(E x)) ≤ t.eval x := by
  intro x hx
  have hEx : 1 ≤ E x := hE x hx
  have htx : (0 : Real) < t.eval x := hpos x hx
  have h1 : exp (1 - log (t.eval x)) ≤ E x := by
    rw [← recipTree_eval]; exact hup x hx
  -- take `log`; the left side is an `exp`, so `log_exp` collapses it
  have h2 : 1 - log (t.eval x) ≤ log (E x) := by
    have m := log_le_log (exp_pos (1 - log (t.eval x))) h1
    rwa [log_exp] at m
  have h4 : 1 - log (t.eval x) ≤ E x := le_trans h2 (log_le_self_ge_one hEx)
  -- rearrange to `-(E x) ≤ log (t x)`, discarding the `+1` in our favour
  have hm1 : (-1 : Real) ≤ 0 := by
    have h := neg_le_neg_wit (le_of_lt zero_lt_one_ax)
    have e : -(0 : Real) = 0 := by mach_ring
    rwa [e] at h
  have h5 : -(E x) ≤ log (t.eval x) := by
    have a := neg_le_neg_wit h4
    have b := add_le_add_wit (le_refl (log (t.eval x))) hm1
    have el : log (t.eval x) + (-1 : Real) = -(1 - log (t.eval x)) := by
      mach_mpoly [log (t.eval x)]
    have er : log (t.eval x) + (0 : Real) = log (t.eval x) := by mach_ring
    rw [el, er] at b
    exact le_trans a b
  have h6 : exp (-(E x)) ≤ exp (log (t.eval x)) := exp_monotone h5
  rwa [exp_log htx] at h6

/-- **A floor on `recipTree t` is a ceiling on `t`**, one `+1` up. The mirror image: `log` both
sides and exponentiate back. -/
theorem upper_of_recip_floor (t : EMLTree) (E : Real → Real) (X₁ : Real)
    (hpos : ∀ x : Real, X₁ ≤ x → 0 < t.eval x)
    (hfl : ∀ x : Real, X₁ ≤ x → exp (-(E x)) ≤ (recipTree t).eval x) :
    ∀ x : Real, X₁ ≤ x → t.eval x ≤ exp (1 + E x) := by
  intro x hx
  have htx : (0 : Real) < t.eval x := hpos x hx
  have h1 : exp (-(E x)) ≤ exp (1 - log (t.eval x)) := by
    rw [← recipTree_eval]; exact hfl x hx
  have h2 : -(E x) ≤ 1 - log (t.eval x) := by
    have m := log_le_log (exp_pos (-(E x))) h1
    rwa [log_exp, log_exp] at m
  have h3 : log (t.eval x) ≤ 1 + E x := by
    have u := add_le_add_wit h2 (le_refl (log (t.eval x) + E x))
    have l : -(E x) + (log (t.eval x) + E x) = log (t.eval x) := by
      mach_mpoly [E x, log (t.eval x)]
    have r : (1 - log (t.eval x)) + (log (t.eval x) + E x) = 1 + E x := by
      mach_mpoly [E x, log (t.eval x)]
    rw [l, r] at u; exact u
  have h4 : exp (log (t.eval x)) ≤ exp (1 + E x) := exp_monotone h3
  rwa [exp_log htx] at h4

/-! ## §3 — the sign-free carrier `recipTree (eTree t)`

`recipTree` needs its argument positive to mean `e/t`. Composing with `eTree` supplies that for
free: `recipTree (eTree t)` is `exp (1 − t x)` — positive for **every** `t` and every `x`, with no
hypothesis and no `evSign_all`. One extra rung of depth buys the sign. -/

theorem recip_eTree_eval (t : EMLTree) (x : Real) :
    (recipTree (eTree t)).eval x = exp (1 - t.eval x) := by
  rw [recipTree_eval, eTree_eval, log_exp]

theorem recip_eTree_depth (t : EMLTree) : (recipTree (eTree t)).depth = t.depth + 3 := by
  rw [recipTree_depth, eTree_depth]
  omega

/-! ## §4 — the transfers fire on a real tree

Both transfers take hypotheses. A transfer whose hypotheses no tree satisfies proves nothing, so
each is exercised here on `decayFast` — `(de)`'s depth-3 witness, `exp (1 − x)`, positive
everywhere.

The reciprocal of `decayFast` is `exp` **on the nose**: `1 − log (exp (1 − x)) = x`. So the ceiling
`towerFn 1` is met with *equality*, which makes the specimen sharp rather than slack.

`decayFast_floor` already gives this tree the height-`0` floor, which is strictly better than the
height-`1` floor the transfer returns. That is the honest reading: **the specimen shows the
machinery fires, not that it improves a bound.** The transfer's output is only ever as good as the
ceiling fed in, and here the ceiling was chosen for concreteness, not sharpness. -/

/-- `recipTree decayFast` is `exp`, exactly — the `1 − log ∘ exp` cancels the `1 − x`. -/
theorem recipTree_decayFast_eval (x : Real) : (recipTree decayFast).eval x = exp x := by
  rw [recipTree_eval, decayFast_eval, log_exp]
  have e : (1 : Real) - (1 - x) = x := by mach_ring
  rw [e]

/-- **`floor_of_recip_upper` fires.** Ceiling `towerFn 1` on the reciprocal (met with equality) in,
floor `exp (−towerFn 1 x)` on `decayFast` out. -/
theorem decayFast_floor_via_transfer :
    ∀ x : Real, 1 ≤ x → exp (-(EMLTree.towerFn 1 x)) ≤ decayFast.eval x := by
  refine floor_of_recip_upper decayFast (EMLTree.towerFn 1) 1 ?_ ?_ ?_
  · intro x hx; exact towerFn_ge_one 1 hx
  · intro x _; exact decayFast_pos x
  · intro x _
    rw [recipTree_decayFast_eval]
    show exp x ≤ exp x
    exact le_refl _

/-- **`upper_of_recip_floor` fires.** Floor `exp (−towerFn 0 x)` on the reciprocal in, ceiling
`exp (1 + x)` on `decayFast` out — true, and slack, since `decayFast` is `exp (1 − x)`. -/
theorem decayFast_upper_via_transfer :
    ∀ x : Real, 1 ≤ x → decayFast.eval x ≤ exp (1 + EMLTree.towerFn 0 x) := by
  refine upper_of_recip_floor decayFast (EMLTree.towerFn 0) 1 ?_ ?_
  · intro x _; exact decayFast_pos x
  · intro x hx
    rw [recipTree_decayFast_eval]
    show exp (-x) ≤ exp x
    have h0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
    have hn : -x ≤ x := by
      have a := neg_le_neg_wit h0
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at a
      exact le_trans a h0
    exact exp_monotone hn

/-! ## §5 — the obligation is satisfiable across a whole depth class

`(dh)` checked `DecayFloor` against two hand-picked witnesses. This checks it against **every tree of
depth ≤ 2 at once**, and the height needed is `0`.

The input is `depth_le_two_decay_on_ray` (`V₂`), whose floor is *log-scale* — `−log (t x) ≤ C + log x`
— and therefore strictly stronger than the tower-scale floor `DecayFloor` asks for. The conversion is
the observation that `2 log x < x` (from `exp_gt_two_x` at `log x`), so once the ray is pushed past
`exp C` the constant is absorbed by the second `log x` and the whole right-hand side drops under `x`,
which is `towerFn 0`.

So `D 0`, `D 1`, `D 2` were all in hand before this module, and the reciprocal route buys no rung:
fed the corpus's `U 3` it would reach only `D 1`, and `U 3` is stated in explicit-constant form
(`exp (exp (exp x + K) + M) + N`) rather than `towerFn` form, so even that would need a conversion
nobody has written. The route's content is the *shape* of the obstruction, not a bound. -/

/-- **`DecayFloor`'s body holds at depth ≤ 2, with tower height `0`** — every eventually-positive
tree of depth ≤ 2 is eventually `≥ exp (−x)`.

Not a discharge of `DecayFloor`, which quantifies over every depth. It is the evidence that the
obligation is satisfiable on a whole depth class rather than at two witnesses. -/
theorem decayFloor_upTo_two (t : EMLTree) (X₀ : Real) (ht : t.depth ≤ 2) (hX₀ : 1 ≤ X₀)
    (hpos : ∀ x : Real, X₀ ≤ x → 0 < t.eval x) :
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn 0 x)) ≤ t.eval x := by
  obtain ⟨C, XV, hXV1, hV⟩ := depth_le_two_decay_on_ray t ht
  -- push the ray past `exp C`, so the constant is dominated by one of the two `log x`
  have hEC1 : (1 : Real) ≤ 1 + exp C := by
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos C))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u
    exact u
  obtain ⟨Y, hY1, hYX₀, hYXV⟩ := two_bounds' hX₀ hXV1
  obtain ⟨X₁, hX₁1, hX₁Y, hX₁E⟩ := two_bounds' hY1 hEC1
  refine ⟨X₁, le_trans hYX₀ hX₁Y, ?_⟩
  intro x hx
  have hxY : Y ≤ x := le_trans hX₁Y hx
  have hx1 : (1 : Real) ≤ x := le_trans hX₁1 hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have htx : (0 : Real) < t.eval x := hpos x (le_trans hYX₀ hxY)
  have hVx : -log (t.eval x) ≤ C + log x := hV x (le_trans hYXV hxY) htx
  -- `C ≤ log x`, because `x ≥ 1 + exp C ≥ exp C`
  have hClog : C ≤ log x := by
    have hxe : exp C ≤ x := by
      have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp C))
      have e : (0 : Real) + exp C = exp C := by mach_ring
      rw [e] at u
      exact le_trans u (le_trans hX₁E hx)
    have m := log_le_log (exp_pos C) hxe
    rwa [log_exp] at m
  -- `2 log x < x`
  have h2log : (1 + 1) * log x < x := by
    have h := exp_gt_two_x (log x)
    rwa [exp_log hx0] at h
  have hsum : C + log x ≤ (1 + 1) * log x := by
    have u := add_le_add_wit hClog (le_refl (log x))
    have e : (1 + 1) * log x = log x + log x := by mach_ring
    rw [e]; exact u
  have hlt : -log (t.eval x) ≤ x :=
    le_trans hVx (le_trans hsum (le_of_lt h2log))
  -- `-x ≤ log (t x)`, then exponentiate
  have hneg : -x ≤ log (t.eval x) := by
    have a := neg_le_neg_wit hlt
    have e : -(-log (t.eval x)) = log (t.eval x) := by mach_ring
    rwa [e] at a
  show exp (-x) ≤ t.eval x
  have h6 : exp (-x) ≤ exp (log (t.eval x)) := exp_monotone hneg
  rwa [exp_log htx] at h6

/-! ## §6 — the equivalence -/

/-- **The at-infinity growth envelope**, stated in `DecayFloor`'s own vocabulary: for each depth a
single tower height serves every tree of that depth as a ceiling.

No positivity hypothesis — a ceiling needs none. The asymmetry with `DecayFloor` is real, and §3 is
what pays for it. -/
def GrowthEnvelope : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (t : EMLTree) (X₀ : Real), t.depth ≤ j → 1 ≤ X₀ →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      t.eval x ≤ EMLTree.towerFn k x

/-- **The envelope two levels up gives the floor** — at the *same* tower height. -/
theorem decayFloor_of_growthEnvelope (hGE : GrowthEnvelope) : DecayFloor := by
  intro j
  obtain ⟨k, hk⟩ := hGE (j + 2)
  refine ⟨k, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  have hd2 : (recipTree t).depth ≤ j + 2 := by
    rw [recipTree_depth]; omega
  obtain ⟨X₁, hX₁, hup⟩ := hk (recipTree t) X₀ hd2 hX₀
  refine ⟨X₁, hX₁, ?_⟩
  refine floor_of_recip_upper t (EMLTree.towerFn k) X₁ ?_ ?_ hup
  · intro x hx
    exact towerFn_ge_one k (le_trans hX₀ (le_trans hX₁ hx))
  · intro x hx
    exact hpos x (le_trans hX₁ hx)

/-- **The floor three levels up gives the envelope** — at tower height `k + 1`.

Routed through `eTree` so that the input to `DecayFloor` is positive by construction. No sign
analysis, no `evSign_all`, and therefore none of the analytic axioms. -/
theorem growthEnvelope_of_decayFloor (hDF : DecayFloor) : GrowthEnvelope := by
  intro j
  obtain ⟨k, hk⟩ := hDF (j + 3)
  refine ⟨k + 1, ?_⟩
  intro t X₀ hdepth hX₀
  have hd3 : (recipTree (eTree t)).depth ≤ j + 3 := by
    rw [recip_eTree_depth]; omega
  obtain ⟨X₁, hX₁, hfl⟩ :=
    hk (recipTree (eTree t)) X₀ hd3 hX₀ (fun x _ => recipTree_pos (eTree t) x)
  refine ⟨X₁, hX₁, ?_⟩
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ (le_trans hX₁ hx)
  -- the general transfer, applied to `eTree t` — positive for free
  have hub :=
    upper_of_recip_floor (eTree t) (EMLTree.towerFn k) X₁
      (fun y _ => by rw [eTree_eval]; exact exp_pos _) hfl x hx
  rw [eTree_eval] at hub
  -- strip the outer `exp`
  have h3 : t.eval x ≤ 1 + EMLTree.towerFn k x := by
    have m := log_le_log (exp_pos (t.eval x)) hub
    rwa [log_exp, log_exp] at m
  show t.eval x ≤ exp (EMLTree.towerFn k x)
  exact le_trans h3 (one_add_le_exp_of_one_le (towerFn_ge_one k hx1))

/-- **`DecayFloor` and the growth envelope are one obligation.** The map between them is
`recipTree`, and it costs depth in *both* directions — `+2` one way, `+3` the other — so neither can
be bootstrapped from the other by induction on depth. -/
theorem decayFloor_iff_growthEnvelope : DecayFloor ↔ GrowthEnvelope :=
  ⟨growthEnvelope_of_decayFloor, decayFloor_of_growthEnvelope⟩

end MachLib
