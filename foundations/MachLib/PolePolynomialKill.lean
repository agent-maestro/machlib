import MachLib.PevRoots
import MachLib.PevSignOnCutFree
import MachLib.EMLDepth2InvX
import MachLib.EMLFTranscendence

/-!
# A polynomial cannot survive exponential decay at a pole

The last clause `OneQueryLevelSet` needs is a **non-zero witness inside every bounded pole-free
component**. `¬ EvZeroF` supplies one only on a *tail*, and a bounded component between two poles is
exactly where no tail reaches. This module removes the need for one on the branch where it can be
removed.

## The situation

On a cut-free component the rational argument `S` has constant sign. Where that sign is negative the
germ is `bipev N x (exp (S x))` — `Fbasis` is `exp` there, by totalisation. If the germ vanishes
identically on the component then, splitting off the constant-in-`y` coefficient,

```
N₀(x)  =  − exp (S x) · H(x)          with H bounded near the endpoint
```

and the endpoints of a *bounded* component are **poles of `S`**. Where `S → −∞` the right-hand side
decays faster than any power of `x − r`, while a non-zero polynomial vanishes to *finite* order. So
`N₀ ≡ 0`, `exp (S x) ≠ 0` divides out, and the same argument runs on the next coefficient.

The conclusion is stronger than "this component is fine": every coefficient dies, so the germ
vanishes **everywhere**, and the level set is co-finite. The bad case does not exist rather than
being excluded.

## Why the `−∞` end is the easy one

This is the reverse of how the two ends read. Where `S → +∞` the germ diverges and the
continuity-versus-divergence barrier applies in principle — but that barrier has no user outside its
own module and driving it needs *local* dominance, while every dominance tool here is tail-shaped.
The `−∞` end, which looks worse, hands over super-polynomial decay for free.

Note also that growth machinery is **unavailable** for `BoundedGermTranscendence` — `F ∘ S` is
polynomially enveloped there, as a theorem — and is exactly the right tool *here*. Same machinery,
opposite end: decay at a finite pole rather than growth along a tail.

## Status

§§1–5 are complete: the endpoint kill (`poly_zero_of_exp_decay`), the coefficient bounds, and the
germ-side wiring (`bipev_zero_near_pole_kills_head`). What remains outside this module is supplying
the pole lower bound `S (r + exp (−T)) ≤ −(c · exp T)` from the rational structure of `S`, which is
`PevRoots`/`deflate` work at the *other* end of the germ.

## The evaluation point

Everything is stated at `x = r + exp (−T)`, the device the depth-2/3 pole arguments already use so
that no proof carries threshold arithmetic. Under it a polynomial vanishing to order `a` contributes
`exp (−a·T)` and a pole contributes `exp (−c·exp T)`, so the comparison collapses to

```
c · exp T  ≤  a·T + const
```

which is literally `exp_pole_contradiction`'s hypothesis. That lemma is the endgame, already written
for the depth-2/3 arguments and reused verbatim.
-/

namespace MachLib

open Real

/-! ## §1 — a continuous function taking arbitrarily small values arbitrarily close to `r` -/

private theorem add_lt_add_p {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  have s1 : c + a < c + b := add_lt_add_left h1 c
  have s2 : b + c < b + d := add_lt_add_left h2 b
  have e1 : c + a = a + c := by mach_ring
  have e2 : c + b = b + c := by mach_ring
  rw [e1, e2] at s1
  exact lt_trans_ax s1 s2


/-- **If `f` is continuous at `r` and takes values below every `ε` at points within every `δ` of
`r`, then `f r = 0`.**

No limits are needed and none exist in this corpus: the hypothesis is the `∃`-form directly, and the
proof is the two-ε triangle argument. This is the only place continuity enters the module. -/
theorem eq_zero_of_small_nearby {f : Real → Real} {r : Real}
    (hc : ContinuousAt f r)
    (hsmall : ∀ ε : Real, 0 < ε → ∀ δ : Real, 0 < δ →
      ∃ y : Real, abs (y - r) < δ ∧ abs (f y) < ε) :
    f r = 0 := by
  refine Classical.byContradiction (fun hne => ?_)
  have hpos : 0 < abs (f r) := abs_pos_of_ne hne
  -- `ε := |f r| / 2`
  have hε : 0 < abs (f r) / (1 + 1) := div_pos_of_pos_pos hpos two_pos
  obtain ⟨δ, hδ, hδ'⟩ := hc _ hε
  obtain ⟨y, hy, hfy⟩ := hsmall _ hε δ hδ
  have hnear := hδ' y hy
  -- `|f r| ≤ |f r − f y| + |f y| < ε + ε = |f r|`
  have hsplit : abs (f r) ≤ abs (f y - f r) + abs (f y) := by
    have e : f r = -(f y - f r) + f y := by mach_ring
    have h := abs_add (-(f y - f r)) (f y)
    rw [← e] at h
    have hneg : abs (-(f y - f r)) = abs (f y - f r) := abs_neg _
    rw [hneg] at h
    exact h
  have hsum : abs (f y - f r) + abs (f y) < abs (f r) := by
    have hadd := add_lt_add_p hnear hfy
    have e : abs (f r) / (1 + 1) + abs (f r) / (1 + 1) = abs (f r) := by
      rw [show abs (f r) / (1 + 1) + abs (f r) / (1 + 1)
            = (1 + 1) * (abs (f r) / (1 + 1)) from by mach_ring]
      exact mul_div_cancel_left (ne_of_gt two_pos)
    rw [e] at hadd
    exact hadd
  exact lt_irrefl_ax _ (lt_of_le_of_lt hsplit hsum)

/-! ## §2 — the witness supply

`exp_beats_linear_past` is *existential* — "there is an `x` beyond any bound with `α·x + β < exp x`"
— and that is exactly the shape wanted, because `hsmall` asks for one point per `(ε, δ)` rather than
for a tail. One application supplies both conditions: its threshold argument carries the `δ`
requirement, its conclusion the `ε` one. No "for all large `T`" statement appears anywhere here.

### A false-absence note, kept because it was nearly shipped

An earlier revision of this header listed four field lemmas as **missing** and deferred §2 on that
basis. **All four existed.** They are named differently from the names I searched for:

| what I searched for | what it is actually called |
| --- | --- |
| `div_self` | `self_div` (`FieldLemmas`) |
| `mul_one_div_cancel` | `mul_inv` — a `Basic` **axiom**, listed in `FieldLemmas`' own header |
| `one_div_one_div` | `one_div_one_div_pos` (`EMLDepthTameness`) |
| `mul_lt_mul_of_pos_left` | `mul_lt_mul_pos_left_wit` (`EMLDepth2InvX`), already imported here |

Searching by *name* is searching for the name **you** would have chosen; this corpus chose others.
Searching by *statement* found all four in one pass. The narrower failure — a grep pattern requiring
a trailing space, which reported `div_pos_of_pos_pos` absent while this file was compiling with it —
is the same disease with a smaller radius. -/

/-- **Super-polynomial decay along `x = r + exp (−T)` supplies `hsmall`.** -/
theorem small_nearby_of_exp_decay {f : Real → Real} {r a c C : Real}
    (ha : 0 ≤ a) (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ T : Real, 1 ≤ T → abs (f (r + exp (-T))) ≤ C * exp (a * T - c * exp T)) :
    ∀ ε : Real, 0 < ε → ∀ δ : Real, 0 < δ →
      ∃ y : Real, abs (y - r) < δ ∧ abs (f y) < ε := by
  intro ε hε δ hδ
  have hcinv : (0 : Real) < 1 / c := one_div_pos_of_pos hc
  have hα : (0 : Real) ≤ a * (1 / c) := mul_nonneg ha (le_of_lt hcinv)
  obtain ⟨T, hTge, hT1, hTlt⟩ :=
    exp_beats_linear_past (α := a * (1 / c)) (β := log (C / ε) * (1 / c)) hα (1 / δ + 1)
  have hexpT : (0 : Real) < exp T := exp_pos T
  have hexpnegT : (0 : Real) < exp (-T) := exp_pos (-T)
  have hmul : exp (-T) * exp T = 1 := by
    rw [← exp_add]
    have e : -T + T = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  refine ⟨r + exp (-T), ?_, ?_⟩
  · have e : r + exp (-T) - r = exp (-T) := by mach_ring
    rw [e, abs_of_nonneg (le_of_lt hexpnegT)]
    have hlin : (1 : Real) / δ < exp T := by
      have h1 : (1 : Real) / δ < 1 / δ + 1 := by
        have v := add_lt_add_left zero_lt_one_ax (1 / δ)
        have l : (1 : Real) / δ + 0 = 1 / δ := by mach_ring
        rw [l] at v; exact v
      have h3 : T < exp T := by
        have v := one_add_le_exp T
        have w : T < 1 + T := by
          have u := add_lt_add_left zero_lt_one_ax T
          have l : T + 0 = T := by mach_ring
          have r' : T + 1 = 1 + T := by mach_ring
          rw [l, r'] at u; exact u
        exact lt_of_lt_of_le w v
      exact lt_trans_ax (lt_of_lt_of_le h1 hTge) h3
    have hinv := one_div_lt_one_div_of_lt (one_div_pos_of_pos hδ) hlin
    have e1 : (1 : Real) / (1 / δ) = δ := one_div_one_div_pos hδ
    have e2 : (1 : Real) / exp T = exp (-T) := by
      refine div_of_eq_mul (ne_of_gt hexpT) ?_
      rw [show exp T * exp (-T) = exp (-T) * exp T from by mach_ring]
      exact hmul.symm
    rw [e1, e2] at hinv
    exact hinv
  · have hb := hbound T hT1
    have hscale : a * T + log (C / ε) < c * exp T := by
      have h := mul_lt_mul_pos_left_wit hTlt hc
      have hcne : c ≠ 0 := ne_of_gt hc
      have e : c * (a * (1 / c) * T + log (C / ε) * (1 / c)) = a * T + log (C / ε) := by
        rw [show c * (a * (1 / c) * T + log (C / ε) * (1 / c))
              = (c * (1 / c)) * (a * T + log (C / ε)) from by mach_ring,
            mul_inv c hcne, one_mul_thm]
      rw [e] at h
      exact h
    have hCε : (0 : Real) < C / ε := div_pos_of_pos_pos hC hε
    have hεC : (0 : Real) < ε / C := div_pos_of_pos_pos hε hC
    have hlogsum : log (C / ε) + log (ε / C) = 0 := by
      have hprod : (C / ε) * (ε / C) = 1 := by
        rw [div_def C ε (ne_of_gt hε), div_def ε C (ne_of_gt hC),
            show C * (1 / ε) * (ε * (1 / C)) = (C * (1 / C)) * (ε * (1 / ε)) from by
              mach_mpoly [C, ε, 1 / C, 1 / ε],
            mul_inv C (ne_of_gt hC), mul_inv ε (ne_of_gt hε), one_mul_thm]
      have h := log_mul hCε hεC
      rw [hprod, log_one] at h
      exact h.symm
    have hkey : a * T - c * exp T < log (ε / C) := by
      have h := add_lt_add_left hscale (-(c * exp T) - log (C / ε))
      have l : -(c * exp T) - log (C / ε) + (a * T + log (C / ε)) = a * T - c * exp T := by
        mach_mpoly [c, exp T, log (C / ε), a, T]
      have rr : -(c * exp T) - log (C / ε) + c * exp T = -log (C / ε) := by
        mach_mpoly [c, exp T, log (C / ε)]
      rw [l, rr] at h
      have e : -log (C / ε) = log (ε / C) := by
        have v : -log (C / ε) + (log (C / ε) + log (ε / C)) = log (ε / C) := by
          mach_mpoly [log (C / ε), log (ε / C)]
        rw [hlogsum] at v
        have l : -log (C / ε) + 0 = -log (C / ε) := by mach_ring
        rw [l] at v
        exact v
      rw [e] at h
      exact h
    have hexp := exp_lt hkey
    rw [exp_log hεC] at hexp
    have hfin := lt_of_le_of_lt hb (mul_lt_mul_pos_left_wit hexp hC)
    have e : C * (ε / C) = ε := mul_div_cancel_left (ne_of_gt hC)
    rw [e] at hfin
    exact hfin

/-! ## §3 — the deflation induction

Each peel of `(x − r)` divides the value by `exp (−T)` at the evaluation point, i.e. **multiplies the
bound by `exp T`** — which the `a·T − c·exp T` form absorbs by bumping `a`. So the hypothesis is
stable under deflation and the induction is on length alone.

That stability is the whole reason the bound was stated with a free `a` rather than with a fixed
power: a shape that did not carry its own linear coefficient would need re-deriving at every peel. -/

/-- **A polynomial with super-polynomial decay at a pole is identically zero.**

Not "zero at `r`" and not "zero on the component" — identically zero, hence the germ it came from
vanishes everywhere and the level set is co-finite. -/
theorem poly_zero_of_exp_decay : ∀ (n : Nat) (p : List Real) (r a c C : Real),
    p.length ≤ n → 0 ≤ a → 0 < c → 0 < C →
    (∀ T : Real, 1 ≤ T → abs (pev p (r + exp (-T))) ≤ C * exp (a * T - c * exp T)) →
    ∀ x : Real, pev p x = 0 := by
  intro n
  induction n with
  | zero =>
      intro p r a c C hlen _ _ _ _ x
      cases p with
      | nil => rfl
      | cons _ _ => exact absurd hlen (Nat.not_succ_le_zero _)
  | succ n ih =>
      intro p r a c C hlen ha hc hC hb x
      cases hp : p with
      | nil => rfl
      | cons c0 cs =>
          subst hp
          -- the endpoint value dies
          have hr : pev (c0 :: cs) r = 0 :=
            eq_zero_of_small_nearby (pev_continuousAt (c0 :: cs) r)
              (small_nearby_of_exp_decay ha hc hC hb)
          have hdefl : ∀ y : Real,
              pev (c0 :: cs) y = (y - r) * pev (deflate r (c0 :: cs)) y := by
            intro y
            rw [pev_deflate (c0 :: cs) r y, hr]
            mach_ring
          -- the same bound for the deflated list, with `a` bumped by one
          have hbd : ∀ T : Real, 1 ≤ T →
              abs (pev (deflate r (c0 :: cs)) (r + exp (-T)))
                ≤ C * exp ((a + 1) * T - c * exp T) := by
            intro T hT
            have hexpT : (0 : Real) < exp T := exp_pos T
            have hexpn : (0 : Real) < exp (-T) := exp_pos (-T)
            have hmul : exp (-T) * exp T = 1 := by
              rw [← exp_add]
              have e : -T + T = (0 : Real) := by mach_ring
              rw [e, exp_zero]
            have hy : r + exp (-T) - r = exp (-T) := by mach_ring
            have hval := hdefl (r + exp (-T))
            rw [hy] at hval
            have habs : abs (pev (c0 :: cs) (r + exp (-T)))
                = exp (-T) * abs (pev (deflate r (c0 :: cs)) (r + exp (-T))) := by
              rw [hval, abs_mul, abs_of_nonneg (le_of_lt hexpn)]
            have hstep := hb T hT
            rw [habs] at hstep
            have hscaled := mul_le_mul_of_nonneg_right hstep (le_of_lt hexpT)
            have regroup : exp (-T) * abs (pev (deflate r (c0 :: cs)) (r + exp (-T))) * exp T
                = (exp (-T) * exp T) * abs (pev (deflate r (c0 :: cs)) (r + exp (-T))) := by
              mach_mpoly [exp (-T), exp T, abs (pev (deflate r (c0 :: cs)) (r + exp (-T)))]
            have lhs : exp (-T) * abs (pev (deflate r (c0 :: cs)) (r + exp (-T))) * exp T
                = abs (pev (deflate r (c0 :: cs)) (r + exp (-T))) := by
              rw [regroup, hmul, one_mul_thm]
            have regroupR : C * exp (a * T - c * exp T) * exp T
                = C * (exp (a * T - c * exp T) * exp T) := by
              mach_mpoly [C, exp (a * T - c * exp T), exp T]
            have expsum : a * T - c * exp T + T = (a + 1) * T - c * exp T := by
              mach_mpoly [a, T, c, exp T]
            have rhs : C * exp (a * T - c * exp T) * exp T
                = C * exp ((a + 1) * T - c * exp T) := by
              rw [regroupR, ← exp_add, expsum]
            rw [lhs, rhs] at hscaled
            exact hscaled
          have hlen' : (deflate r (c0 :: cs)).length ≤ n := by
            rw [deflate_length cs r c0]
            have h := hlen
            simp only [List.length_cons] at h
            omega
          have ha1 : (0 : Real) ≤ a + 1 := by
            have v := add_le_add_left (le_of_lt zero_lt_one_ax) a
            have l : a + 0 = a := by mach_ring
            rw [l] at v
            exact le_trans ha v
          have hzero := ih (deflate r (c0 :: cs)) r (a + 1) c C hlen' ha1 hc hC hbd x
          rw [hdefl x, hzero]
          mach_ring

/-! ## §4 — a polynomial is bounded in absolute value on a compact interval

The germ side of the wiring needs `|H|` bounded near the endpoint, where `H` is a sum of `pev`s
against powers of `exp (S x)` — and on the negative branch `0 < exp (S x) ≤ 1`, so the whole of `H`
is controlled once each coefficient polynomial is.

`continuousAt_bddAbove_Icc` bounds a continuous function **above**. `abs` needs both directions, so
it is applied twice — once to `pev L` and once to `0 - pev L`, whose continuity comes from the same
`HasDerivAt_sub` construction `PevSignOnCutFree` already uses for the mirrored intermediate value. -/

/-- **`|pev L|` is bounded on `[a, b]`.** -/
theorem pev_abs_bounded_on_Icc (L : List Real) (a b : Real) (hab : a ≤ b) :
    ∃ M : Real, ∀ x : Real, a ≤ x → x ≤ b → abs (pev L x) ≤ M := by
  obtain ⟨M₁, hM₁⟩ :=
    continuousAt_bddAbove_Icc (fun y => pev L y) a b hab (fun z _ _ => pev_continuousAt L z)
  have hcontneg : ∀ z : Real, ContinuousAt (fun w => 0 - pev L w) z := by
    intro z
    exact hasDerivAt_continuousAt
      (HasDerivAt_sub (fun _ => 0) (fun w => pev L w) 0 (pev (pderiv L) z) z
        (HasDerivAt_const 0 z) (hasDerivAt_pev L z))
  obtain ⟨M₂, hM₂⟩ :=
    continuousAt_bddAbove_Icc (fun y => 0 - pev L y) a b hab (fun z _ _ => hcontneg z)
  refine ⟨max M₁ M₂, fun x hax hxb => ?_⟩
  rcases lt_total (pev L x) 0 with hneg | hzero | hpos
  · -- `abs = -pev`, bounded by `M₂`
    have hb2 := hM₂ x hax hxb
    have e : (0 : Real) - pev L x = -pev L x := by mach_ring
    rw [e] at hb2
    rw [iv_aon hneg]
    exact le_trans hb2 (le_max_right M₁ M₂)
  · rw [hzero, abs_of_nonneg (le_refl (0 : Real))]
    have h1 := hM₁ x hax hxb
    rw [hzero] at h1
    exact le_trans h1 (le_max_left M₁ M₂)
  · rw [abs_of_nonneg (le_of_lt hpos)]
    exact le_trans (hM₁ x hax hxb) (le_max_left M₁ M₂)

/-! ## §5 — the germ side, and the wiring

On the negative branch `0 < exp (S x) ≤ 1`, so a bipolynomial evaluated along it is controlled by its
coefficients alone — there is no growth in `y` to fight. That is totalisation once more: `Fbasis`
*is* `exp` where the argument is non-positive, so the `log` half never appears and the whole germ is
bounded by §4 applied coefficient-wise.

`bipev (L :: Ls) x y = pev L x + y * bipev Ls x y` is **definitional**, so splitting the head
coefficient off needs no lemma at all. -/

/-- **`|bipev N x y|` is bounded on `[a,b] × [−1,1]`.** -/
theorem bipev_abs_bounded_on_Icc : ∀ (N : List (List Real)) (a b : Real), a ≤ b →
    ∃ M : Real, 0 ≤ M ∧ ∀ x y : Real, a ≤ x → x ≤ b → abs y ≤ 1 → abs (bipev N x y) ≤ M := by
  intro N
  induction N with
  | nil =>
      intro a b _
      refine ⟨0, le_refl 0, fun x y _ _ _ => ?_⟩
      show abs (0 : Real) ≤ 0
      rw [abs_of_nonneg (le_refl (0 : Real))]
      exact le_refl 0
  | cons L Ls ih =>
      intro a b hab
      obtain ⟨ML, hML⟩ := pev_abs_bounded_on_Icc L a b hab
      obtain ⟨MR, hMR0, hMR⟩ := ih a b hab
      refine ⟨max ML 0 + MR, ?_, fun x y hax hxb hy => ?_⟩
      · have v := add_le_add_wit (le_max_right ML 0) (le_refl MR)
        have e : (0 : Real) + MR = MR := by mach_ring
        rw [e] at v
        exact le_trans hMR0 v
      · show abs (pev L x + y * bipev Ls x y) ≤ max ML 0 + MR
        refine le_trans (abs_add _ _) ?_
        have h1 : abs (pev L x) ≤ max ML 0 :=
          le_trans (hML x hax hxb) (le_max_left ML 0)
        have h2 : abs (y * bipev Ls x y) ≤ MR := by
          rw [abs_mul]
          have hstep : abs y * abs (bipev Ls x y) ≤ 1 * abs (bipev Ls x y) :=
            mul_le_mul_of_nonneg_right hy (abs_nonneg _)
          rw [one_mul_thm] at hstep
          exact le_trans hstep (hMR x y hax hxb hy)
        exact add_le_add_wit h1 h2

/-- **The wiring: a one-query germ vanishing along a pole approach kills its head coefficient.**

Everything upstream is now discharged, so this is composition: the split is definitional, `H` is
bounded by the theorem above, the pole bound turns that into super-polynomial decay, and
`poly_zero_of_exp_decay` finishes at `a = 0` — the deflation peels supply their own. -/
theorem bipev_zero_near_pole_kills_head (N₀ : List Real) (N' : List (List Real))
    (S : Real → Real) (r c : Real) (hc : 0 < c)
    (hneg : ∀ T : Real, 1 ≤ T → S (r + exp (-T)) ≤ 0)
    (hpole : ∀ T : Real, 1 ≤ T → S (r + exp (-T)) ≤ -(c * exp T))
    (hzero : ∀ T : Real, 1 ≤ T →
      bipev (N₀ :: N') (r + exp (-T)) (exp (S (r + exp (-T)))) = 0) :
    ∀ x : Real, pev N₀ x = 0 := by
  have hr1 : r ≤ r + 1 := by
    have v := add_le_add_wit (le_refl r) (le_of_lt zero_lt_one_ax)
    have e : r + 0 = r := by mach_ring
    rw [e] at v; exact v
  obtain ⟨M, hM0, hM⟩ := bipev_abs_bounded_on_Icc N' r (r + 1) hr1
  have hCpos : (0 : Real) < M + 1 := by
    have v := add_le_add_wit hM0 (le_refl (1 : Real))
    have e : (0 : Real) + 1 = 1 := by mach_ring
    rw [e] at v
    exact lt_of_lt_of_le zero_lt_one_ax v
  refine poly_zero_of_exp_decay N₀.length N₀ r 0 c (M + 1) (Nat.le_refl _) (le_refl 0) hc hCpos ?_
  intro T hT
  have hexpn : (0 : Real) < exp (-T) := exp_pos (-T)
  have hyl : r ≤ r + exp (-T) := by
    have v := add_le_add_wit (le_refl r) (le_of_lt hexpn)
    have e : r + 0 = r := by mach_ring
    rw [e] at v; exact v
  have hnegT : -T ≤ 0 := by
    have v := add_le_add_wit (le_refl (-T)) (le_trans (le_of_lt zero_lt_one_ax) hT)
    have l : -T + 0 = -T := by mach_ring
    have rr : -T + T = (0 : Real) := by mach_ring
    rw [l, rr] at v; exact v
  have hyr : r + exp (-T) ≤ r + 1 := by
    refine add_le_add_left ?_ r
    have h := exp_monotone hnegT
    rw [exp_zero] at h
    exact h
  -- the head coefficient, definitionally
  have hsplit : pev N₀ (r + exp (-T))
      + exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T)))) = 0 :=
    hzero T hT
  have hval : pev N₀ (r + exp (-T))
      = -(exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T))))) := by
    have v : pev N₀ (r + exp (-T))
        = (pev N₀ (r + exp (-T))
            + exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T)))))
          + -(exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T))))) := by
      mach_mpoly [pev N₀ (r + exp (-T)),
        exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T))))]
    rw [hsplit] at v
    have e : (0 : Real)
        + -(exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T)))))
        = -(exp (S (r + exp (-T))) * bipev N' (r + exp (-T)) (exp (S (r + exp (-T))))) := by
      mach_ring
    rw [e] at v; exact v
  -- `|head| = exp (S ·) · |H|`
  have habs : abs (pev N₀ (r + exp (-T)))
      = exp (S (r + exp (-T))) * abs (bipev N' (r + exp (-T)) (exp (S (r + exp (-T))))) := by
    rw [hval, abs_neg, abs_mul, abs_of_nonneg (le_of_lt (exp_pos (S (r + exp (-T)))))]
  -- `|H| ≤ M`, since `exp (S ·) ≤ 1` on the negative branch
  have hy1 : abs (exp (S (r + exp (-T)))) ≤ 1 := by
    rw [abs_of_nonneg (le_of_lt (exp_pos (S (r + exp (-T)))))]
    exact exp_le_one (hneg T hT)
  have hHbound := hM (r + exp (-T)) (exp (S (r + exp (-T)))) hyl hyr hy1
  -- assemble
  rw [habs]
  refine le_trans (mul_le_mul_of_nonneg_left hHbound
      (le_of_lt (exp_pos (S (r + exp (-T)))))) ?_
  refine le_trans (mul_le_mul_of_nonneg_right (exp_monotone (hpole T hT)) hM0) ?_
  have e : (M + 1) * exp (0 * T - c * exp T) = exp (-(c * exp T)) * M
      + exp (-(c * exp T)) := by
    rw [show (0 : Real) * T - c * exp T = -(c * exp T) from by mach_ring]
    mach_mpoly [M, exp (-(c * exp T))]
  rw [e]
  have v := add_le_add_wit (le_refl (exp (-(c * exp T)) * M))
    (le_of_lt (exp_pos (-(c * exp T))))
  have l : exp (-(c * exp T)) * M + 0 = exp (-(c * exp T)) * M := by mach_ring
  rw [l] at v
  exact v

end MachLib
