import MachLib.PevRoots
import MachLib.PevSignOnCutFree
import MachLib.EMLDepth2InvX

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

end MachLib
