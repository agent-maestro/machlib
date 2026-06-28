import MachLib.OperatorBasisSound
import MachLib.ErrorAlgebraTrans

/-!
# Operator-basis soundness, extended past `{+,×}` — the bounded-Lipschitz class

`OperatorBasisSound` proved the certifier's soundness for the nonneg `{+,×}` core
(one meta-theorem, every kernel). This pushes past it, into the *bounded-Lipschitz*
transcendental class — `sin`, `cos`, and `exp(−·)` over a nonneg core (the `e^{−S}`
Gaussian shape).

`sin_grow` and `cos_grow` are the **same** proof up to two facts about the operator
`f`: it is bounded (`|f| ≤ 1`) and 1-Lipschitz (`|f a − f b| ≤ |a − b|`). So they are
one rule, `bdd_lip_grow`, for the whole class — which also contains `exp(−S)` for
`S ≥ 0` (`exp(−S) ≤ 1`, slope `−exp(−S) ∈ [−1,0)`), the most common transcendental
skeleton in the operator-basis study (5 unrelated domains). A bounded-Lipschitz
operator turns argument error `E` into output error `E + w` (absolute, not
amplified). Folding that over the arithmetic core (`opTree_fwd_error` supplies the
inner `E`) gives `texpr_sound`: **one meta-theorem covering every `{sin, cos,
exp(−·)}`-stack over a nonneg `{+,×}` arithmetic core** — extending the proven
pipeline well past `{+,×}` into the trigonometric and `e^{−S}` shapes.

`exp` in its *amplifying* régime (general arguments, `exp_grow`) and
arithmetic-*of*-transcendentals are the named next classes. `sorryAx`-free.
-/

namespace MachLib.Real

/-! ## the bounded-Lipschitz operator rule (one rule for the whole class) -/

/-- **Bounded-Lipschitz forward-error rule.** For any operator `f` that is bounded
(`|f xc| ≤ 1`) and 1-Lipschitz at the evaluation points, one rounded `f` of an
argument with absolute error `≤ E` lands within `w + E` of `f xe` — absolute, not
amplified. Subsumes `sin_grow`/`cos_grow`. -/
theorem bdd_lip_grow {f : Real → Real} {w E xc xe p : Real}
    (hw0 : 0 ≤ w) (hbdd : abs (f xc) ≤ 1)
    (hlip : abs (f xc - f xe) ≤ abs (xc - xe)) (harg : abs (xc - xe) ≤ E)
    (hp : RoundsW w p (f xc)) :
    abs (p - f xe) ≤ w + E := by
  have hround1 : abs (p - f xc) ≤ w := by
    have h := mul_le_mul_of_nonneg_left hbdd hw0
    rw [show w * 1 = w from by mach_ring] at h
    exact le_trans (roundsW_abs hp) h
  have hprop : abs (f xc - f xe) ≤ E := le_trans hlip harg
  rw [et_split3 p (f xc) (f xe)]
  exact le_trans (abs_add _ _) (add_le_add_both hround1 hprop)

/-! ## `exp(−·)` is bounded-Lipschitz on the nonnegatives — the `e^{−S}` shape

`exp` in general *amplifies* (`exp_grow`). But on the **nonnegatives** `exp(−S)` is
bounded by `1` and 1-Lipschitz (`exp(−·)` has slope `−exp(−S) ∈ [−1, 0)` there), so
the `e^{−S}` Gaussian shell — the most common transcendental skeleton in the
operator-basis study (5 unrelated domains) — joins the bounded-Lipschitz class and
folds through `bdd_lip_grow` with the *clean* `w + E` bound (tighter than the
amplifying route). -/

/-- `0 ≤ x → |exp(−x)| ≤ 1`. -/
theorem exp_neg_le_one {x : Real} (hx : 0 ≤ x) : abs (exp (-x)) ≤ 1 := by
  rw [abs_of_nonneg (le_of_lt (exp_pos (-x)))]
  have hnx : -x ≤ 0 := by have h := neg_le_neg hx; rwa [neg_zero] at h
  have h := exp_monotone hnx; rwa [exp_zero] at h

/-- One-sided step: for `0 ≤ a ≤ b`, `exp(−a) − exp(−b) ≤ b − a`. The slope bound
`1 − exp(−t) ≤ t` (`one_add_le_exp`) times `exp(−a) ≤ 1`. -/
theorem exp_neg_sub_le {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    exp (-a) - exp (-b) ≤ b - a := by
  have hba : 0 ≤ b - a := sub_nonneg_of_le hab
  have hfac : exp (-a) - exp (-b) = exp (-a) * (1 - exp (-(b - a))) := by
    rw [show exp (-a) * (1 - exp (-(b - a)))
          = exp (-a) - exp (-a) * exp (-(b - a)) from by mach_ring,
        ← exp_add, show (-a) + (-(b - a)) = -b from by mach_ring]
  have hexp_le1 : exp (-(b - a)) ≤ 1 := by
    have hnn : -(b - a) ≤ 0 := by have h := neg_le_neg hba; rwa [neg_zero] at h
    have h := exp_monotone hnn; rwa [exp_zero] at h
  have h0 : 0 ≤ 1 - exp (-(b - a)) := sub_nonneg_of_le hexp_le1
  have h1 : 1 - exp (-(b - a)) ≤ b - a := by
    have h2 : 1 - (b - a) ≤ exp (-(b - a)) := by
      rw [show (1 : Real) - (b - a) = 1 + (-(b - a)) from by mach_ring]; exact one_add_le_exp _
    have h3 := sub_le_sub_left h2 1
    rwa [show (1 : Real) - (1 - (b - a)) = b - a from by mach_ring] at h3
  have hea_le1 : exp (-a) ≤ 1 := by
    have h := exp_neg_le_one ha; rwa [abs_of_nonneg (le_of_lt (exp_pos (-a)))] at h
  rw [hfac]
  exact le_trans (mul_le_mul_of_nonneg_right hea_le1 h0)
                 (le_trans (le_of_eq (one_mul_thm (1 - exp (-(b - a))))) h1)

/-- **`exp(−·)` is 1-Lipschitz on the nonnegatives.** -/
theorem exp_neg_lipschitz {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    abs (exp (-a) - exp (-b)) ≤ abs (a - b) := by
  have htot : a ≤ b ∨ b ≤ a := by
    rcases lt_total a b with h | h | h
    · exact Or.inl (le_of_lt h)
    · exact Or.inl (le_of_eq h)
    · exact Or.inr (le_of_lt h)
  rcases htot with hab | hba
  · have hge : exp (-b) ≤ exp (-a) := exp_monotone (neg_le_neg hab)
    have hababs : abs (a - b) = b - a := by
      rw [show a - b = -(b - a) from by mach_ring, abs_neg, abs_of_nonneg (sub_nonneg_of_le hab)]
    rw [abs_of_nonneg (sub_nonneg_of_le hge), hababs]
    exact exp_neg_sub_le ha hab
  · have hge : exp (-a) ≤ exp (-b) := exp_monotone (neg_le_neg hba)
    have hlhsabs : abs (exp (-a) - exp (-b)) = exp (-b) - exp (-a) := by
      rw [show exp (-a) - exp (-b) = -(exp (-b) - exp (-a)) from by mach_ring, abs_neg,
          abs_of_nonneg (sub_nonneg_of_le hge)]
    rw [hlhsabs, abs_of_nonneg (sub_nonneg_of_le hba)]
    exact exp_neg_sub_le hb hba

/-- The computed value of a nonneg `{+,×}` evaluation is itself nonneg — needed to
land an `exp(−·)` argument in the nonnegative domain. (Lower `Renc` bound: `0 ≤
(1−w)^d·exact ≤ v`.) -/
theorem roundedEval_nonneg {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : OpTree} {v : Real} (hev : RoundedEval w t v) (hnn : t.Nonneg) : 0 ≤ v := by
  obtain ⟨hlo, _⟩ := renc_sound hw0 hw1 hev hnn
  exact le_trans (mul_nonneg (npow_nonneg (sub_nonneg_of_le hw1) t.depth)
    (OpTree.exact_nonneg hnn)) hlo

/-! ## the fold: bounded-Lipschitz transcendentals over the `{+,×}` core -/

/-- A bounded-Lipschitz transcendental stack (`sin`/`cos`, and `exp(−·)` over a
nonneg core) over a nonneg `{+,×}` arithmetic core (`OpTree`). (Constructors
`sinOp`/`cosOp` to avoid colliding with the trig functions `sin`/`cos`.) -/
inductive TExpr where
  | arith       (t : OpTree)
  | sinOp       (a : TExpr)
  | cosOp       (a : TExpr)
  | expNegArith (t : OpTree)        -- `exp(−S)`, `S` a nonneg `{+,×}` core (the `e^{−S}` shape)

/-- The exact value. -/
noncomputable def TExpr.texact : TExpr → Real
  | .arith t       => t.exact
  | .sinOp a       => sin (TExpr.texact a)
  | .cosOp a       => cos (TExpr.texact a)
  | .expNegArith t => exp (-(t.exact))
  termination_by structural t => t

/-- The forward-error bound: the arithmetic core's `((1+w)^depth − 1)·exact`, plus
`+ w` per bounded-Lipschitz wrapper (`w + E`, matching `bdd_lip_grow`). -/
noncomputable def TExpr.terr (w : Real) : TExpr → Real
  | .arith t       => (npow t.depth (1 + w) - 1) * t.exact
  | .sinOp a       => w + TExpr.terr w a
  | .cosOp a       => w + TExpr.terr w a
  | .expNegArith t => w + (npow t.depth (1 + w) - 1) * t.exact
  termination_by structural t => t

/-- Validity: every arithmetic core is nonneg. -/
def TExpr.Valid : TExpr → Prop
  | .arith t       => t.Nonneg
  | .sinOp a       => TExpr.Valid a
  | .cosOp a       => TExpr.Valid a
  | .expNegArith t => t.Nonneg
  termination_by structural t => t

/-- Any per-node-rounded evaluation of the stack. -/
inductive TRoundedEval (w : Real) : TExpr → Real → Prop where
  | arith {t : OpTree} {v : Real} (h : RoundedEval w t v) : TRoundedEval w (.arith t) v
  | sinOp {a : TExpr} {va p : Real}
      (ha : TRoundedEval w a va) (hp : RoundsW w p (sin va)) : TRoundedEval w (.sinOp a) p
  | cosOp {a : TExpr} {va p : Real}
      (ha : TRoundedEval w a va) (hp : RoundsW w p (cos va)) : TRoundedEval w (.cosOp a) p
  | expNegArith {t : OpTree} {va p : Real}
      (hev : RoundedEval w t va) (hp : RoundsW w p (exp (-va))) :
      TRoundedEval w (.expNegArith t) p

/-- **The extended meta-theorem.** Every `{sin, cos, exp(−·)}`-stack over a nonneg
`{+,×}` arithmetic core has forward error `≤ t.terr w` — folding `opTree_fwd_error`
at the core and `bdd_lip_grow` at each transcendental. One theorem, every such
kernel. -/
theorem texpr_sound {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : TExpr} {v : Real} (h : TRoundedEval w t v) :
    t.Valid → abs (v - t.texact) ≤ t.terr w := by
  induction h with
  | arith hre => exact fun hv => opTree_fwd_error hw0 hw1 hre hv
  | @sinOp a va p ha hp iha =>
      exact fun hv => bdd_lip_grow hw0 (abs_sin_le_one va) (sin_lipschitz va a.texact) (iha hv) hp
  | @cosOp a va p ha hp iha =>
      exact fun hv => bdd_lip_grow hw0 (abs_cos_le_one va) (cos_lipschitz va a.texact) (iha hv) hp
  | @expNegArith t va p hev hp =>
      intro hv
      exact bdd_lip_grow (f := fun z => exp (-z)) hw0
        (exp_neg_le_one (roundedEval_nonneg hw0 hw1 hev hv))
        (exp_neg_lipschitz (roundedEval_nonneg hw0 hw1 hev hv) (OpTree.exact_nonneg hv))
        (opTree_fwd_error hw0 hw1 hev hv) hp

/-- `sin(x²+y²)` (a trig-of-arithmetic kernel) as an instance: forward error
`≤ w + ((1+w)²−1)·(x²+y²)`, assembled by the meta-theorem with no hand proof —
the `+ w` of the `sin` rounding over the arithmetic core's `((1+w)²−1)·(x²+y²)`. -/
theorem sin_lengthsq2_via_meta {w x y px py s p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py)) (hp : RoundsW w p (sin s)) :
    abs (p - sin (x * x + y * y)) ≤ w + (npow 2 (1 + w) - 1) * (x * x + y * y) :=
  texpr_sound hw0 hw1
    (TRoundedEval.sinOp (a := .arith (.add (.rleaf (x * x)) (.rleaf (y * y))))
      (TRoundedEval.arith (RoundedEval.add (RoundedEval.rleaf hpx) (RoundedEval.rleaf hpy) hs)) hp)
    ⟨mul_self_nonneg x, mul_self_nonneg y⟩

/-- **The Gaussian `exp(−(x²+y²))`** (the `e^{−S}` shell) as a one-line instance —
forward error `≤ w + ((1+w)²−1)·(x²+y²)`, the *bounded* treatment of `exp` (cf.
`HybridError.gaussian2_fwd`'s amplifying route). Shows the canonical transcendental
shape folding through the *same* meta-theorem as `sin`/`cos`. -/
theorem gaussian2_via_meta {w x y px py s p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py)) (hp : RoundsW w p (exp (-s))) :
    abs (p - exp (-(x * x + y * y))) ≤ w + (npow 2 (1 + w) - 1) * (x * x + y * y) :=
  texpr_sound hw0 hw1
    (TRoundedEval.expNegArith (t := .add (.rleaf (x * x)) (.rleaf (y * y)))
      (RoundedEval.add (RoundedEval.rleaf hpx) (RoundedEval.rleaf hpy) hs) hp)
    ⟨mul_self_nonneg x, mul_self_nonneg y⟩

end MachLib.Real
