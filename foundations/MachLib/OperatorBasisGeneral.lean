import MachLib.OperatorBasisTrans
import MachLib.FixedPoint

/-!
# The general absolute-error meta-theorem — every operator, freely mixed

`OperatorBasisSound` proved the tight *relative* (`Renc`) fold for the nonneg `{+,×}`
core; `OperatorBasisTrans` folded the *bounded-Lipschitz* transcendentals (`sin`,
`cos`, `e^{−S}`) as a stack over one arithmetic core. Both leave two classes open:
the **amplifying** `exp` (general arguments) and **arithmetic-*of*-transcendentals**
(a transcendental output flowing back into `+`/`×`, e.g. `1 + cos²θ`).

This file closes both at once with a single, more general currency: a forward-error
certificate `AErr M E v ve` carrying **both** a magnitude bound (`|ve| ≤ M`) and the
absolute error (`|v − ve| ≤ E`). Magnitude tracking is exactly what the open classes
need — `exp`'s output error scales with `exp(M_arg)` (so it must know its argument's
magnitude), and `×`/`+` of transcendentals need magnitude bounds on their operands.

Every operator gets an `AErr` propagation rule, and `aexpr_sound` folds them over a
free `{leaf, +, ×, neg, exp, sin, cos}` expression tree. This is *more general* than
the Renc fold (handles the full mix) but *looser* on pure arithmetic (absolute,
magnitude-based, vs the tight relative `(1+w)^d`) — the two tracks are complementary:
prefer `renc_sound` where the kernel is pure nonneg `{+,×}`, this where it mixes
transcendentals. `sorryAx`-free; division (needs a denominator lower bound) is the
remaining operator class.
-/

namespace MachLib.Real

/-! ## the certificate and its basic facts -/

/-- Absolute forward-error certificate: the exact value has magnitude `≤ M` and the
computed value is within `E` of it. -/
def AErr (M E v ve : Real) : Prop := abs ve ≤ M ∧ abs (v - ve) ≤ E

theorem AErr.mag {M E v ve : Real} (h : AErr M E v ve) : abs ve ≤ M := h.1
theorem AErr.err {M E v ve : Real} (h : AErr M E v ve) : abs (v - ve) ≤ E := h.2

/-- The *computed* value is bounded by `M + E` (triangle `|v| ≤ |ve| + |v − ve|`). -/
theorem AErr.val_bound {M E v ve : Real} (h : AErr M E v ve) : abs v ≤ M + E := by
  have key : abs v ≤ abs ve + abs (v - ve) := by
    have h2 := abs_add ve (v - ve)
    rwa [show ve + (v - ve) = v from by mach_ring] at h2
  exact le_trans key (add_le_add_both h.1 h.2)

/-! ## the per-operator rules -/

/-- Exact leaf (an input, no rounding). -/
theorem aerr_leaf (ve : Real) : AErr (abs ve) 0 ve ve := by
  refine ⟨le_refl _, ?_⟩
  rw [show ve - ve = 0 from by mach_ring]
  exact le_of_eq abs_zero

/-- A single rounding of a value. -/
theorem aerr_round {w p ve : Real} (hp : RoundsW w p ve) : AErr (abs ve) (w * abs ve) p ve :=
  ⟨le_refl _, roundsW_abs hp⟩

/-- Negation: magnitude and error unchanged. -/
theorem aerr_neg {M E v ve : Real} (h : AErr M E v ve) : AErr M E (-v) (-ve) := by
  refine ⟨?_, ?_⟩
  · rw [abs_neg]; exact h.1
  · rw [show (-v) - (-ve) = -(v - ve) from by mach_ring, abs_neg]; exact h.2

/-- Sum: magnitudes add; error is `Ex + Ey` plus the sum's own rounding `w·(|vx|+|vy|)`
bounded through the magnitude+error of each operand. -/
theorem aerr_add {w Mx Ex vx xe My Ey vy ye p : Real} (hw0 : 0 ≤ w)
    (hx : AErr Mx Ex vx xe) (hy : AErr My Ey vy ye) (hp : RoundsW w p (vx + vy)) :
    AErr (Mx + My) (Ex + Ey + w * (Mx + Ex + My + Ey)) p (xe + ye) := by
  refine ⟨le_trans (abs_add xe ye) (add_le_add_both hx.1 hy.1), ?_⟩
  have hround : abs (p - (vx + vy)) ≤ w * (Mx + Ex + My + Ey) := by
    have h2 : abs (vx + vy) ≤ Mx + Ex + My + Ey :=
      le_trans (abs_add vx vy)
        (le_trans (add_le_add_both hx.val_bound hy.val_bound) (le_of_eq (by mach_ring)))
    exact le_trans (roundsW_abs hp) (mul_le_mul_of_nonneg_left h2 hw0)
  have hprop : abs ((vx + vy) - (xe + ye)) ≤ Ex + Ey := by
    rw [show (vx + vy) - (xe + ye) = (vx - xe) + (vy - ye) from by mach_ring]
    exact le_trans (abs_add (vx - xe) (vy - ye)) (add_le_add_both hx.2 hy.2)
  rw [et_split3 p (vx + vy) (xe + ye)]
  exact le_trans (abs_add _ _)
    (le_trans (add_le_add_both hround hprop) (le_of_eq (by mach_ring)))

/-- Product: magnitudes multiply; error is the bilinear `(|vx|·Ey + |ye|·Ex)` plus the
product's own rounding, each factor bounded by magnitude+error. -/
theorem aerr_mul {w Mx Ex vx xe My Ey vy ye p : Real} (hw0 : 0 ≤ w)
    (hx : AErr Mx Ex vx xe) (hy : AErr My Ey vy ye) (hp : RoundsW w p (vx * vy)) :
    AErr (Mx * My) ((Mx + Ex) * Ey + My * Ex + w * ((Mx + Ex) * (My + Ey))) p (xe * ye) := by
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg xe) hx.1
  have hMy0 : 0 ≤ My := le_trans (abs_nonneg ye) hy.1
  have hMxEx0 : 0 ≤ Mx + Ex := le_trans (abs_nonneg vx) hx.val_bound
  refine ⟨?_, ?_⟩
  · rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hx.1 (abs_nonneg ye))
                   (mul_le_mul_of_nonneg_left hy.1 hMx0)
  · have hround : abs (p - vx * vy) ≤ w * ((Mx + Ex) * (My + Ey)) := by
      have h2 : abs (vx * vy) ≤ (Mx + Ex) * (My + Ey) := by
        rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hx.val_bound (abs_nonneg vy))
                       (mul_le_mul_of_nonneg_left hy.val_bound hMxEx0)
      exact le_trans (roundsW_abs hp) (mul_le_mul_of_nonneg_left h2 hw0)
    have hprop : abs (vx * vy - xe * ye) ≤ (Mx + Ex) * Ey + My * Ex := by
      rw [show vx * vy - xe * ye = vx * (vy - ye) + ye * (vx - xe) from by mach_ring]
      have hA : abs (vx * (vy - ye)) ≤ (Mx + Ex) * Ey := by
        rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hx.val_bound (abs_nonneg (vy - ye)))
                       (mul_le_mul_of_nonneg_left hy.2 hMxEx0)
      have hB : abs (ye * (vx - xe)) ≤ My * Ex := by
        rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hy.1 (abs_nonneg (vx - xe)))
                       (mul_le_mul_of_nonneg_left hx.2 hMy0)
      exact le_trans (abs_add _ _) (add_le_add_both hA hB)
    rw [et_split3 p (vx * vy) (xe * ye)]
    exact le_trans (abs_add _ _)
      (le_trans (add_le_add_both hround hprop) (le_of_eq (by mach_ring)))

/-- **Amplifying `exp`** (general argument). Output magnitude `exp M`; error scales by
`exp M` (the condition number) — `exp_grow`'s relative factor times the magnitude
bound `exp ve ≤ exp M`. This is the case the bounded-Lipschitz fold could not reach. -/
theorem aerr_exp {w M E v ve p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (h : AErr M E v ve) (hp : RoundsW w p (exp v)) :
    AErr (exp M) (exp M * (exp E * (1 + w) - 1)) p (exp ve) := by
  have hE0 : 0 ≤ E := le_trans (abs_nonneg (v - ve)) h.2
  have hpre : exp ve ≤ exp M := exp_monotone (le_trans (le_abs_self ve) h.1)
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (le_of_lt (exp_pos ve))]; exact hpre
  · have hfac0 : 0 ≤ exp E * (1 + w) - 1 := by
      have he1 : 1 ≤ exp E := by have h := exp_monotone hE0; rwa [exp_zero] at h
      have hw1' : (1 : Real) ≤ 1 + w := le_add_of_nonneg_right hw0
      have hstep1 : (1 : Real) ≤ exp E :=
        le_trans (le_of_eq (one_mul_thm 1).symm)
          (le_trans (mul_le_mul_of_nonneg_right he1 (le_of_lt zero_lt_one_ax))
                    (le_of_eq (by mach_ring)))
      have hprod : (1 : Real) ≤ exp E * (1 + w) :=
        le_trans hstep1 (le_trans (le_of_eq (mul_one_ax (exp E)).symm)
          (mul_le_mul_of_nonneg_left hw1' (le_of_lt (exp_pos E))))
      exact sub_nonneg_of_le hprod
    exact le_trans (exp_grow hw0 hw1 hE0 h.2 hp) (mul_le_mul_of_nonneg_right hpre hfac0)

/-- **Relative (upper-bound-aware) `exp` rule.** When the argument is bounded *above* by `U`
(`ve ≤ U`), the magnitude is the **tight** `exp U` and the error is scaled by `exp U` — not
the symmetric `exp |arg|` of `aerr_exp`. For an argument that is non-positive (e.g.
`exp(−x²)`, take `U = 0`) this gives magnitude `exp 0 = 1` instead of the loose `exp |arg|`,
killing the amplifying-family looseness the tightness probe measured. The proof is `aerr_exp`'s,
with the magnitude read off a one-sided `ve ≤ U` rather than `|ve| ≤ M` (`exp` is monotone, so
`exp ve ≤ exp U`). -/
theorem aerr_exp_upper {w M E v ve U p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (h : AErr M E v ve) (hU : ve ≤ U) (hp : RoundsW w p (exp v)) :
    AErr (exp U) (exp U * (exp E * (1 + w) - 1)) p (exp ve) := by
  have hE0 : 0 ≤ E := le_trans (abs_nonneg (v - ve)) h.2
  have hpre : exp ve ≤ exp U := exp_monotone hU
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (le_of_lt (exp_pos ve))]; exact hpre
  · have hfac0 : 0 ≤ exp E * (1 + w) - 1 := by
      have he1 : 1 ≤ exp E := by have h := exp_monotone hE0; rwa [exp_zero] at h
      have hw1' : (1 : Real) ≤ 1 + w := le_add_of_nonneg_right hw0
      have hstep1 : (1 : Real) ≤ exp E :=
        le_trans (le_of_eq (one_mul_thm 1).symm)
          (le_trans (mul_le_mul_of_nonneg_right he1 (le_of_lt zero_lt_one_ax))
                    (le_of_eq (by mach_ring)))
      have hprod : (1 : Real) ≤ exp E * (1 + w) :=
        le_trans hstep1 (le_trans (le_of_eq (mul_one_ax (exp E)).symm)
          (mul_le_mul_of_nonneg_left hw1' (le_of_lt (exp_pos E))))
      exact sub_nonneg_of_le hprod
    exact le_trans (exp_grow hw0 hw1 hE0 h.2 hp) (mul_le_mul_of_nonneg_right hpre hfac0)

/-- `sin`: bounded magnitude `1`, error `E + w` (bounded-Lipschitz). -/
theorem aerr_sin {w M E v ve p : Real} (hw0 : 0 ≤ w)
    (h : AErr M E v ve) (hp : RoundsW w p (sin v)) : AErr 1 (E + w) p (sin ve) :=
  ⟨abs_sin_le_one ve, le_trans (sin_grow hw0 h.2 hp) (le_of_eq (by mach_ring))⟩

/-- `cos`: bounded magnitude `1`, error `E + w`. -/
theorem aerr_cos {w M E v ve p : Real} (hw0 : 0 ≤ w)
    (h : AErr M E v ve) (hp : RoundsW w p (cos v)) : AErr 1 (E + w) p (cos ve) :=
  ⟨abs_cos_le_one ve, le_trans (cos_grow hw0 h.2 hp) (le_of_eq (by mach_ring))⟩

/-- `||a| − |b|| ≤ |a − b|` — `abs` is 1-Lipschitz (reverse triangle, from `abs_add`). -/
theorem abs_abs_sub_le (a b : Real) : abs (abs a - abs b) ≤ abs (a - b) := by
  have key : ∀ x y : Real, abs x - abs y ≤ abs (x - y) := by
    intro x y
    have h := abs_add (x - y) y
    rw [show (x - y) + y = x from by mach_ring] at h
    refine le_of_sub_nonneg ?_
    rw [show abs (x - y) - (abs x - abs y) = abs (x - y) + abs y - abs x from by
          mach_mpoly [abs (x - y), abs y, abs x]]
    exact sub_nonneg_of_le h
  apply abs_le_of
  · exact key a b
  · rw [show -(abs a - abs b) = abs b - abs a from by mach_ring, abs_sub_comm a b]
    exact key b a

/-- `abs` (`|·|`): exact (no rounding) and 1-Lipschitz, so it *preserves* both magnitude
and error — `|x|` has the same `M` (`|ve| ≤ M ⇒ ||ve|| = |ve| ≤ M`) and the same `E`. -/
theorem aerr_abs {M E v ve : Real} (h : AErr M E v ve) : AErr M E (abs v) (abs ve) :=
  ⟨by rw [abs_of_nonneg (abs_nonneg ve)]; exact h.1, le_trans (abs_abs_sub_le v ve) h.2⟩

/-- `clamp` (to `[lo, hi]`, `lo ≤ hi`): magnitude bounded by the range `max |lo| |hi|`;
error *preserved* (`E`, not `E + w`) — `min`/`max` are exact (no rounding) and `clamp`
is 1-Lipschitz, so it propagates the argument error unchanged and cannot amplify. -/
theorem aerr_clamp {M E v ve lo hi : Real} (hlohi : lo ≤ hi) (h : AErr M E v ve) :
    AErr (max (abs lo) (abs hi)) E (clamp v lo hi) (clamp ve lo hi) := by
  refine ⟨?_, le_trans (clamp_lipschitz v ve lo hi) h.2⟩
  apply abs_le_of
  · exact le_trans (clamp_le_hi ve lo hi) (le_trans (le_abs_self hi) (le_max_right _ _))
  · exact le_trans (neg_le_neg (lo_le_clamp ve lo hi hlohi))
      (le_trans (neg_le_abs lo) (le_max_left _ _))

/-- **Robust conditional** (`if c then · else ·`): given a forward-error certificate for
*each* branch, the selected value is certified by the *max* of the two branches'
magnitude and error bounds. The `Bool c` is the branch the computation took; the *exact*
value selects with the **same** `c` — that is exactly the **branch-robustness**
hypothesis (the rounding did not flip which side of the test was taken). Under it, the
conditional cannot amplify error: whichever branch is live, its own certificate carries.
This is the one composition the unified tree could not absorb structurally — its exact
value is branch-dependent — so it enters as a Bool-indexed *field* (`iteO`), the analogue
of `clamp`'s `lo`/`hi`. (A *non-robust* conditional, where rounding flips the test near
the boundary, is genuinely off-basis: the two branches can disagree by `Ma + Mb`, not
`max Ea Eb`.) -/
theorem aerr_ite {Ma Ea va vea Mb Eb vb veb : Real} (c : Bool)
    (ha : AErr Ma Ea va vea) (hb : AErr Mb Eb vb veb) :
    AErr (max Ma Mb) (max Ea Eb) (cond c va vb) (cond c vea veb) := by
  cases c
  · show AErr (max Ma Mb) (max Ea Eb) vb veb
    exact ⟨le_trans hb.1 (le_max_right _ _), le_trans hb.2 (le_max_right _ _)⟩
  · show AErr (max Ma Mb) (max Ea Eb) va vea
    exact ⟨le_trans ha.1 (le_max_left _ _), le_trans ha.2 (le_max_left _ _)⟩

/-! ## the general fold over a free `{leaf, +, ×, neg, exp, sin, cos}` tree -/

/-- A free expression over the full operator set. (Constructors `expO`/`sinO`/`cosO`
to avoid colliding with the functions `exp`/`sin`/`cos`.) -/
inductive AExpr where
  | leaf  (ve : Real)        -- exact input
  | rleaf (ve : Real)        -- a single rounding
  | add   (a b : AExpr)
  | mul   (a b : AExpr)
  | neg   (a : AExpr)
  | expO  (a : AExpr)
  | sinO  (a : AExpr)
  | cosO  (a : AExpr)

/-- The exact value. -/
noncomputable def AExpr.exact : AExpr → Real
  | .leaf ve  => ve
  | .rleaf ve => ve
  | .add a b  => AExpr.exact a + AExpr.exact b
  | .mul a b  => AExpr.exact a * AExpr.exact b
  | .neg a    => -(AExpr.exact a)
  | .expO a   => exp (AExpr.exact a)
  | .sinO a   => sin (AExpr.exact a)
  | .cosO a   => cos (AExpr.exact a)
  termination_by structural t => t

/-- Magnitude bound on the exact value: `|exact| ≤ Mbound`. -/
noncomputable def AExpr.Mbound : AExpr → Real
  | .leaf ve  => abs ve
  | .rleaf ve => abs ve
  | .add a b  => AExpr.Mbound a + AExpr.Mbound b
  | .mul a b  => AExpr.Mbound a * AExpr.Mbound b
  | .neg a    => AExpr.Mbound a
  | .expO a   => exp (AExpr.Mbound a)
  | .sinO _   => 1
  | .cosO _   => 1
  termination_by structural t => t

/-- Absolute forward-error bound (folds the per-operator `AErr` error terms). -/
noncomputable def AExpr.Ebound (w : Real) : AExpr → Real
  | .leaf _   => 0
  | .rleaf ve => w * abs ve
  | .add a b  => AExpr.Ebound w a + AExpr.Ebound w b
                 + w * (AExpr.Mbound a + AExpr.Ebound w a + AExpr.Mbound b + AExpr.Ebound w b)
  | .mul a b  => (AExpr.Mbound a + AExpr.Ebound w a) * AExpr.Ebound w b
                 + AExpr.Mbound b * AExpr.Ebound w a
                 + w * ((AExpr.Mbound a + AExpr.Ebound w a) * (AExpr.Mbound b + AExpr.Ebound w b))
  | .neg a    => AExpr.Ebound w a
  | .expO a   => exp (AExpr.Mbound a) * (exp (AExpr.Ebound w a) * (1 + w) - 1)
  | .sinO a   => AExpr.Ebound w a + w
  | .cosO a   => AExpr.Ebound w a + w
  termination_by structural t => t

/-- Any per-node-rounded evaluation. `neg` is exact (sign flip, no rounding). -/
inductive ARoundedEval (w : Real) : AExpr → Real → Prop where
  | leaf  (ve : Real) : ARoundedEval w (.leaf ve) ve
  | rleaf {ve p : Real} (hp : RoundsW w p ve) : ARoundedEval w (.rleaf ve) p
  | add   {a b : AExpr} {va vb p : Real} (ha : ARoundedEval w a va) (hb : ARoundedEval w b vb)
      (hp : RoundsW w p (va + vb)) : ARoundedEval w (.add a b) p
  | mul   {a b : AExpr} {va vb p : Real} (ha : ARoundedEval w a va) (hb : ARoundedEval w b vb)
      (hp : RoundsW w p (va * vb)) : ARoundedEval w (.mul a b) p
  | neg   {a : AExpr} {va : Real} (ha : ARoundedEval w a va) : ARoundedEval w (.neg a) (-va)
  | expO  {a : AExpr} {va p : Real} (ha : ARoundedEval w a va)
      (hp : RoundsW w p (exp va)) : ARoundedEval w (.expO a) p
  | sinO  {a : AExpr} {va p : Real} (ha : ARoundedEval w a va)
      (hp : RoundsW w p (sin va)) : ARoundedEval w (.sinO a) p
  | cosO  {a : AExpr} {va p : Real} (ha : ARoundedEval w a va)
      (hp : RoundsW w p (cos va)) : ARoundedEval w (.cosO a) p

/-- **The general meta-theorem.** Any per-node-rounded evaluation of *any*
`{leaf, +, ×, neg, exp, sin, cos}` expression carries the magnitude+error certificate
`AErr Mbound Ebound` — one structural induction folding the eight per-operator rules.
Covers the amplifying-`exp` régime and arithmetic-of-transcendentals (e.g. `cos²θ` is
`mul (cosO …) (cosO …)`), the classes the relative/bounded folds could not reach. -/
theorem aexpr_sound {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : AExpr} {v : Real} (h : ARoundedEval w t v) :
    AErr t.Mbound (t.Ebound w) v t.exact := by
  induction h with
  | leaf ve            => exact aerr_leaf ve
  | rleaf hp           => exact aerr_round hp
  | add _ _ hp iha ihb => exact aerr_add hw0 iha ihb hp
  | mul _ _ hp iha ihb => exact aerr_mul hw0 iha ihb hp
  | neg _ iha          => exact aerr_neg iha
  | expO _ hp iha      => exact aerr_exp hw0 hw1 iha hp
  | sinO _ hp iha      => exact aerr_sin hw0 iha hp
  | cosO _ hp iha      => exact aerr_cos hw0 iha hp

/-- The forward-error corollary: `|v − exact| ≤ Ebound`. -/
theorem aexpr_fwd_error {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : AExpr} {v : Real} (h : ARoundedEval w t v) : abs (v - t.exact) ≤ t.Ebound w :=
  (aexpr_sound hw0 hw1 h).err

/-- **Amplifying `exp(x²)`** as a one-line instance — the case `OperatorBasisTrans`'s
bounded fold could *not* reach (the argument `x²` is unbounded above, so `exp` truly
amplifies). The meta-theorem hands back the condition-number-scaled bound
`exp(x²)·(exp(w·x²)·(1+w) − 1)` with no hand proof. -/
theorem exp_sq_via_meta {w x px p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hp : RoundsW w p (exp px)) :
    abs (p - exp (x * x))
      ≤ exp (abs (x * x)) * (exp (w * abs (x * x)) * (1 + w) - 1) :=
  aexpr_fwd_error hw0 hw1 (ARoundedEval.expO (ARoundedEval.rleaf (ve := x * x) hpx) hp)

/-- **Arithmetic-*of*-transcendental** compiles and yields a bound: `cos²θ` is
`mul (cosO …) (cosO …)` — a transcendental output flowing back into `×`, which the
relative/bounded folds (a stack *over* arithmetic) structurally could not express. -/
theorem cos_sq_mixed_via_meta {w θ pc p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpc : RoundsW w pc (cos θ)) (hp : RoundsW w p (pc * pc)) :
    abs (p - cos θ * cos θ)
      ≤ (AExpr.mul (.cosO (.leaf θ)) (.cosO (.leaf θ))).Ebound w :=
  aexpr_fwd_error hw0 hw1
    (ARoundedEval.mul (ARoundedEval.cosO (ARoundedEval.leaf θ) hpc)
      (ARoundedEval.cosO (ARoundedEval.leaf θ) hpc) hp)

end MachLib.Real
