import MachLib.DivisionError

/-!
# The complete operator-basis certifier — one fold, every operator including division

`OperatorBasisGeneral.aexpr_sound` folded every operator *except* division (which alone
needs a per-node denominator lower bound, a data-dependent side condition the
unconditional tree could not carry). `DivisionError.aerr_div` proved the division rule.
This file unites them: a **guarded** expression tree `GExpr` over the full basis
`{leaf, +, ×, neg, exp, sin, cos, ÷}`, a `Valid` predicate that carries each division
node's lower bound `m` (`0 < m ≤ denom.exact`), and **one fold `gexpr_sound`** that, for
any `Valid` tree, hands back the `AErr` magnitude+error certificate — folding all nine
per-operator rules (`aerr_leaf/round/neg/add/mul/exp/sin/cos/div`).

`GRoundedEval.divO` additionally witnesses that the *computed* denominator was guarded
(`m ≤ vb`) — what a real floating-point evaluation of a clamped/guarded denominator
provides. With this, **a single fold certifies the forward error of any kernel over the
operator basis.** `GExpr` supersedes `AExpr` (the division-free special case);
`aexpr_sound` remains as the unconditional result where no division occurs.

`sorryAx`-free; 0 new axioms. The Lorentzian `1/(1+x²)` (division over arithmetic, a
structurally-guaranteed positive denominator) drops out as a one-line instance.
-/

namespace MachLib.Real

/-! ## a guarded transcendental: `sqrt` (amplifying near 0 — lower-bound guarded)

`sqrt` is ill-conditioned at `0` (slope `1/(2√x) → ∞`), so like division it needs a
lower bound `0 < m ≤ arg`. On `[m, ∞)` it is `1/(2√m)`-Lipschitz — proved here from the
difference-of-squares identity `(√a−√b)(√a+√b) = a−b` and the division-inequality kit. -/

theorem sqrt_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) : sqrt a ≤ sqrt b := by
  have hb : 0 ≤ b := le_trans ha hab
  apply sqrt_le_of_le_sq (sqrt_nonneg b); rw [sqrt_sq_nonneg b hb]; exact hab

theorem sqrt_diff_mul {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (sqrt a - sqrt b) * (sqrt a + sqrt b) = a - b := by
  rw [show (sqrt a - sqrt b) * (sqrt a + sqrt b) = sqrt a * sqrt a - sqrt b * sqrt b from by
        mach_mpoly [sqrt a, sqrt b], sqrt_sq_nonneg a ha, sqrt_sq_nonneg b hb]

/-- `sqrt` is `1/(2√m)`-Lipschitz on `[m, ∞)`: `|√a − √b| ≤ |a − b| / (2√m)`. -/
theorem sqrt_lipschitz_bound {a b m : Real} (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) :
    abs (sqrt a - sqrt b) ≤ abs (a - b) / (sqrt m + sqrt m) := by
  have ha : 0 ≤ a := le_trans (le_of_lt hm) hma
  have hb : 0 ≤ b := le_trans (le_of_lt hm) hmb
  have hsm_le_sa : sqrt m ≤ sqrt a := sqrt_mono (le_of_lt hm) hma
  have hsm_le_sb : sqrt m ≤ sqrt b := sqrt_mono (le_of_lt hm) hmb
  have hsum_pos : 0 < sqrt a + sqrt b :=
    lt_of_lt_of_le (sqrt_pos hm) (le_trans hsm_le_sa (le_add_of_nonneg_right (sqrt_nonneg b)))
  rw [eq_div_of_mul_eq (ne_of_gt hsum_pos) (sqrt_diff_mul ha hb), abs_div_pos hsum_pos]
  exact div_le_div_pos (abs_nonneg _) (le_refl _) (add_pos (sqrt_pos hm) (sqrt_pos hm))
    (add_le_add_both hsm_le_sa hsm_le_sb)

/-- **`sqrt`** (`AErr`, argument bounded below `0 < m ≤ v, ve`): magnitude `√M`; error is
the `√`-rounding `w·√(M+E)` plus the `1/(2√m)`-Lipschitz propagation `E/(2√m)`. -/
theorem aerr_sqrt {w M E v ve m p : Real} (hw0 : 0 ≤ w)
    (hm : 0 < m) (hmv : m ≤ v) (hmve : m ≤ ve)
    (h : AErr M E v ve) (hp : RoundsW w p (sqrt v)) :
    AErr (sqrt M) (w * sqrt (M + E) + E / (sqrt m + sqrt m)) p (sqrt ve) := by
  have hv0 : 0 < v := lt_of_lt_of_le hm hmv
  have hve0 : 0 < ve := lt_of_lt_of_le hm hmve
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (sqrt_nonneg ve)]
    exact sqrt_mono (le_of_lt hve0) (le_trans (le_abs_self ve) h.1)
  · have hround : abs (p - sqrt v) ≤ w * sqrt (M + E) := by
      have h1 := roundsW_abs hp
      rw [abs_of_nonneg (sqrt_nonneg v)] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left
        (sqrt_mono (le_of_lt hv0) (le_trans (le_abs_self v) h.val_bound)) hw0)
    have hprop : abs (sqrt v - sqrt ve) ≤ E / (sqrt m + sqrt m) :=
      le_trans (sqrt_lipschitz_bound hm hmv hmve)
        (div_le_div_pos (abs_nonneg _) h.2 (add_pos (sqrt_pos hm) (sqrt_pos hm)) (le_refl _))
    rw [et_split3 p (sqrt v) (sqrt ve)]
    exact le_trans (abs_add _ _) (add_le_add_both hround hprop)

/-- A guarded expression over the full operator basis. `divO a b m` records the
denominator lower bound `m` it is certified against. -/
inductive GExpr where
  | leaf  (ve : Real)
  | rleaf (ve : Real)
  | add   (a b : GExpr)
  | mul   (a b : GExpr)
  | neg   (a : GExpr)
  | expO  (a : GExpr)
  | sinO  (a : GExpr)
  | cosO  (a : GExpr)
  | divO  (a b : GExpr) (m : Real)
  | clampO (a : GExpr) (lo hi : Real)
  | sqrtO (a : GExpr) (m : Real)        -- `√a`, `a` bounded below by `m > 0`

/-- The exact value. -/
noncomputable def GExpr.exact : GExpr → Real
  | .leaf ve     => ve
  | .rleaf ve    => ve
  | .add a b     => GExpr.exact a + GExpr.exact b
  | .mul a b     => GExpr.exact a * GExpr.exact b
  | .neg a       => -(GExpr.exact a)
  | .expO a      => exp (GExpr.exact a)
  | .sinO a      => sin (GExpr.exact a)
  | .cosO a      => cos (GExpr.exact a)
  | .divO a b _  => GExpr.exact a / GExpr.exact b
  | .clampO a lo hi => clamp (GExpr.exact a) lo hi
  | .sqrtO a _   => sqrt (GExpr.exact a)
  termination_by structural t => t

/-- Magnitude bound (`÷` uses the lower bound: `|a/b| ≤ Mbound a / m`). -/
noncomputable def GExpr.Mbound : GExpr → Real
  | .leaf ve     => abs ve
  | .rleaf ve    => abs ve
  | .add a b     => GExpr.Mbound a + GExpr.Mbound b
  | .mul a b     => GExpr.Mbound a * GExpr.Mbound b
  | .neg a       => GExpr.Mbound a
  | .expO a      => exp (GExpr.Mbound a)
  | .sinO _      => 1
  | .cosO _      => 1
  | .divO a _ m  => GExpr.Mbound a / m
  | .clampO _ lo hi => max (abs lo) (abs hi)
  | .sqrtO a _   => sqrt (GExpr.Mbound a)
  termination_by structural t => t

/-- Forward-error bound (`÷` term is `aerr_div`'s, every part scaled by `1/m`). -/
noncomputable def GExpr.Ebound (w : Real) : GExpr → Real
  | .leaf _      => 0
  | .rleaf ve    => w * abs ve
  | .add a b     => GExpr.Ebound w a + GExpr.Ebound w b
                    + w * (GExpr.Mbound a + GExpr.Ebound w a + GExpr.Mbound b + GExpr.Ebound w b)
  | .mul a b     => (GExpr.Mbound a + GExpr.Ebound w a) * GExpr.Ebound w b
                    + GExpr.Mbound b * GExpr.Ebound w a
                    + w * ((GExpr.Mbound a + GExpr.Ebound w a) * (GExpr.Mbound b + GExpr.Ebound w b))
  | .neg a       => GExpr.Ebound w a
  | .expO a      => exp (GExpr.Mbound a) * (exp (GExpr.Ebound w a) * (1 + w) - 1)
  | .sinO a      => GExpr.Ebound w a + w
  | .cosO a      => GExpr.Ebound w a + w
  | .divO a b m  => w * ((GExpr.Mbound a + GExpr.Ebound w a) / m)
                    + (GExpr.Ebound w a / m + GExpr.Mbound a * GExpr.Ebound w b / (m * m))
  | .clampO a _ _ => GExpr.Ebound w a
  | .sqrtO a m   => w * sqrt (GExpr.Mbound a + GExpr.Ebound w a)
                    + GExpr.Ebound w a / (sqrt m + sqrt m)
  termination_by structural t => t

/-- Validity: at each `÷` node, the recorded bound is positive and below the exact
denominator (`0 < m ≤ denom.exact`). Trivially `True` away from division. -/
def GExpr.Valid : GExpr → Prop
  | .leaf _      => True
  | .rleaf _     => True
  | .add a b     => GExpr.Valid a ∧ GExpr.Valid b
  | .mul a b     => GExpr.Valid a ∧ GExpr.Valid b
  | .neg a       => GExpr.Valid a
  | .expO a      => GExpr.Valid a
  | .sinO a      => GExpr.Valid a
  | .cosO a      => GExpr.Valid a
  | .divO a b m  => GExpr.Valid a ∧ GExpr.Valid b ∧ 0 < m ∧ m ≤ GExpr.exact b
  | .clampO a lo hi => GExpr.Valid a ∧ lo ≤ hi
  | .sqrtO a m   => GExpr.Valid a ∧ 0 < m ∧ m ≤ GExpr.exact a
  termination_by structural t => t

/-- Any per-node-rounded evaluation. `divO` additionally witnesses the computed
denominator is guarded (`m ≤ vb`) — what a guarded floating-point division provides. -/
inductive GRoundedEval (w : Real) : GExpr → Real → Prop where
  | leaf  (ve : Real) : GRoundedEval w (.leaf ve) ve
  | rleaf {ve p : Real} (hp : RoundsW w p ve) : GRoundedEval w (.rleaf ve) p
  | add   {a b : GExpr} {va vb p : Real} (ha : GRoundedEval w a va) (hb : GRoundedEval w b vb)
      (hp : RoundsW w p (va + vb)) : GRoundedEval w (.add a b) p
  | mul   {a b : GExpr} {va vb p : Real} (ha : GRoundedEval w a va) (hb : GRoundedEval w b vb)
      (hp : RoundsW w p (va * vb)) : GRoundedEval w (.mul a b) p
  | neg   {a : GExpr} {va : Real} (ha : GRoundedEval w a va) : GRoundedEval w (.neg a) (-va)
  | expO  {a : GExpr} {va p : Real} (ha : GRoundedEval w a va)
      (hp : RoundsW w p (exp va)) : GRoundedEval w (.expO a) p
  | sinO  {a : GExpr} {va p : Real} (ha : GRoundedEval w a va)
      (hp : RoundsW w p (sin va)) : GRoundedEval w (.sinO a) p
  | cosO  {a : GExpr} {va p : Real} (ha : GRoundedEval w a va)
      (hp : RoundsW w p (cos va)) : GRoundedEval w (.cosO a) p
  | divO  {a b : GExpr} {va vb p m : Real} (ha : GRoundedEval w a va) (hb : GRoundedEval w b vb)
      (hvb : m ≤ vb) (hp : RoundsW w p (va / vb)) : GRoundedEval w (.divO a b m) p
  | clampO {a : GExpr} {va lo hi : Real} (ha : GRoundedEval w a va) :
      GRoundedEval w (.clampO a lo hi) (clamp va lo hi)   -- min/max are exact: no rounding
  | sqrtO {a : GExpr} {va p m : Real} (ha : GRoundedEval w a va) (hmv : m ≤ va)
      (hp : RoundsW w p (sqrt va)) : GRoundedEval w (.sqrtO a m) p

/-- **The complete certifier.** Any per-node-rounded evaluation of a `Valid` expression
over the *full* operator basis (division included) carries the `AErr` magnitude+error
certificate — one structural induction folding all nine per-operator rules. -/
theorem gexpr_sound {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : GExpr} {v : Real} (h : GRoundedEval w t v) :
    t.Valid → AErr t.Mbound (t.Ebound w) v t.exact := by
  induction h with
  | leaf ve            => exact fun _ => aerr_leaf ve
  | rleaf hp           => exact fun _ => aerr_round hp
  | add _ _ hp iha ihb => exact fun hv => aerr_add hw0 (iha hv.1) (ihb hv.2) hp
  | mul _ _ hp iha ihb => exact fun hv => aerr_mul hw0 (iha hv.1) (ihb hv.2) hp
  | neg _ iha          => exact fun hv => aerr_neg (iha hv)
  | expO _ hp iha      => exact fun hv => aerr_exp hw0 hw1 (iha hv) hp
  | sinO _ hp iha      => exact fun hv => aerr_sin hw0 (iha hv) hp
  | cosO _ hp iha      => exact fun hv => aerr_cos hw0 (iha hv) hp
  | divO _ _ hvb hp iha ihb =>
      exact fun hv => aerr_div hw0 (iha hv.1) (ihb hv.2.1) hv.2.2.1 hvb hv.2.2.2 hp
  | clampO _ iha => exact fun hv => aerr_clamp hv.2 (iha hv.1)
  | sqrtO _ hmv hp iha => exact fun hv => aerr_sqrt hw0 hv.2.1 hmv hv.2.2 (iha hv.1) hp

/-- The forward-error corollary: `|v − exact| ≤ Ebound`, for any `Valid` kernel. -/
theorem gexpr_fwd_error {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : GExpr} {v : Real} (h : GRoundedEval w t v) (hv : t.Valid) :
    abs (v - t.exact) ≤ t.Ebound w :=
  (gexpr_sound hw0 hw1 h hv).err

/-- **Cross-target equivalence — for the whole operator basis.** The *same* kernel `t`
evaluated at two unit-roundoffs `w₁, w₂` (e.g. an `f32` shader lane and an `f64`
software lane) agrees to within `Ebound w₁ + Ebound w₂` — both evaluations enclose the
single exact value, so the triangle bounds their gap. One proof for *every* kernel the
certifier covers (division included), generalizing the per-kernel `CrossTargetPairs`
lemmas: cross-target numerical agreement is now a property of the operator basis, not a
hand-proved fact per kernel. -/
theorem gexpr_cross_target {w1 w2 : Real}
    (hw10 : 0 ≤ w1) (hw11 : w1 ≤ 1) (hw20 : 0 ≤ w2) (hw21 : w2 ≤ 1)
    {t : GExpr} {v1 v2 : Real}
    (h1 : GRoundedEval w1 t v1) (h2 : GRoundedEval w2 t v2) (hv : t.Valid) :
    abs (v1 - v2) ≤ t.Ebound w1 + t.Ebound w2 := by
  have e1 := gexpr_fwd_error hw10 hw11 h1 hv
  have e2 : abs (t.exact - v2) ≤ t.Ebound w2 := by
    rw [show t.exact - v2 = -(v2 - t.exact) from by mach_ring, abs_neg]
    exact gexpr_fwd_error hw20 hw21 h2 hv
  rw [et_split3 v1 t.exact v2]
  exact le_trans (abs_add _ _) (add_le_add_both e1 e2)

/-- A guarded ratio `x / y` (`y ≥ m > 0`, exact inputs) certified end-to-end by the
complete fold — division now folds like every other operator. -/
theorem ratio_via_gfold {w x y p m : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hm : 0 < m) (hmy : m ≤ y) (hp : RoundsW w p (x / y)) :
    abs (p - x / y) ≤ (GExpr.divO (.leaf x) (.leaf y) m).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.divO (GRoundedEval.leaf x) (GRoundedEval.leaf y) hmy hp)
    ⟨trivial, trivial, hm, hmy⟩

/-- **The Lorentzian `1/(1+x²)`** (division *over* arithmetic, denominator structurally
`≥ 1`): a single fold certifies it. The denominator subtree `1 + x²` is `add (leaf 1)
(rleaf x²)`, exact `1 + x² ≥ 1`, so the validity bound `m = 1` is met with no hand proof
beyond `0 ≤ x²`. -/
theorem lorentzian_via_gfold {w x px s p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hs : RoundsW w s (1 + px)) (hsc : 1 ≤ s)
    (hp : RoundsW w p (1 / s)) :
    abs (p - 1 / (1 + x * x))
      ≤ (GExpr.divO (.leaf 1) (.add (.leaf 1) (.rleaf (x * x))) 1).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.divO (GRoundedEval.leaf 1)
      (GRoundedEval.add (GRoundedEval.leaf 1) (GRoundedEval.rleaf hpx) hs) hsc hp)
    ⟨trivial, ⟨trivial, trivial⟩, zero_lt_one_ax, le_add_of_nonneg_right (sq_nonneg x)⟩

/-- **Cross-target: the Lorentzian `1/(1+x²)` at two precisions.** A division-containing
kernel computed on two lanes (`w₁`, `w₂`) agrees to within the sum of the two lanes'
forward-error bounds — proven cross-target equivalence for a kernel with a transcendental-
free but division-bearing shape, straight from the general `gexpr_cross_target`. -/
theorem lorentzian_cross_target {w1 w2 x px1 s1 p1 px2 s2 p2 : Real}
    (hw10 : 0 ≤ w1) (hw11 : w1 ≤ 1) (hw20 : 0 ≤ w2) (hw21 : w2 ≤ 1)
    (hpx1 : RoundsW w1 px1 (x * x)) (hs1 : RoundsW w1 s1 (1 + px1)) (hsc1 : 1 ≤ s1)
    (hp1 : RoundsW w1 p1 (1 / s1))
    (hpx2 : RoundsW w2 px2 (x * x)) (hs2 : RoundsW w2 s2 (1 + px2)) (hsc2 : 1 ≤ s2)
    (hp2 : RoundsW w2 p2 (1 / s2)) :
    abs (p1 - p2)
      ≤ (GExpr.divO (.leaf 1) (.add (.leaf 1) (.rleaf (x * x))) 1).Ebound w1
        + (GExpr.divO (.leaf 1) (.add (.leaf 1) (.rleaf (x * x))) 1).Ebound w2 :=
  gexpr_cross_target hw10 hw11 hw20 hw21
    (GRoundedEval.divO (GRoundedEval.leaf 1)
      (GRoundedEval.add (GRoundedEval.leaf 1) (GRoundedEval.rleaf hpx1) hs1) hsc1 hp1)
    (GRoundedEval.divO (GRoundedEval.leaf 1)
      (GRoundedEval.add (GRoundedEval.leaf 1) (GRoundedEval.rleaf hpx2) hs2) hsc2 hp2)
    ⟨trivial, ⟨trivial, trivial⟩, zero_lt_one_ax, le_add_of_nonneg_right (sq_nonneg x)⟩

end MachLib.Real
