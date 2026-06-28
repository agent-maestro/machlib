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

/-- The forward-error corollary: `|v − exact| ≤ Ebound`, for any `Valid` kernel. -/
theorem gexpr_fwd_error {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : GExpr} {v : Real} (h : GRoundedEval w t v) (hv : t.Valid) :
    abs (v - t.exact) ≤ t.Ebound w :=
  (gexpr_sound hw0 hw1 h hv).err

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

end MachLib.Real
