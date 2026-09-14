import MachLib.EMLTreeGroundedPipeline
import MachLib.AcosTaylorRemainder

/-!
# Discharging the grounded certificates' float side conditions: what can be, and what cannot

Since 2026-09-14 the grounded forward-error certificates (`FPGrounding.lean`, `EMLCertcomGrounded.lean`,
`EMLTreeGroundedPipeline.lean`) take `hsafe : FloatSafe …` or `EMLTreeFloatSafe …`, and some take finiteness
hypotheses on single floats besides. A conditional theorem is not evidence until its hypotheses are instantiated.
This module instantiates what the disclosed axioms allow, shows why nothing else can be instantiated from ANY
assumption about the inputs, and names the missing fact.

## Nothing here concludes that a float is finite

Read off the environment after `import MachLib`, not grepped. The disclosed axioms that mention `Float.isFinite`
(`real_exp_rounds`, `real_sinh_rounds`, `real_cosh_rounds`, `real_log10_rounds`, `real_tan_rounds`,
`real_tanh_rounds`, and the fields of `FPBridgeFinite`, which `real_fpbridge` asserts) all have it as a PREMISE.
The only theorems with it in a conclusion are projections out of a `FloatSafe` or `EMLTreeFloatSafe` premise.
Lean core proves nothing about it: `Float.isFinite` is an `@[extern]` opaque, so `decide` and `rfl` get stuck,
`exact?` closes no finiteness goal, and `native_decide` proves one only by adding an axiom of its own for each
use. `real_round_bounds` says how close `floatOfR x` reads back, never that it is finite.

So `FloatSafe` of a tree with a `+`, `−`, `×` or negation node, and `EMLTreeFloatSafe` of an `eml` node, cannot be
established for any input, however it is bounded. That is a property of the axiom set, not of these proofs. No flat
certificate in `FPGrounding.lean`, and no `eml`-node instance of `eml_tree_grounded`, is instantiated.
`no-float-finiteness-producer` in `tools/absence_claims.json` is an environment scan that fires when anything starts
concluding finiteness, including an axiom stated as a structure and a `native_decide` theorem.

## `FloatSafe` is two conditions of different kinds

`floatSafe_of_split`, `FloatSafe.floatFinite` and `FloatSafe.productsNormal`: `FloatSafe` holds exactly when both
`FloatFinite` (every node's computed float is finite, a property of the run and the half nothing can supply) and
`ProductsNormal` (every product's exact real value is `0` or at least `DBL_MIN`, a property of real numbers) hold.

The second half discharges from a real domain (`mul_normal_of_floors`, `productsNormal_detEML`,
`productsNormal_pidRawEML`), and it needs a magnitude FLOOR, not merely a bound:
`bounded_inputs_can_have_subnormal_product` exhibits two nonzero reals of magnitude at most `1` (both `DBL_MIN`)
whose product violates it. For a product of two inputs, each `0` or at least `α` in magnitude, `DBL_MIN ≤ α·α` is
enough; `α = 2⁻⁵¹¹` makes it an equality. For the `gain × input` products of `pidRawEML` the floor is on `κ·δ`,
where `κ` bounds the gains' real values `realToR 1.5`, `realToR 0.4` and `realToR 0.05` from below, and no axiom says
anything about the real value of a `Float` literal.

`pipeline_det_grounded_of_floor` composes both halves with `pipeline_det_grounded`: given the floor on its four
inputs, that certificate needs only `FloatFinite` of its three computed floats. It is a REDUCTION, not an instance,
since nothing can supply that hypothesis.

## The instance that exists: a constant leaf

`eml_tree_grounded_const_leaf` is `eml_tree_grounded` at `EMLTree.const c`, for every real `c` that is `0` or has
`DBL_MIN ≤ |c| ≤ DBL_MAX`: the compiled constant, read back through `realToR`, is within `u·|c|` of `c`. A constant
leaf's float side conditions are conditions on the real `c` alone, so they discharge.
`eml_tree_grounded_const_one_specimen` (`c = 1`, within `u`) and `eml_tree_grounded_const_zero_specimen` (`c = 0`,
exact) take both branches of `c = 0 ∨ DBL_MIN ≤ |c|`. It is depth 0: it rests on `real_round_bounds`, and it certifies
no arithmetic node and no primitive. It is all that the current axioms instantiate.

## What would change that, and why it is not added here

The missing fact is round-to-nearest's overflow rule over `realToR`: for finite `a` and `b`, if the exact real value
of `a + b`, `a − b` or `a * b` is at most `DBL_MAX` in magnitude then the float result is finite, and `-a` is finite.
A specimen also needs one float known to be finite, for instance `floatOfR x` for `|x| ≤ DBL_MAX`. The PID kernels
need the real values of their literal gains as well, and `exp`, `sinh` and `cosh` need a finite result from a bounded
argument. Each is a new disclosed axiom, and each needs the owner's approval; none is added here.

One obstacle survives all of them. `u` is constrained only by `0 ≤ u ≤ 1`, so `real_round_bounds` places
`realToR (floatOfR x)` in an interval containing `0` for every `x`. No float is provably nonzero, so no specimen can
reach the `DBL_MIN ≤ |X·Y|` branch of a product while `u < 1` is not known.
-/

namespace Certcom

open MachLib MachLib.Real

/-! ## 1. The split -/

/-- The finiteness half of `FloatSafe`: every `+`, `−`, `×` and negation node of the evaluation computes a finite
float. It mentions no real number, and nothing in this corpus can establish it for a concrete input (module
docstring). -/
inductive FloatFinite (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    EML → Prop
  | lit (c : Float) : FloatFinite i1 i2 env (.lit c)
  | var (s : String) : FloatFinite i1 i2 env (.var s)
  | add (a b : EML) : FloatFinite i1 i2 env a → FloatFinite i1 i2 env b →
      ((evalEML i1 i2 env a).toF + (evalEML i1 i2 env b).toF).isFinite = true →
      FloatFinite i1 i2 env (.bin .add a b)
  | sub (a b : EML) : FloatFinite i1 i2 env a → FloatFinite i1 i2 env b →
      ((evalEML i1 i2 env a).toF - (evalEML i1 i2 env b).toF).isFinite = true →
      FloatFinite i1 i2 env (.bin .sub a b)
  | mul (a b : EML) : FloatFinite i1 i2 env a → FloatFinite i1 i2 env b →
      ((evalEML i1 i2 env a).toF * (evalEML i1 i2 env b).toF).isFinite = true →
      FloatFinite i1 i2 env (.bin .mul a b)
  | neg (a : EML) : FloatFinite i1 i2 env a → (evalEML i1 i2 env a).toF.isFinite = true →
      FloatFinite i1 i2 env (.neg a)
  | tr1 (t : Trans1) (a : EML) : FloatFinite i1 i2 env a → FloatFinite i1 i2 env (.tr1 t a)

/-- The real half of `FloatSafe`: at every product node the exact product of the operands' real values is `0` or at
least `DBL_MIN` in magnitude. It mentions no float's finiteness, and it discharges from a magnitude floor on the
operands (`mul_normal_of_floors`). -/
inductive ProductsNormal (toR : Float → MachLib.Real) (i1 : Trans1 → Float → Float)
    (i2 : Trans2 → Float → Float → Float) (env : Env) : EML → Prop
  | lit (c : Float) : ProductsNormal toR i1 i2 env (.lit c)
  | var (s : String) : ProductsNormal toR i1 i2 env (.var s)
  | add (a b : EML) : ProductsNormal toR i1 i2 env a → ProductsNormal toR i1 i2 env b →
      ProductsNormal toR i1 i2 env (.bin .add a b)
  | sub (a b : EML) : ProductsNormal toR i1 i2 env a → ProductsNormal toR i1 i2 env b →
      ProductsNormal toR i1 i2 env (.bin .sub a b)
  | mul (a b : EML) : ProductsNormal toR i1 i2 env a → ProductsNormal toR i1 i2 env b →
      (toR (evalEML i1 i2 env a).toF * toR (evalEML i1 i2 env b).toF = 0 ∨
        dblMin ≤ abs (toR (evalEML i1 i2 env a).toF * toR (evalEML i1 i2 env b).toF)) →
      ProductsNormal toR i1 i2 env (.bin .mul a b)
  | neg (a : EML) : ProductsNormal toR i1 i2 env a → ProductsNormal toR i1 i2 env (.neg a)
  | tr1 (t : Trans1) (a : EML) : ProductsNormal toR i1 i2 env a → ProductsNormal toR i1 i2 env (.tr1 t a)

/-- **`FloatSafe` from its two halves.** With `FloatSafe.floatFinite` and `FloatSafe.productsNormal`, the split is
exact. -/
theorem floatSafe_of_split {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} {env : Env} {e : EML}
    (hf : FloatFinite i1 i2 env e) (hp : ProductsNormal toR i1 i2 env e) : FloatSafe toR i1 i2 env e := by
  induction hf with
  | lit c => exact FloatSafe.lit c
  | var s => exact FloatSafe.var s
  | add a b _ _ hfin iha ihb =>
      cases hp with
      | add _ _ hpa hpb => exact FloatSafe.add a b (iha hpa) (ihb hpb) hfin
  | sub a b _ _ hfin iha ihb =>
      cases hp with
      | sub _ _ hpa hpb => exact FloatSafe.sub a b (iha hpa) (ihb hpb) hfin
  | mul a b _ _ hfin iha ihb =>
      cases hp with
      | mul _ _ hpa hpb hz => exact FloatSafe.mul a b (iha hpa) (ihb hpb) hfin hz
  | neg a _ hfin iha =>
      cases hp with
      | neg _ hpa => exact FloatSafe.neg a (iha hpa) hfin
  | tr1 t a _ iha =>
      cases hp with
      | tr1 _ _ hpa => exact FloatSafe.tr1 t a (iha hpa)

/-- `FloatSafe` contains its finiteness half. -/
theorem FloatSafe.floatFinite {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} {env : Env} {e : EML}
    (h : FloatSafe toR i1 i2 env e) : FloatFinite i1 i2 env e := by
  induction h with
  | lit c => exact FloatFinite.lit c
  | var s => exact FloatFinite.var s
  | add a b _ _ hf iha ihb => exact FloatFinite.add a b iha ihb hf
  | sub a b _ _ hf iha ihb => exact FloatFinite.sub a b iha ihb hf
  | mul a b _ _ hf _ iha ihb => exact FloatFinite.mul a b iha ihb hf
  | neg a _ hf iha => exact FloatFinite.neg a iha hf
  | tr1 t a _ iha => exact FloatFinite.tr1 t a iha

/-- `FloatSafe` contains its real half. -/
theorem FloatSafe.productsNormal {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} {env : Env} {e : EML}
    (h : FloatSafe toR i1 i2 env e) : ProductsNormal toR i1 i2 env e := by
  induction h with
  | lit c => exact ProductsNormal.lit c
  | var s => exact ProductsNormal.var s
  | add a b _ _ _ iha ihb => exact ProductsNormal.add a b iha ihb
  | sub a b _ _ _ iha ihb => exact ProductsNormal.sub a b iha ihb
  | mul a b _ _ _ hz iha ihb => exact ProductsNormal.mul a b iha ihb hz
  | neg a _ _ iha => exact ProductsNormal.neg a iha
  | tr1 t a _ iha => exact ProductsNormal.tr1 t a iha

/-! ## 2. The real side -/

/-- `0 ≤ DBL_MAX`. -/
theorem dblMax_nonneg : (0 : MachLib.Real) ≤ dblMax := Real.natCast_nonneg _

set_option exponentiation.threshold 1100 in
/-- `1 ≤ DBL_MAX`, which is what lets a constant of magnitude at most `1` meet `real_round_bounds`'s range. -/
theorem one_le_dblMax : (1 : MachLib.Real) ≤ dblMax := by
  have h1 : 1 ≤ (2 ^ 53 - 1) * 2 ^ 971 := by decide
  have hn : (2 ^ 53 - 1) * 2 ^ 971 = ((2 ^ 53 - 1) * 2 ^ 971 - 1) + 1 := (Nat.sub_add_cancel h1).symm
  show (1 : MachLib.Real) ≤ natCast ((2 ^ 53 - 1) * 2 ^ 971)
  rw [hn, natCast_succ]
  exact le_add_of_nonneg_left (Real.natCast_nonneg _)

set_option exponentiation.threshold 1100 in
/-- `DBL_MIN < 1`, strictly. -/
theorem dblMin_lt_one : dblMin < 1 := by
  have h1 : 0 < 2 ^ 1022 - 1 := by decide
  have hn : 2 ^ 1022 = (2 ^ 1022 - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_two_pow (n := 1022))).symm
  have hk : (0 : MachLib.Real) < natCast (2 ^ 1022 - 1) := natCast_pos h1
  have hgt : (1 : MachLib.Real) < natCast (2 ^ 1022) := by
    rw [hn, natCast_succ]
    have h2 := add_lt_add_left hk 1
    rw [add_zero, add_comm] at h2
    exact h2
  show (1 : MachLib.Real) / natCast (2 ^ 1022) < 1
  exact div_lt_one_of_pos_lt (natCast_pos (Nat.two_pow_pos 1022)) hgt

/-- **The `DBL_MIN` condition of a product, from magnitude floors on its operands.** If each operand is `0` or at
least its floor in magnitude, and the floors' product is at least `DBL_MIN`, the exact product is `0` or at least
`DBL_MIN`. -/
theorem mul_normal_of_floors {X Y α β : MachLib.Real} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : dblMin ≤ α * β) (hX : X = 0 ∨ α ≤ abs X) (hY : Y = 0 ∨ β ≤ abs Y) :
    X * Y = 0 ∨ dblMin ≤ abs (X * Y) := by
  rcases hX with hX0 | hXa
  · rw [hX0]; exact Or.inl (zero_mul Y)
  · rcases hY with hY0 | hYb
    · rw [hY0]; exact Or.inl (mul_zero X)
    · rw [abs_mul]; exact Or.inr (le_trans hαβ (mul_le_mul' hα hXa hβ hYb))

/-- **A bound alone does not give the `DBL_MIN` condition.** Two nonzero reals of magnitude at most `1` (both
`DBL_MIN`) whose exact product is neither `0` nor at least `DBL_MIN`. Any domain that discharges `ProductsNormal`
therefore needs a floor, which is why `mul_normal_of_floors` takes one. -/
theorem bounded_inputs_can_have_subnormal_product :
    ∃ X Y : MachLib.Real, X ≠ 0 ∧ Y ≠ 0 ∧ abs X ≤ 1 ∧ abs Y ≤ 1 ∧
      ¬ (X * Y = 0 ∨ dblMin ≤ abs (X * Y)) := by
  have hpos : (0 : MachLib.Real) < dblMin * dblMin := mul_pos dblMin_pos dblMin_pos
  have hlt : dblMin * dblMin < dblMin := by
    have h1 := mul_lt_mul_left_helper dblMin_pos dblMin_lt_one
    rw [mul_one_ax] at h1
    exact h1
  have habs : abs dblMin = dblMin := abs_of_nonneg (le_of_lt dblMin_pos)
  refine ⟨dblMin, dblMin, Ne.symm (ne_of_lt dblMin_pos), Ne.symm (ne_of_lt dblMin_pos),
    by rw [habs]; exact dblMin_le_one, by rw [habs]; exact dblMin_le_one, ?_⟩
  intro h
  rcases h with h0 | hle
  · exact (ne_of_lt hpos) h0.symm
  · rw [abs_of_nonneg (le_of_lt hpos)] at hle
    exact (ne_of_lt (lt_of_le_of_lt hle hlt)) rfl

/-! ## 3. The real half, discharged for two kernels -/

/-- `ProductsNormal` for the determinant kernel `x·y − z·w`, from a floor `α` on its four inputs with
`DBL_MIN ≤ α·α`. Every quantity here is an input's real value: nothing about floats is assumed. -/
theorem productsNormal_detEML {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} (env : Env) {α : MachLib.Real}
    (hα : 0 ≤ α) (hαα : dblMin ≤ α * α)
    (hx : toR (env "x").toF = 0 ∨ α ≤ abs (toR (env "x").toF))
    (hy : toR (env "y").toF = 0 ∨ α ≤ abs (toR (env "y").toF))
    (hz : toR (env "z").toF = 0 ∨ α ≤ abs (toR (env "z").toF))
    (hw : toR (env "w").toF = 0 ∨ α ≤ abs (toR (env "w").toF)) :
    ProductsNormal toR i1 i2 env detEML :=
  ProductsNormal.sub _ _
    (ProductsNormal.mul _ _ (.var "x") (.var "y") (mul_normal_of_floors hα hα hαα hx hy))
    (ProductsNormal.mul _ _ (.var "z") (.var "w") (mul_normal_of_floors hα hα hαα hz hw))

/-- `ProductsNormal` for the PID law `1.5·e + 0.4·i + 0.05·d`, from a floor `δ` on the three inputs and a floor `κ`
on the three gains' real values, with `DBL_MIN ≤ κ·δ`. The gain hypotheses are about `toR` at `Float` literals; at
`realToR` no axiom constrains those values, so this lemma does not discharge `pidRawEML`'s real half on its own. -/
theorem productsNormal_pidRawEML {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} (env : Env) {κ δ : MachLib.Real}
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hκδ : dblMin ≤ κ * δ)
    (hkp : toR 1.5 = 0 ∨ κ ≤ abs (toR 1.5)) (hki : toR 0.4 = 0 ∨ κ ≤ abs (toR 0.4))
    (hkd : toR 0.05 = 0 ∨ κ ≤ abs (toR 0.05))
    (he : toR (env "e").toF = 0 ∨ δ ≤ abs (toR (env "e").toF))
    (hi : toR (env "i").toF = 0 ∨ δ ≤ abs (toR (env "i").toF))
    (hd : toR (env "d").toF = 0 ∨ δ ≤ abs (toR (env "d").toF)) :
    ProductsNormal toR i1 i2 env pidRawEML :=
  ProductsNormal.add _ _
    (ProductsNormal.add _ _
      (ProductsNormal.mul _ _ (.lit 1.5) (.var "e") (mul_normal_of_floors hκ hδ hκδ hkp he))
      (ProductsNormal.mul _ _ (.lit 0.4) (.var "i") (mul_normal_of_floors hκ hδ hκδ hki hi)))
    (ProductsNormal.mul _ _ (.lit 0.05) (.var "d") (mul_normal_of_floors hκ hδ hκδ hkd hd))

/-- **A reduction of `pipeline_det_grounded`, NOT an instance of it.** Given a floor on the four inputs, the
certificate's `hsafe` comes down to `hfin`: the two products and the difference compute finite floats. Nothing in this
corpus can supply `hfin` for a concrete input (module docstring), so this theorem is exactly as conditional as the
certificate it calls, on a smaller and purely float-valued hypothesis. -/
theorem pipeline_det_grounded_of_floor (env : Env) {α : MachLib.Real}
    (hfin : FloatFinite (fun _ _ => 0) (fun _ _ _ => 0) env detEML)
    (hα : 0 ≤ α) (hαα : dblMin ≤ α * α)
    (hx : realToR (env "x").toF = 0 ∨ α ≤ abs (realToR (env "x").toF))
    (hy : realToR (env "y").toF = 0 ∨ α ≤ abs (realToR (env "y").toF))
    (hz : realToR (env "z").toF = 0 ∨ α ≤ abs (realToR (env "z").toF))
    (hw : realToR (env "w").toF = 0 ∨ α ≤ abs (realToR (env "w").toF)) :
    AbsEnc (u * (1 + 1 + u) * (abs (realToR (env "x").toF * realToR (env "y").toF)
                              + abs (realToR (env "z").toF * realToR (env "w").toF)))
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC detEML)).toF)
      (realToR (env "x").toF * realToR (env "y").toF
        - realToR (env "z").toF * realToR (env "w").toF) :=
  pipeline_det_grounded env (floatSafe_of_split hfin (productsNormal_detEML env hα hαα hx hy hz hw))

/-! ## 4. The instance: a constant leaf -/

/-- **`eml_tree_grounded`, instantiated at a constant leaf.** For every real `c` that is `0` or has
`DBL_MIN ≤ |c| ≤ DBL_MAX`, the compiled constant, read back through `realToR`, is within `u·|c|` of `c`. The float
side conditions (`EMLTreeFloatSafe.const`) are conditions on `c` alone and discharge from the domain; validity is
unconditional at a leaf. Depth 0: it rests on `real_round_bounds` and certifies no arithmetic node and no primitive. -/
theorem eml_tree_grounded_const_leaf (env : Env) (c : MachLib.Real)
    (hc : c = 0 ∨ dblMin ≤ abs c) (hcM : abs c ≤ dblMax) :
    abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML (EMLTree.const c))).toF - c)
      ≤ u * abs c :=
  (eml_tree_grounded env (EMLTree.const c) (EMLTreeValid.const c) (EMLTreeFloatSafe.const c hc hcM)).2.2

/-- A concrete environment for the specimens. A constant leaf never reads it; `eml_tree_grounded` quantifies over
one. -/
def leafSpecimenEnv : Env := fun _ => Val.scalar 0.0

/-- **Specimen, `c = 1`.** Every hypothesis of `eml_tree_grounded_const_leaf` discharged, through the `DBL_MIN ≤ |c|`
branch: the compiled constant `1` reads back within `u` of `1`. -/
theorem eml_tree_grounded_const_one_specimen :
    abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) leafSpecimenEnv
      (toCertcomEML (EMLTree.const 1))).toF - 1) ≤ u := by
  have h := eml_tree_grounded_const_leaf leafSpecimenEnv 1
    (Or.inr (by rw [abs_one]; exact dblMin_le_one)) (by rw [abs_one]; exact one_le_dblMax)
  rw [abs_one, mul_one_ax] at h
  exact h

/-- **Specimen, `c = 0`.** Every hypothesis discharged, through the `c = 0` branch: the compiled constant `0` reads
back exactly. -/
theorem eml_tree_grounded_const_zero_specimen :
    realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) leafSpecimenEnv
      (toCertcomEML (EMLTree.const 0))).toF = 0 := by
  have h := eml_tree_grounded_const_leaf leafSpecimenEnv 0 (Or.inl rfl)
    (by rw [abs_zero]; exact dblMax_nonneg)
  rw [abs_zero, mul_zero, sub_zero] at h
  exact eq_zero_of_abs_le_zero h

end Certcom

