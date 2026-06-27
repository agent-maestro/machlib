import MachLib.Basic
import MachLib.Ring
import MachLib.Lemmas
import MachLib.Forge
import MachLib.FPModel

/-!
# Consistency model — the flagship axiom closure has a model (so it is not vacuous)

`#print axioms` proves a theorem has no `sorry`. It does **not** prove the axioms
it rests on are *consistent*: a bogus `axiom foo : (0:Real) = 1` would pass every
`#print axioms` check and silently make everything downstream true-but-meaningless.
This file closes that gap for the axioms the **flagship verified-numerics results**
actually depend on (the PID capstone, the forward/backward-error algebra, the
condition-number bound, interval arithmetic, the contraction certificate) — by
exhibiting a **model**.

The closure of those results (taken from their `#print axioms`) is an *ordered
commutative ring with `abs`* — `MachLib.Real`'s field/order/`abs` axioms, with no
division and no transcendentals. We bundle exactly that closure as `RealCoreSpec`
and give it **two** instances:

* `machlibWitness : RealCoreSpec` over `MachLib.Real` — **faithfulness.** It
  compiles *only if* every spec field is discharged by an actual MachLib axiom, so
  the spec is provably *no stronger* than what MachLib assumes. (If a field were
  stronger than the real axiom, `:= MachLib.Real.<axiom>` would fail to typecheck.)
  `#print axioms machlibWitness` enumerates exactly the flagship closure — the
  ordered-comm-ring-with-`abs` axioms; as more of those `abs` facts become theorems
  (the audit), the closure shifts to the finer order axioms they rest on (e.g.
  `lt_irrefl_ax`), all of which are spec fields here.
* `intModel : RealCoreSpec` over `Int` — **consistency.** `ℤ` is an ordered
  commutative ring with `abs`, so every axiom in the closure holds in it. This
  instance is built purely from Lean-core `Int` lemmas; `#print axioms intModel`
  shows it depends on **none** of `MachLib.Real`'s axioms (only Lean's own
  `propext`/`Quot.sound`/`Classical.choice`).

Together: the flagship closure is satisfied by `ℤ` ⇒ it cannot prove `False` ⇒ the
flagship results are **not vacuous**. The full 292-axiom base additionally needs
the *field* axioms (`mul_inv`, `div`) and the *analytic* axioms (`sin`/`cos`/`exp`,
derivatives, MVT); those are modelled by `ℝ` (Mathlib), not by `ℤ` — which is
exactly why they are separate axioms — and are out of this Mathlib-free file's
scope. The division-free, transcendental-free spine — the part the moat results
ride on — is machine-checked consistent here, and re-checked on every build.

`sorryAx`-free; `intModel` is Mathlib-free (Lean-core `Int` only).
-/

namespace MachLib.Model

/-- The flagship axiom closure as a bundle: an ordered commutative ring with `abs`.
Every field is a verbatim transcription of a `MachLib.Real` axiom (with the opaque
operations abstracted to the structure's own fields, so the statements carry no
notation/instance coupling). A *model* is any inhabitant of this type. -/
structure RealCoreSpec where
  R    : Type
  add  : R → R → R
  mul  : R → R → R
  neg  : R → R
  sub  : R → R → R
  lt   : R → R → Prop
  le   : R → R → Prop
  zero : R
  one  : R
  abs  : R → R
  -- commutative-ring axioms
  add_comm    : ∀ a b, add a b = add b a
  add_assoc   : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero    : ∀ a, add a zero = a
  add_neg     : ∀ a, add a (neg a) = zero
  mul_comm    : ∀ a b, mul a b = mul b a
  mul_assoc   : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one     : ∀ a, mul a one = a
  mul_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  neg_mul     : ∀ a b, mul (neg a) b = neg (mul a b)
  mul_neg     : ∀ a b, mul a (neg b) = neg (mul a b)
  neg_neg     : ∀ a, neg (neg a) = a
  sub_def     : ∀ a b, sub a b = add a (neg b)
  -- order axioms
  lt_total           : ∀ a b, lt a b ∨ a = b ∨ lt b a
  lt_trans           : ∀ a b c, lt a b → lt b c → lt a c
  lt_irrefl          : ∀ a, ¬ lt a a
  le_iff_lt_or_eq    : ∀ a b, le a b ↔ lt a b ∨ a = b
  add_lt_add_left    : ∀ a b c, lt a b → lt (add c a) (add c b)
  mul_pos            : ∀ a b, lt zero a → lt zero b → lt zero (mul a b)
  mul_lt_mul_pos_rht : ∀ a b c, lt a b → lt zero c → lt (mul a c) (mul b c)
  zero_lt_one        : lt zero one
  -- abs axioms
  abs_neg : ∀ x, abs (neg x) = abs x
  abs_add : ∀ a b, le (abs (add a b)) (add (abs a) (abs b))
  abs_mul : ∀ a b, abs (mul a b) = mul (abs a) (abs b)

/-- **Faithfulness.** `MachLib.Real` with its own axioms inhabits the spec — so the
spec is no stronger than what MachLib assumes. Each field is the corresponding
`MachLib.Real` axiom; this `def` typechecks only because the transcription matches. -/
noncomputable def machlibWitness : RealCoreSpec where
  R    := MachLib.Real
  add  := MachLib.Real.addR
  mul  := MachLib.Real.mulR
  neg  := MachLib.Real.negR
  sub  := MachLib.Real.subR
  lt   := MachLib.Real.ltR
  le   := MachLib.Real.leR
  zero := MachLib.Real.zeroR
  one  := MachLib.Real.oneR
  abs  := MachLib.Real.abs
  add_comm    := MachLib.Real.add_comm
  add_assoc   := MachLib.Real.add_assoc
  add_zero    := MachLib.Real.add_zero
  add_neg     := MachLib.Real.add_neg
  mul_comm    := MachLib.Real.mul_comm
  mul_assoc   := MachLib.Real.mul_assoc
  mul_one     := MachLib.Real.mul_one_ax
  mul_distrib := MachLib.Real.mul_distrib
  neg_mul     := MachLib.Real.neg_mul
  mul_neg     := MachLib.Real.mul_neg
  neg_neg     := MachLib.Real.neg_neg_helper
  sub_def     := MachLib.Real.sub_def
  lt_total    := MachLib.Real.lt_total
  lt_trans    := fun _ _ _ => MachLib.Real.lt_trans_ax
  lt_irrefl   := MachLib.Real.lt_irrefl_ax
  le_iff_lt_or_eq := MachLib.Real.le_iff_lt_or_eq
  add_lt_add_left := fun _ _ c h => MachLib.Real.add_lt_add_left h c
  mul_pos     := fun _ _ => MachLib.Real.mul_pos
  mul_lt_mul_pos_rht := fun _ _ _ h hc => MachLib.Real.mul_lt_mul_of_pos_right h hc
  zero_lt_one := MachLib.Real.zero_lt_one_ax
  abs_neg     := MachLib.Real.abs_neg
  abs_add     := MachLib.Real.abs_add
  abs_mul     := MachLib.Real.abs_mul

/-- **Consistency.** `ℤ` — an ordered commutative ring with `abs := |·|` (via
`Int.natAbs`) — satisfies every axiom in the closure. Built only from Lean-core
`Int` lemmas, so it depends on none of MachLib's axioms: a genuine external model.
Its existence proves the flagship closure cannot derive `False`. -/
def intModel : RealCoreSpec where
  R    := Int
  add  := fun a b => a + b
  mul  := fun a b => a * b
  neg  := fun a => -a
  sub  := fun a b => a - b
  lt   := fun a b => a < b
  le   := fun a b => a ≤ b
  zero := (0 : Int)
  one  := (1 : Int)
  abs  := fun x => (x.natAbs : Int)
  add_comm    := fun a b => by dsimp only; omega
  add_assoc   := fun a b c => by dsimp only; omega
  add_zero    := fun a => by dsimp only; omega
  add_neg     := fun a => by dsimp only; omega
  mul_comm    := Int.mul_comm
  mul_assoc   := Int.mul_assoc
  mul_one     := Int.mul_one
  mul_distrib := Int.mul_add
  neg_mul     := Int.neg_mul
  mul_neg     := Int.mul_neg
  neg_neg     := Int.neg_neg
  sub_def     := fun a b => by dsimp only; omega
  lt_total    := fun a b => by dsimp only; omega
  lt_trans    := fun a b c => by dsimp only; omega
  lt_irrefl   := fun a => by dsimp only; omega
  le_iff_lt_or_eq := fun a b => by dsimp only; omega
  add_lt_add_left := fun a b c => by dsimp only; omega
  mul_pos     := fun _ _ => Int.mul_pos
  mul_lt_mul_pos_rht := fun _ _ _ h hc => Int.mul_lt_mul_of_pos_right h hc
  zero_lt_one := by dsimp only; omega
  abs_neg := fun x => by
    show ((-x).natAbs : Int) = (x.natAbs : Int); rw [Int.natAbs_neg]
  abs_add := fun a b => by
    show ((a + b).natAbs : Int) ≤ (a.natAbs : Int) + (b.natAbs : Int)
    exact_mod_cast Int.natAbs_add_le a b
  abs_mul := fun a b => by
    show ((a * b).natAbs : Int) = (a.natAbs : Int) * (b.natAbs : Int)
    rw [Int.natAbs_mul]; exact_mod_cast rfl

end MachLib.Model
