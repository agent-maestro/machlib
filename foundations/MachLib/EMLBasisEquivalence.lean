import MachLib.EMLUnaryBasis
import MachLib.EMLDerivClosure

/-!
# Change of basis: `L_F ⊆ EML`, the reverse translation

`EMLUnaryBasis.lean` proves `EML ⊆ L_F` — every EML tree is computed at every real point by a term
over constants, the variable, the four field operations, and the single unary generator
`F(x) = exp x + log₀ x`. This file compiles back the other way.

**Most of the work was already done.** `EMLRingClosure.lean` shows EML is closed under `+`, `−` and
`×` with *no hypotheses*, via `domTree t = exp (1 − t)`: any subtree can be shifted into the positive
range by an EML-expressible amount and the shift removed afterwards, so the positivity side
conditions on `subTree`/`addTree`/`mulPos` were never about the class. `EMLDerivClosure.lean` adds
`invPos t = exp (−log t)`, the reciprocal of a *positive* tree.

So exactly one operation was missing: **division by a tree of unknown sign**. It follows from the
positive reciprocal by one identity,

```
a / b  =  a · b · (1 / b²),        b² > 0 wherever b ≠ 0
```

which is the same move as everywhere else in this arc — route the sign-indefinite quantity through a
quantity that is positive for a structural reason, here `b²` rather than `exp`.

The nonzero-denominator condition is the one side condition that does *not* lift, and it is a
property of the `L_F` term rather than of the encoding: `a / b` has no value to reproduce where `b`
vanishes.
-/

namespace MachLib

open Real

/-! ## The one missing operation: division -/

private theorem sq_pos_of_ne {b : Real} (hb : b ≠ 0) : 0 < b * b := by
  rcases lt_total 0 b with h | h | h
  · exact mul_pos h h
  · exact absurd h.symm hb
  · have v := add_lt_add_left h (-b)
    have l : -b + b = 0 := by mach_ring
    have r : -b + 0 = -b := by mach_ring
    rw [l, r] at v
    have hp := mul_pos v v
    have e : -b * -b = b * b := by mach_ring
    rw [e] at hp; exact hp

private theorem inv_unique {b z : Real} (hb : b ≠ 0) (h : z * b = 1) : z = 1 / b := by
  have e0 : z = z * (b * (1 / b)) := by rw [mul_inv b hb]; mach_ring
  have e : z * (b * (1 / b)) = z * b * (1 / b) := by mach_mpoly [z, b, (1 : Real) / b]
  rw [e0, e, h]; mach_ring

private theorem inv_via_sq {b : Real} (hb : b ≠ 0) : b * (1 / (b * b)) = 1 / b := by
  have hbb : b * b ≠ 0 := ne_of_gt (sq_pos_of_ne hb)
  refine inv_unique hb ?_
  have e : b * (1 / (b * b)) * b = b * b * (1 / (b * b)) := by
    mach_mpoly [b, (1 : Real) / (b * b)]
  rw [e, mul_inv _ hbb]

/-- **Division by a tree of unknown sign**, wherever it is nonzero: `a / b = a · b · (1/b²)`. The
reciprocal is taken of `b²`, which is positive for a structural reason rather than an assumed one. -/
noncomputable def divGen (a b : EMLTree) : EMLTree :=
  mulGen a (mulGen b (invPos (mulGen b b)))

theorem divGen_eval {a b : EMLTree} {x : Real} (hb : b.eval x ≠ 0) :
    (divGen a b).eval x = a.eval x / b.eval x := by
  have hsq : 0 < (mulGen b b).eval x := by rw [mulGen_eval]; exact sq_pos_of_ne hb
  rw [divGen, mulGen_eval, mulGen_eval, invPos_eval hsq, mulGen_eval, inv_via_sq hb]
  exact (div_def _ _ hb).symm

/-- The generator itself, as an EML tree. `F` is an EML function — this is what keeps the change of
basis inside the theory rather than importing an oracle. -/
noncomputable def FTree (t : EMLTree) : EMLTree := addGen (expOf t) (logTree t)

theorem FTree_eval (t : EMLTree) (x : Real) : (FTree t).eval x = Fbasis (t.eval x) := by
  rw [FTree, addGen_eval, expOf_eval, logTree_eval]; rfl

/-! ## The reverse translation -/

/-- Every `L_F` term compiled back to an EML tree, one clause per constructor. -/
noncomputable def toEML : FTerm → EMLTree
  | .const c => .const c
  | .var     => .var
  | .add a b => addGen (toEML a) (toEML b)
  | .sub a b => subGen (toEML a) (toEML b)
  | .mul a b => mulGen (toEML a) (toEML b)
  | .div a b => divGen (toEML a) (toEML b)
  | .F a     => FTree (toEML a)

/-- The only side condition: at `x`, no division in the term divides by zero. -/
def DivSafe : FTerm → Real → Prop
  | .const _, _ => True
  | .var,     _ => True
  | .add a b, x => DivSafe a x ∧ DivSafe b x
  | .sub a b, x => DivSafe a x ∧ DivSafe b x
  | .mul a b, x => DivSafe a x ∧ DivSafe b x
  | .div a b, x => DivSafe a x ∧ DivSafe b x ∧ FTerm.eval b x ≠ 0
  | .F a,     x => DivSafe a x

/-- **`L_F ⊆ EML`.** Every `L_F` term is computed by an EML tree at every point where its divisions
are defined. The tree does not depend on the point. -/
theorem toEML_eval : ∀ (T : FTerm) (x : Real), DivSafe T x →
    (toEML T).eval x = FTerm.eval T x := by
  intro T
  induction T with
  | const c => intro _ _; rfl
  | var => intro _ _; rfl
  | add a b iha ihb =>
      intro x h
      obtain ⟨ha, hb⟩ := h
      rw [toEML, addGen_eval, iha x ha, ihb x hb]; rfl
  | sub a b iha ihb =>
      intro x h
      obtain ⟨ha, hb⟩ := h
      rw [toEML, subGen_eval, iha x ha, ihb x hb]; rfl
  | mul a b iha ihb =>
      intro x h
      obtain ⟨ha, hb⟩ := h
      rw [toEML, mulGen_eval, iha x ha, ihb x hb]; rfl
  | div a b iha ihb =>
      intro x h
      obtain ⟨ha, hb, hne⟩ := h
      have hbv : (toEML b).eval x ≠ 0 := by rw [ihb x hb]; exact hne
      rw [toEML, divGen_eval hbv, iha x ha, ihb x hb]; rfl
  | F a iha =>
      intro x h
      rw [toEML, FTree_eval, iha x h]; rfl

/-- **Discrimination: division is the only thing `DivSafe` guards.** A term with no division at all
translates unconditionally — so the hypothesis in `toEML_eval` is not doing hidden work for the
other five constructors. -/
theorem toEML_eval_div_free (T : FTerm) (hd : ∀ x : Real, DivSafe T x) (x : Real) :
    (toEML T).eval x = FTerm.eval T x := toEML_eval T x (hd x)
/-! ## The emitted `L_F` term never divides by zero

The reverse direction carries `DivSafe` as a hypothesis, so the *forward* direction has to discharge
it: the terms `toFTerm` emits must be shown safe. They are, and for structural reasons — `EFall`
divides only by `EF(u² + 1)`, whose value is `exp(u² + 1) > 0`, and the division inside `EF` itself
has denominator `exp(2w) − exp(w)` with `w > 0`. -/

private theorem two_pos' : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax

/-- The denominator inside `EF u` is `exp(2w) − exp(w)`, nonzero because `w > 0` forces
`exp w > 1`. -/
theorem EF_denom_ne_zero {u : FTerm} {x : Real} (hp : 0 < FTerm.eval u x) :
    FTerm.eval (FTerm.sub (FTerm.sub (FTerm.F (FTerm.mul (FTerm.const (1 + 1)) u)) (FTerm.F u))
      (FTerm.const (log (1 + 1)))) x ≠ 0 := by
  have hval : FTerm.eval (FTerm.sub (FTerm.sub (FTerm.F (FTerm.mul (FTerm.const (1 + 1)) u))
      (FTerm.F u)) (FTerm.const (log (1 + 1)))) x
      = exp ((1 + 1) * FTerm.eval u x) - exp (FTerm.eval u x) :=
    dilation_diff (1 + 1) (FTerm.eval u x) two_pos' hp
  have e2 : exp ((1 + 1) * FTerm.eval u x) = exp (FTerm.eval u x) * exp (FTerm.eval u x) := by
    have hx2 : (1 + 1) * FTerm.eval u x = FTerm.eval u x + FTerm.eval u x := by mach_ring
    rw [hx2, exp_add]
  rw [hval, e2]
  refine ne_of_gt ?_
  have hy : 1 < exp (FTerm.eval u x) := one_lt_exp hp
  have hp2 : (0 : Real) < exp (FTerm.eval u x) * (exp (FTerm.eval u x) - 1) :=
    mul_pos (lt_trans_ax zero_lt_one_ax hy) (sub_pos_of_lt hy)
  have e : exp (FTerm.eval u x) * (exp (FTerm.eval u x) - 1)
      = exp (FTerm.eval u x) * exp (FTerm.eval u x) - exp (FTerm.eval u x) := by
    mach_mpoly [exp (FTerm.eval u x)]
  rw [e] at hp2; exact hp2

theorem EF_divSafe {u : FTerm} {x : Real} (hu : DivSafe u x) (hp : 0 < FTerm.eval u x) :
    DivSafe (FTerm.EF u) x :=
  ⟨⟨⟨⟨⟨True.intro, hu⟩, hu⟩, True.intro⟩, ⟨⟨⟨True.intro, hu⟩, hu⟩, True.intro⟩,
    EF_denom_ne_zero hp⟩, True.intro⟩

theorem EFall_divSafe {u : FTerm} {x : Real} (hu : DivSafe u x) :
    DivSafe (FTerm.EFall u) x := by
  have hq : 0 < FTerm.eval (FTerm.add (FTerm.mul u u) (FTerm.const 1)) x :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one_ax
  have hpn : 0 < FTerm.eval (FTerm.add (FTerm.add u (FTerm.mul u u)) (FTerm.const 1)) x := by
    have hq2 := quad_pos (FTerm.eval u x)
    have e : FTerm.eval u x * FTerm.eval u x + FTerm.eval u x + 1
        = FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by mach_ring
    rw [e] at hq2; exact hq2
  refine ⟨EF_divSafe ⟨⟨hu, ⟨hu, hu⟩⟩, True.intro⟩ hpn,
          EF_divSafe ⟨⟨hu, hu⟩, True.intro⟩ hq, ?_⟩
  rw [FTerm.EF_eval _ x hq]
  exact ne_of_gt (exp_pos _)

theorem LFall_divSafe {u : FTerm} {x : Real} (hu : DivSafe u x) :
    DivSafe (FTerm.LFall u) x := ⟨hu, EFall_divSafe hu⟩

theorem toFTerm_divSafe : ∀ (t : EMLTree) (x : Real), DivSafe (toFTerm t) x := by
  intro t
  induction t with
  | const c => intro _; exact True.intro
  | var => intro _; exact True.intro
  | eml a b iha ihb =>
      intro x
      exact ⟨EFall_divSafe (iha x), LFall_divSafe (ihb x)⟩

/-! ## The two classes are equal -/

/-- The function class generated by the EML grammar. -/
def EMLClass (f : Real → Real) : Prop := ∃ t : EMLTree, ∀ x : Real, t.eval x = f x

/-- The function class generated from constants and `x` by the four field operations and the single
unary generator `F(x) = exp x + log₀ x`, by terms whose divisions are everywhere defined. -/
def LFClass (f : Real → Real) : Prop :=
  ∃ T : FTerm, (∀ x : Real, DivSafe T x) ∧ ∀ x : Real, FTerm.eval T x = f x

/-- **Change of basis.** The totalised exponential–logarithmic function class admits a single unary
transcendental generator over the field operations:

```
EMLClass f  ↔  LFClass f
```

Neither direction assumes anything about signs, domains or rays. The generator is not an oracle
imported from outside the theory — `F` is itself an EML function (`FTree`), so this is a second
presentation of one semantic class rather than an extension of it. -/
theorem eml_class_eq_lf_class (f : Real → Real) : EMLClass f ↔ LFClass f := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨toFTerm t, toFTerm_divSafe t, fun x => (toFTerm_eval t x).trans (ht x)⟩
  · rintro ⟨T, hd, hT⟩
    exact ⟨toEML T, fun x => (toEML_eval T x (hd x)).trans (hT x)⟩

/-- **The `DivSafe` hypothesis is load-bearing, not decorative.** Where the denominator vanishes the
translated tree evaluates to `0` — for *every* numerator. Matching `a / b` there would therefore
require `a / 0 = 0` for all `a`, which MachLib's field axioms do not provide: `mul_inv` is stated
only for nonzero arguments, so `a / 0` is an unconstrained value. The condition is a fact about the
`L_F` term, and the translation cannot repair it. -/
theorem divGen_at_zero {a b : EMLTree} {x : Real} (hb : b.eval x = 0) :
    (divGen a b).eval x = 0 := by
  rw [divGen, mulGen_eval, mulGen_eval, hb]
  mach_ring

/-- `F` is in the class it generates — the statement that keeps the change of basis internal. -/
theorem F_mem_EMLClass : EMLClass Fbasis := ⟨FTree .var, fun x => FTree_eval .var x⟩

end MachLib
