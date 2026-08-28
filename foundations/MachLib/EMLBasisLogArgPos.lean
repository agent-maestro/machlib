import MachLib.EMLBasisEquivalence
import MachLib.EMLEncoderAnalytic
import MachLib.EMLZeroBoundAssembly

/-!
# `LogArgPosOn` through the change of basis — what the encoder needs from `toEML`

`EMLBasisEquivalence` proves `L_F ⊆ EML` (`toEML`, `toEML_eval`) and `EMLZeroBoundAssembly` gives an
explicit interval-independent zero bound for any EML tree (`encBound`, `encBound_bounds`). **Nothing
connects them**, because `encBound_bounds` needs `LogArgPosOn t (Icc a b)` — every `eml` node's log
argument positive — and no result says when `toEML T` has it.

That gap is what stops the query-vein germ `bipev N x (Fbasis (pev P x / pev Q x))` from being fed to
the explicit descent, and it is the last structural step of
`oneQueryDichotomy_of_uniformBoundsFrom`'s antecedent.

## The observation that makes this mechanical

**At every generator, the `LogArgPosOn` side condition is exactly the `eval` side condition already
carried.** `subTree_eval` needs `0 < a.eval x`; so does `LogArgPosOn (subTree a b)`. `mulPos_eval`
needs both factors positive; so does `LogArgPosOn (mulPos a b)`. `mulTree_eval` needs `1 < a.eval x`;
so does `LogArgPosOn (mulTree a b)`. Nothing new has to be discovered about the constructions — the
positivity a generator needs to *compute* the right value is the positivity it needs to keep its logs
in range.

The consequence is the useful part: the **`Gen` layer is unconditional**. `subGen`, `addGen`,
`mulGen`, `negGen` all shift through `domTree u = exp (1 − u)`, whose value is positive for a
structural reason, so their `LogArgPosOn` obligations discharge with no hypothesis on `u` or `v` at
all — exactly mirroring why `EMLRingClosure` could drop the positivity hypotheses from `+`, `−`, `×`.

**So the only place positivity is genuinely needed is `FTree`**, through `logTree`: `F`'s argument
must be positive. Which is the honest answer to "when can the query germ be fed to the encoder" —
when `pev P x / pev Q x > 0` on the interval, and nowhere else does the question arise.

## Scope

The whole stack, up to `logArgPosOn_toEML`. What it does **not** do is discharge `FArgsPos` for the
query germ — that is a statement about `pev P x / pev Q x` being positive on a ray, and belongs with
the germ construction rather than here.
-/

namespace MachLib

open Real

/-- `expOf t = eml t (const 1)`: the log argument is the constant `1`. -/
theorem logArgPosOn_expOf (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S) :
    LogArgPosOn (expOf t) S :=
  ⟨h, True.intro, fun _ _ => zero_lt_one_ax⟩

/-- `negOffset c t = eml (const c) (expOf t)`: the log argument is `exp (t x)`, positive structurally. -/
theorem logArgPosOn_negOffset (c : Real) (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S) :
    LogArgPosOn (negOffset c t) S :=
  ⟨True.intro, logArgPosOn_expOf t S h, fun x _ => by rw [expOf_eval]; exact exp_pos _⟩

/-- **`domTree` is unconditional.** `exp (1 − t)` needs nothing of `t` beyond `t`'s own logs — which
is the whole reason the `Gen` layer below can drop its positivity hypotheses. -/
theorem logArgPosOn_domTree (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S) :
    LogArgPosOn (domTree t) S :=
  logArgPosOn_expOf _ S (logArgPosOn_negOffset 0 t S h)

/-- **`logTree` is where positivity is genuinely required**, and the requirement is exactly
`logTree`'s own argument — the same condition its *value* lemma does not need (the totalised `log`
makes `logTree_eval` unconditional) but its *chain encoding* does. -/
theorem logArgPosOn_logTree (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S)
    (hpos : ∀ x : Real, S x → 0 < t.eval x) :
    LogArgPosOn (logTree t) S :=
  logArgPosOn_negOffset 0 _ S ⟨True.intro, h, hpos⟩

/-- `subTree a b = eml (logTree a) (expOf b)`: needs `a` positive, matching `subTree_eval`. -/
theorem logArgPosOn_subTree (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (hpos : ∀ x : Real, S x → 0 < a.eval x) :
    LogArgPosOn (subTree a b) S :=
  ⟨logArgPosOn_logTree a S ha hpos, logArgPosOn_expOf b S hb,
   fun x _ => by rw [expOf_eval]; exact exp_pos _⟩

/-- `addTree a b`: two `negOffset` wrappers over a `subTree`, so again exactly `a` positive. -/
theorem logArgPosOn_addTree (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (hpos : ∀ x : Real, S x → 0 < a.eval x) :
    LogArgPosOn (addTree a b) S :=
  logArgPosOn_negOffset _ _ S (logArgPosOn_negOffset 0 _ S
    (logArgPosOn_subTree a (negOffset 0 b) S ha (logArgPosOn_negOffset 0 b S hb) hpos))

/-- **The shift is `LogArgPosOn`-safe with no hypothesis**, because `domTree u` is positive
structurally. This is the lemma the whole `Gen` layer rests on. -/
theorem logArgPosOn_shift (u : EMLTree) (S : RealSet) (h : LogArgPosOn u S) :
    LogArgPosOn (addTree (domTree u) u) S :=
  logArgPosOn_addTree _ u S (logArgPosOn_domTree u S h) h
    (fun x _ => by rw [domTree_eval]; exact exp_pos _)

/-! ## The `Gen` layer — unconditional, because every shift is through `domTree` -/

/-- **`subGen` needs nothing.** Its `subTree` is applied to the shift, whose positivity is
`shift_pos`, so no hypothesis on `u` or `v` survives. -/
theorem logArgPosOn_subGen (u v : EMLTree) (S : RealSet)
    (hu : LogArgPosOn u S) (hv : LogArgPosOn v S) : LogArgPosOn (subGen u v) S :=
  logArgPosOn_subTree _ _ S (logArgPosOn_shift u S hu)
    (logArgPosOn_addTree _ v S (logArgPosOn_domTree u S hu) hv
      (fun x _ => by rw [domTree_eval]; exact exp_pos _))
    (fun x _ => shift_pos u x)

/-- **`addGen` likewise.** -/
theorem logArgPosOn_addGen (u v : EMLTree) (S : RealSet)
    (hu : LogArgPosOn u S) (hv : LogArgPosOn v S) : LogArgPosOn (addGen u v) S :=
  logArgPosOn_subGen _ _ S
    (logArgPosOn_addTree _ v S (logArgPosOn_shift u S hu) hv (fun x _ => shift_pos u x))
    (logArgPosOn_domTree u S hu)

/-- **`negGen` likewise.** -/
theorem logArgPosOn_negGen (u : EMLTree) (S : RealSet) (hu : LogArgPosOn u S) :
    LogArgPosOn (negGen u) S :=
  logArgPosOn_subGen _ u S True.intro hu

/-! ## The positive-argument layer — where the side conditions match the value lemmas exactly -/

/-- `mulTree a b = expOf (addTree (logTree a) (logTree b))`: needs `1 < a` and `0 < b`, which is
`mulTree_eval`'s hypothesis pair verbatim. -/
theorem logArgPosOn_mulTree (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (ha1 : ∀ x : Real, S x → 1 < a.eval x) (hb0 : ∀ x : Real, S x → 0 < b.eval x) :
    LogArgPosOn (mulTree a b) S := by
  have ha0 : ∀ x : Real, S x → 0 < a.eval x :=
    fun x hx => lt_trans_ax zero_lt_one_ax (ha1 x hx)
  refine logArgPosOn_expOf _ S (logArgPosOn_addTree _ _ S
    (logArgPosOn_logTree a S ha ha0) (logArgPosOn_logTree b S hb hb0) ?_)
  intro x hx
  rw [logTree_eval]
  have h1 : Real.log 1 = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  have := log_lt_log zero_lt_one_ax (ha1 x hx)
  rw [h1] at this; exact this

/-- `mulPos a b`: both factors positive — `mulPos_eval`'s hypotheses, again verbatim. -/
theorem logArgPosOn_mulPos (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (ha0 : ∀ x : Real, S x → 0 < a.eval x) (hb0 : ∀ x : Real, S x → 0 < b.eval x) :
    LogArgPosOn (mulPos a b) S := by
  have hone : LogArgPosOn (EMLTree.const 1) S := True.intro
  have hA1 : LogArgPosOn (addTree a (EMLTree.const 1)) S :=
    logArgPosOn_addTree a _ S ha hone ha0
  have hB1 : LogArgPosOn (addTree b (EMLTree.const 1)) S :=
    logArgPosOn_addTree b _ S hb hone hb0
  have hAv : ∀ x : Real, S x → 1 < (addTree a (EMLTree.const 1)).eval x := by
    intro x hx
    rw [addTree_eval _ (ha0 x hx)]
    have v := add_lt_add_left (ha0 x hx) (1 : Real)
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : (1 : Real) + a.eval x = a.eval x + (EMLTree.const 1).eval x := by
      show (1 : Real) + a.eval x = a.eval x + 1
      mach_ring
    rw [e1, e2] at v; exact v
  have hBv : ∀ x : Real, S x → 0 < (addTree b (EMLTree.const 1)).eval x := by
    intro x hx
    rw [addTree_eval _ (hb0 x hx)]
    show (0 : Real) < b.eval x + 1
    exact add_pos (hb0 x hx) zero_lt_one_ax
  have hab : LogArgPosOn (addTree a b) S := logArgPosOn_addTree a b S ha hb ha0
  have habv : ∀ x : Real, S x → 0 < (addTree a b).eval x := by
    intro x hx; rw [addTree_eval _ (ha0 x hx)]; exact add_pos (ha0 x hx) (hb0 x hx)
  refine logArgPosOn_subTree _ _ S
    (logArgPosOn_mulTree _ _ S hA1 hB1 hAv hBv)
    (logArgPosOn_addTree _ _ S hab hone habv) ?_
  intro x hx
  rw [mulTree_eval (hAv x hx) (hBv x hx)]
  exact mul_pos (lt_trans_ax zero_lt_one_ax (hAv x hx)) (hBv x hx)

/-- `invPos t`: the reciprocal of a positive tree, needing exactly that. -/
theorem logArgPosOn_invPos (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S)
    (hpos : ∀ x : Real, S x → 0 < t.eval x) : LogArgPosOn (invPos t) S :=
  logArgPosOn_expOf _ S (logArgPosOn_negGen _ S (logArgPosOn_logTree t S h hpos))

/-! ## `mulL`, `mulGen`, `divGen`, `FTree` -/

/-- `mulL a b`: only the left factor positive, matching `mulL_eval`. -/
theorem logArgPosOn_mulL (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (ha0 : ∀ x : Real, S x → 0 < a.eval x) : LogArgPosOn (mulL a b) S := by
  have hdb : LogArgPosOn (domTree b) S := logArgPosOn_domTree b S hb
  have hdbv : ∀ x : Real, S x → 0 < (domTree b).eval x :=
    fun x _ => by rw [domTree_eval]; exact exp_pos _
  have hsh : LogArgPosOn (addTree (domTree b) b) S := logArgPosOn_shift b S hb
  refine logArgPosOn_subTree _ _ S
    (logArgPosOn_mulPos a _ S ha hsh ha0 (fun x _ => shift_pos b x))
    (logArgPosOn_mulPos a _ S ha hdb ha0 hdbv) ?_
  intro x hx
  rw [mulPos_eval (ha0 x hx) (shift_pos b x)]
  exact mul_pos (ha0 x hx) (shift_pos b x)

/-- **`mulGen` is unconditional**, like the rest of the `Gen` layer. -/
theorem logArgPosOn_mulGen (u v : EMLTree) (S : RealSet)
    (hu : LogArgPosOn u S) (hv : LogArgPosOn v S) : LogArgPosOn (mulGen u v) S :=
  logArgPosOn_subGen _ _ S
    (logArgPosOn_mulL _ v S (logArgPosOn_shift u S hu) hv (fun x _ => shift_pos u x))
    (logArgPosOn_mulL _ v S (logArgPosOn_domTree u S hu) hv
      (fun x _ => by rw [domTree_eval]; exact exp_pos _))

/-- `divGen a b`: needs only `b ≠ 0`, since the reciprocal is taken of `b²` — positive for a
structural reason, exactly as `divGen_eval` has it. -/
theorem logArgPosOn_divGen (a b : EMLTree) (S : RealSet)
    (ha : LogArgPosOn a S) (hb : LogArgPosOn b S)
    (hne : ∀ x : Real, S x → b.eval x ≠ 0) : LogArgPosOn (divGen a b) S := by
  have hsq : LogArgPosOn (mulGen b b) S := logArgPosOn_mulGen b b S hb hb
  have hsqv : ∀ x : Real, S x → 0 < (mulGen b b).eval x := by
    intro x hx; rw [mulGen_eval]; exact mul_self_pos (hne x hx)
  exact logArgPosOn_mulGen a _ S ha
    (logArgPosOn_mulGen b _ S hb (logArgPosOn_invPos _ S hsq hsqv))

/-- **`FTree` is the only place positivity is genuinely required.** `F`'s argument must be positive —
everything else in the translation shifts through `domTree`. -/
theorem logArgPosOn_FTree (t : EMLTree) (S : RealSet) (h : LogArgPosOn t S)
    (hpos : ∀ x : Real, S x → 0 < t.eval x) : LogArgPosOn (FTree t) S :=
  logArgPosOn_addGen _ _ S (logArgPosOn_expOf t S h) (logArgPosOn_logTree t S h hpos)

/-! ## The capstone: `LogArgPosOn (toEML T)`

`DivSafe` is `toEML_eval`'s existing side condition (no division by zero). `FArgsPos` is the new one,
and by the analysis above it says **only** what `F`'s arguments must satisfy — every other constructor
contributes nothing, because the `Gen` layer shifts through `domTree`. -/

/-- **The `F`-argument condition.** Mirrors `DivSafe`'s shape, and is `True` at every node except
`F`, where it demands what `logTree` needs. -/
def FArgsPos : FTerm → RealSet → Prop
  | .const _, _ => True
  | .var,     _ => True
  | .add a b, S => FArgsPos a S ∧ FArgsPos b S
  | .sub a b, S => FArgsPos a S ∧ FArgsPos b S
  | .mul a b, S => FArgsPos a S ∧ FArgsPos b S
  | .div a b, S => FArgsPos a S ∧ FArgsPos b S
  | .F a,     S => FArgsPos a S ∧ (∀ x : Real, S x → 0 < FTerm.eval a x)

/-- **`toEML` preserves `LogArgPosOn`, given only `F`-argument positivity.**

This is the missing link between `EMLBasisEquivalence` (`L_F ⊆ EML`) and `EMLZeroBoundAssembly`
(`encBound_bounds`): with it, any `L_F` term whose `F`-arguments are positive on `Icc a b` and whose
divisions are safe there inherits the explicit, interval-independent zero bound `encBound (toEML T)`.

The proof is a structural induction in which **five of the seven cases carry no positivity at all** —
`const`, `var`, `add`, `sub`, `mul` discharge from the `Gen` lemmas above with nothing but the
inductive hypotheses. `div` needs its denominator nonzero, which `DivSafe` already carries. Only `F`
consumes `FArgsPos`. -/
theorem logArgPosOn_toEML : ∀ (T : FTerm) (S : RealSet),
    (∀ x : Real, S x → DivSafe T x) → FArgsPos T S → LogArgPosOn (toEML T) S := by
  intro T
  induction T with
  | const c => intro _ _ _; exact True.intro
  | var => intro _ _ _; exact True.intro
  | add a b iha ihb =>
      intro S hd ⟨hfa, hfb⟩
      exact logArgPosOn_addGen _ _ S
        (iha S (fun x hx => (hd x hx).1) hfa) (ihb S (fun x hx => (hd x hx).2) hfb)
  | sub a b iha ihb =>
      intro S hd ⟨hfa, hfb⟩
      exact logArgPosOn_subGen _ _ S
        (iha S (fun x hx => (hd x hx).1) hfa) (ihb S (fun x hx => (hd x hx).2) hfb)
  | mul a b iha ihb =>
      intro S hd ⟨hfa, hfb⟩
      exact logArgPosOn_mulGen _ _ S
        (iha S (fun x hx => (hd x hx).1) hfa) (ihb S (fun x hx => (hd x hx).2) hfb)
  | div a b iha ihb =>
      intro S hd ⟨hfa, hfb⟩
      refine logArgPosOn_divGen _ _ S
        (iha S (fun x hx => (hd x hx).1) hfa) (ihb S (fun x hx => (hd x hx).2.1) hfb) ?_
      intro x hx
      rw [toEML_eval b x (hd x hx).2.1]
      exact (hd x hx).2.2
  | F a iha =>
      intro S hd ⟨hfa, hpos⟩
      refine logArgPosOn_FTree _ S (iha S (fun x hx => hd x hx) hfa) ?_
      intro x hx
      rw [toEML_eval a x (hd x hx)]
      exact hpos x hx

/-! ## The payoff: an explicit, interval-independent zero bound for `L_F` terms

`encBound (toEML T)` is a `Nat` built from the translated tree alone — no `a`, no `b`. So this is the
`UniformZeroBoundFrom`-shaped statement that `oneQueryDichotomy_of_uniformBoundsFrom`'s antecedent
asks for, once the germ is exhibited as an `FTerm` with positive `F`-arguments on a ray. -/

/-- **Any `L_F` term inherits the explicit bound.** Divisions safe and `F`-arguments positive on
`Icc a b`, plus a nonzero witness, give a zero count bounded by `encBound (toEML T)` — a function of
the term alone.

Note where each hypothesis is consumed: `hd` twice (once for `logArgPosOn_toEML`, once to transport
each zero across `toEML_eval`), `hf` only inside `logArgPosOn_toEML`, and `hab`/`hne` only by
`encBound_bounds`. -/
theorem fterm_encBound_bounds (T : FTerm) (a b : Real) (hab : a < b)
    (hd : ∀ x : Real, Icc a b x → DivSafe T x)
    (hf : FArgsPos T (Icc a b))
    (hne : ∃ z : Real, a < z ∧ z < b ∧ FTerm.eval T z ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ FTerm.eval T z = 0) →
      zeros.length ≤ encBound (toEML T) := by
  have hmem : ∀ z : Real, a < z → z < b → Icc a b z :=
    fun z h1 h2 => ⟨le_of_lt h1, le_of_lt h2⟩
  have hlog : LogArgPosOn (toEML T) (Icc a b) := logArgPosOn_toEML T (Icc a b) hd hf
  have hne' : ∃ z : Real, a < z ∧ z < b ∧ (toEML T).eval z ≠ 0 := by
    obtain ⟨z, hz1, hz2, hz0⟩ := hne
    exact ⟨z, hz1, hz2, by rw [toEML_eval T z (hd z (hmem z hz1 hz2))]; exact hz0⟩
  intro zeros hnd hz
  refine encBound_bounds (toEML T) a b hab hlog hne' zeros hnd ?_
  intro z hzmem
  obtain ⟨h1, h2, h0⟩ := hz z hzmem
  exact ⟨h1, h2, by rw [toEML_eval T z (hd z (hmem z h1 h2))]; exact h0⟩

end MachLib
