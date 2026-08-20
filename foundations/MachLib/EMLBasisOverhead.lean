import MachLib.EMLGeneratorFamily
import MachLib.EMLCertifiedSynthesis

/-!
# Simulation overhead, both directions — and where the lower bounds run out

`EMLQueryComplexity.lean` measures the forward translation: `fDepth (toFTermFast t) = t.depth`,
**exactly**. This file measures the other one, and the two are not alike.

`toEML` pays EML depth for every **field operation**, because EML has no primitive `+`, `−`, `×` or
`÷` — each is a gadget costing a fixed number of levels (`EMLDepthCost.lean` records the numbers at
`var`: `subGen` 15, `addGen` 34, `mulGen` 54). So the reverse bound is a constant times the `L_F`
term's **syntactic height**, not its `F`-depth:

```
fDepth (toFTermFast t)   =  t.depth                      exact, no overhead
EMLTree.depth (toEML T)  ≤  400 · fHeight T              constant × height
```

The asymmetry is real and not an artefact of loose constants: `1/x` has `F`-depth `0` in `L_F` and
minimum EML depth **exactly 4** (`inv_x_min_depth`, certified), so no inequality
`d_EML ≤ C · d_F + D` can hold with `D < 4`, whatever `C` is.

**What is not proved here, and is the honest boundary of the whole arc:** whether that additive slack
is *bounded*. Every complexity statement in this development is an upper bound or an exact count of a
construction I wrote. The one lower bound available — `4 ≤ D` below — is imported from the EML side,
where the corpus's exclusion machinery reaches. On the `L_F` side there is no lower-bound machinery at
all: nothing here can show that a given function needs a positive number of `F`-queries, because that
requires proving a function is not rational, and the corpus has no route to it.
-/

set_option maxRecDepth 8000

namespace MachLib

open Real

/-! ## Depth of the EML gadgets, in general

`EMLDepthCost.lean` gives exact depths at `var`. These are the general bounds the composition needs;
the constants are **not** optimised, and are chosen to make the induction go through. -/

theorem subTree_depth_le (a b : EMLTree) : (subTree a b).depth ≤ 4 + max a.depth b.depth := by
  simp only [subTree, EMLTree.depth, logTree_depth, expOf_depth]; omega

theorem addTree_depth_le (a b : EMLTree) : (addTree a b).depth ≤ 12 + max a.depth b.depth := by
  rw [addTree, negOffset_depth, negOffset_depth]
  have h := subTree_depth_le a (negOffset 0 b)
  rw [negOffset_depth] at h
  omega

theorem mulTree_depth_le (a b : EMLTree) : (mulTree a b).depth ≤ 20 + max a.depth b.depth := by
  rw [mulTree, expOf_depth]
  have h := addTree_depth_le (logTree a) (logTree b)
  rw [logTree_depth, logTree_depth] at h
  omega

theorem mulPos_depth_le (a b : EMLTree) : (mulPos a b).depth ≤ 40 + max a.depth b.depth := by
  have hc : (EMLTree.const (1 : Real)).depth = 0 := rfl
  rw [mulPos]
  have h1 := subTree_depth_le (mulTree (addTree a (.const 1)) (addTree b (.const 1)))
      (addTree (addTree a b) (.const 1))
  have h2 := mulTree_depth_le (addTree a (.const 1)) (addTree b (.const 1))
  have h3 := addTree_depth_le a (EMLTree.const (1 : Real))
  have h4 := addTree_depth_le b (EMLTree.const (1 : Real))
  have h5 := addTree_depth_le (addTree a b) (EMLTree.const (1 : Real))
  have h6 := addTree_depth_le a b
  rw [hc] at h3 h4 h5
  omega

theorem subGen_depth_le (u v : EMLTree) : (subGen u v).depth ≤ 24 + max u.depth v.depth := by
  rw [subGen]
  have h1 := subTree_depth_le (addTree (domTree u) u) (addTree (domTree u) v)
  have h2 := addTree_depth_le (domTree u) u
  have h3 := addTree_depth_le (domTree u) v
  rw [domTree_depth] at h2 h3
  omega

theorem addGen_depth_le (u v : EMLTree) : (addGen u v).depth ≤ 56 + max u.depth v.depth := by
  rw [addGen]
  have h1 := subGen_depth_le (addTree (addTree (domTree u) u) v) (domTree u)
  have h2 := addTree_depth_le (addTree (domTree u) u) v
  have h3 := addTree_depth_le (domTree u) u
  rw [domTree_depth] at h1 h3
  omega

theorem mulL_depth_le (a b : EMLTree) : (mulL a b).depth ≤ 64 + max a.depth b.depth := by
  rw [mulL]
  have h1 := subTree_depth_le (mulPos a (addTree (domTree b) b)) (mulPos a (domTree b))
  have h2 := mulPos_depth_le a (addTree (domTree b) b)
  have h3 := mulPos_depth_le a (domTree b)
  have h4 := addTree_depth_le (domTree b) b
  rw [domTree_depth] at h3 h4
  omega

theorem mulGen_depth_le (u v : EMLTree) : (mulGen u v).depth ≤ 112 + max u.depth v.depth := by
  rw [mulGen]
  have h1 := subGen_depth_le (mulL (addTree (domTree u) u) v) (mulL (domTree u) v)
  have h2 := mulL_depth_le (addTree (domTree u) u) v
  have h3 := mulL_depth_le (domTree u) v
  have h4 := addTree_depth_le (domTree u) u
  rw [domTree_depth] at h3 h4
  omega

theorem negGen_depth_le (u : EMLTree) : (negGen u).depth ≤ 24 + u.depth := by
  have hc : (EMLTree.const (0 : Real)).depth = 0 := rfl
  rw [negGen]
  have h := subGen_depth_le (EMLTree.const (0 : Real)) u
  rw [hc] at h
  omega

theorem invPos_depth_le (t : EMLTree) : (invPos t).depth ≤ 28 + t.depth := by
  rw [invPos, expOf_depth]
  have h := negGen_depth_le (logTree t)
  rw [logTree_depth] at h
  omega

theorem divGen_depth_le (a b : EMLTree) : (divGen a b).depth ≤ 384 + max a.depth b.depth := by
  rw [divGen]
  have h1 := mulGen_depth_le a (mulGen b (invPos (mulGen b b)))
  have h2 := mulGen_depth_le b (invPos (mulGen b b))
  have h3 := invPos_depth_le (mulGen b b)
  have h4 := mulGen_depth_le b b
  omega

theorem FTree_depth_le (t : EMLTree) : (FTree t).depth ≤ 64 + t.depth := by
  rw [FTree]
  have h1 := addGen_depth_le (expOf t) (logTree t)
  rw [expOf_depth, logTree_depth] at h1
  omega

/-! ## The reverse simulation bound -/

/-- Syntactic height of an `L_F` term — every constructor counts, not only `F`. -/
def fHeight : FTerm → Nat
  | .const _ => 1
  | .var     => 1
  | .add a b => 1 + max (fHeight a) (fHeight b)
  | .sub a b => 1 + max (fHeight a) (fHeight b)
  | .mul a b => 1 + max (fHeight a) (fHeight b)
  | .div a b => 1 + max (fHeight a) (fHeight b)
  | .F a     => 1 + fHeight a

/-- **`L_F → EML` costs depth per field operation, not per `F`-query.**

The bound is a constant times the term's *syntactic height*. It cannot be improved to a function of
`fDepth` alone: `fDepth` ignores the field operations, and EML has to pay for every one of them.

The constant `400` is not optimised — it is an envelope over the gadget bounds above, the largest of
which is `divGen` at `384`. -/
theorem toEML_depth_le : ∀ T : FTerm, (toEML T).depth ≤ 400 * fHeight T := by
  intro T
  induction T with
  | const c => exact Nat.le_trans (Nat.le_refl _) (by simp [toEML, fHeight, EMLTree.depth])
  | var => exact Nat.le_trans (Nat.le_refl _) (by simp [toEML, fHeight, EMLTree.depth])
  | add a b iha ihb =>
      have h := addGen_depth_le (toEML a) (toEML b)
      simp only [toEML, fHeight]
      omega
  | sub a b iha ihb =>
      have h := subGen_depth_le (toEML a) (toEML b)
      simp only [toEML, fHeight]
      omega
  | mul a b iha ihb =>
      have h := mulGen_depth_le (toEML a) (toEML b)
      simp only [toEML, fHeight]
      omega
  | div a b iha ihb =>
      have h := divGen_depth_le (toEML a) (toEML b)
      simp only [toEML, fHeight]
      omega
  | F a iha =>
      have h := FTree_depth_le (toEML a)
      simp only [toEML, fHeight]
      omega

/-! ## A second basis-gap specimen, and the one lower bound available -/

/-- **`1/x`: minimum EML depth exactly 4, zero `F`-queries in `L_F`.**

Better than the `x + 1` specimen in one respect — the EML minimality here is *certified*
(`invX4_depth_optimal`), not merely an exclusion plus a witness. -/
theorem inv_x_basis_gap :
    (∀ u : EMLTree, (∀ x : Real, 0 < x → u.eval x = 1 / x) → 4 ≤ u.depth)
    ∧ (∃ T : FTerm, fDepth T = 0 ∧ FQueriesLe T 0
        ∧ ∀ x : Real, 0 < x → FTerm.eval T x = 1 / x) := by
  refine ⟨EMLTree.inv_x_min_depth, FTerm.div (FTerm.const 1) FTerm.var, by simp [fDepth], ?_,
    fun _ _ => rfl⟩
  exact ⟨[], Nat.le_refl 0, fun a ha => absurd ha (by simp [fArgs])⟩

/-- **The additive slack in any depth-simulation inequality is at least 4.**

Suppose some `C`, `D` satisfied `d_EML(f) ≤ C · d_F(f) + D` for every function computed on both
sides, where `d_EML` is the *minimum* over EML trees. Instantiating at `1/x` — `F`-depth `0`,
minimum EML depth `4` — gives `4 ≤ C · 0 + D`.

This is the only lower bound in the development, and note where it comes from: the EML side, where
exclusion machinery exists. Nothing here bounds `d_F` from below for any function. -/
theorem additive_slack_at_least_four (C D : Nat)
    (h : ∀ (T : FTerm) (u : EMLTree),
          (∀ x : Real, 0 < x → FTerm.eval T x = u.eval x) →
          (∀ w : EMLTree, (∀ x : Real, 0 < x → w.eval x = u.eval x) → u.depth ≤ w.depth) →
          u.depth ≤ C * fDepth T + D) :
    4 ≤ D := by
  have hT : ∀ x : Real, 0 < x →
      FTerm.eval (FTerm.div (FTerm.const 1) FTerm.var) x = invX4.eval x := by
    intro x hx; rw [invX4_eval x hx]; rfl
  have hmin : ∀ w : EMLTree, (∀ x : Real, 0 < x → w.eval x = invX4.eval x) →
      invX4.depth ≤ w.depth := by
    intro w hw
    rw [invX4_depth]
    exact EMLTree.inv_x_min_depth w (fun x hx => by rw [hw x hx, invX4_eval x hx])
  have hres := h (FTerm.div (FTerm.const 1) FTerm.var) invX4 hT hmin
  rw [invX4_depth] at hres
  simp only [fDepth, Nat.max_self, Nat.mul_zero] at hres
  omega

/-! ## The obligation this arc did not discharge -/

/-- **Named obligation: any lower bound at all on the `L_F` side.**

The smallest instance: computing `exp` requires at least one `F`. Equivalently — since an `F`-free
`L_F` term is a rational function of `x` — **`exp` is not a rational function**.

It is stated rather than proved because the corpus has no route to it. Every complexity statement in
this development is an upper bound or an exact count of a construction, and the single lower bound
(`additive_slack_at_least_four`) is imported from the EML side, where exclusion machinery exists.
Discharging this would need either a growth comparison (`exp` outgrows every rational function) or a
rational normal form for `F`-free terms; neither is present.

Recorded as an obligation, not a conjecture: it is certainly true, and the point of the row is that
**this development does not prove it**. -/
def FQueryLowerBound : Prop :=
  ∀ T : FTerm, (∀ x : Real, FTerm.eval T x = exp x) → 1 ≤ fOcc T

end MachLib
