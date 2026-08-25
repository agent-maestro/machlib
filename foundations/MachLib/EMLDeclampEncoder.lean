import MachLib.EMLEncoder
import MachLib.EMLEventualContinuity
import MachLib.EMLSignZeroProducer

/-!
# The clamped-aware encoder: positivity where the induction gives a disjunction

`enc_isCoherentOn` (`EMLEncoder`) needs `LogArgPos` — the log argument **positive** at every node
throughout `(a,b)`. The depth induction does not supply that. `evSignCont_of_cts`
(`EMLEventualContinuity`) gives each node's argument *positive or non-positive on a ray*, and on the
non-positive branch `LogArgPos` fails outright.

That gap is not mathematical. **Where the log argument is non-positive, the node has no logarithm in
it**: `log y = 0` for `y ≤ 0`, so `eml t1 t2` there evaluates to `exp (t1 x)`. And `exp ∘ t1` is
itself an EML node with a *positive* argument — `eml t1 (const 1)`, since `log 1 = 0`
(`expTree_eval`, `EMLSignReduction`).

So the fix is to rewrite the **tree**, not to rebuild the encoder. `declamp t a b` replaces every
clamped node's right child by `const 1`. The result computes the same function on `(a,b)` and
satisfies `LogArgPos` outright, so the existing encoder applies unchanged.

## What this closes

```
SignHardCase → ∀ t, EvSign t.eval            (evSign_of_hard)
             → LogArgStable t on a ray        (logArgStable_of_evSign)
             → LogArgPos (declamp t) ∧ same values   (declamp_logArgPos, declamp_eval)
             → enc (declamp t) is coherent on (a,b)  (enc_declamp_isCoherentOn)
```

A coherent chain is analytic, which is what the log-Khovanskii arc consumes. The disjunction the
induction produces is therefore *enough* to feed the encoder — it was only ever the wrong shape.

## What this does not close

`declamp` depends on `(a,b)`: it is a different tree per interval, chosen by a `Classical` test on
each node. That is harmless for coherence on a fixed interval, which is all `enc_isCoherentOn` asks,
but it means there is no single tree serving every interval, and the zero-counting step must be taken
per interval and then made uniform. No `UniformZeroBound` is supplied here, and `SignHardCase` stays
open.

Note also what `LogArgStable` is **not**: it is not `EMLNoCrossingAt`. A node whose argument sits at
exactly `0` throughout is stable (the non-positive branch), and `declamp` sends it to `const 1`. The
condition rules out *crossings within the interval*, not zeros.
-/

namespace MachLib

open Real

/-! ## §1 — the stability condition

`LogArgPos` with each node's positivity replaced by a **disjunction**: positive throughout, or
non-positive throughout. Exactly what a per-node `EvSign` verdict delivers on a ray. -/

/-- Every `eml` node's log argument is of one sign throughout `(a,b)` — positive, or non-positive.
Weaker than `LogArgPos`, and the shape the depth induction produces. -/
def LogArgStable : EMLTree → Real → Real → Prop
  | .const _, _, _ => True
  | .var,     _, _ => True
  | .eml t1 t2, a, b =>
      LogArgStable t1 a b ∧ LogArgStable t2 a b ∧
        ((∀ x, a < x → x < b → 0 < t2.eval x) ∨ (∀ x, a < x → x < b → t2.eval x ≤ 0))

/-- `LogArgPos` is the positive-branch special case. -/
theorem logArgStable_of_logArgPos (t : EMLTree) (a b : Real) (h : LogArgPos t a b) :
    LogArgStable t a b := by
  induction t with
  | const c => exact True.intro
  | var => exact True.intro
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨h1, h2, hpos⟩ := h
      exact ⟨ih1 h1, ih2 h2, Or.inl hpos⟩

/-! ## §2 — the rewrite

The branch test is a `Classical` decision on a `Prop` about the whole interval, so `declamp` is
`noncomputable`. That costs nothing here: it is only ever used inside proofs about a fixed `(a,b)`. -/

open Classical in
/-- Replace every **clamped** node's right child by `const 1`. On the clamped branch the node's value
is `exp (t1 x)`, and `eml t1 (const 1)` computes exactly that with a log argument of `1 > 0`. -/
noncomputable def declamp : EMLTree → Real → Real → EMLTree
  | .const c, _, _ => .const c
  | .var,     _, _ => .var
  | .eml t1 t2, a, b =>
      if (∀ x, a < x → x < b → 0 < t2.eval x) then
        .eml (declamp t1 a b) (declamp t2 a b)
      else
        .eml (declamp t1 a b) (.const 1)

/-- **The rewrite preserves the function on `(a,b)`.** The clamped branch is where the work happens:
there `log (t2.eval x) = 0` by totalisation and `log 1 = 0` by definition, so both sides are
`exp (t1.eval x)`. -/
theorem declamp_eval (t : EMLTree) (a b : Real) (h : LogArgStable t a b) :
    ∀ x : Real, a < x → x < b → (declamp t a b).eval x = t.eval x := by
  induction t with
  | const c => intro x _ _; rfl
  | var => intro x _ _; rfl
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨h1, h2, hd⟩ := h
      intro x hxa hxb
      by_cases hpos : (∀ x, a < x → x < b → 0 < t2.eval x)
      · rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (declamp t2 a b) from by
            simp only [declamp, if_pos hpos]]
        show exp ((declamp t1 a b).eval x) - log ((declamp t2 a b).eval x)
            = exp (t1.eval x) - log (t2.eval x)
        rw [ih1 h1 x hxa hxb, ih2 h2 x hxa hxb]
      · have hnp : ∀ x, a < x → x < b → t2.eval x ≤ 0 := by
          rcases hd with hp | hn
          · exact absurd hp hpos
          · exact hn
        rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (EMLTree.const 1) from by
            simp only [declamp, if_neg hpos]]
        show exp ((declamp t1 a b).eval x) - log ((1 : Real))
            = exp (t1.eval x) - log (t2.eval x)
        rw [ih1 h1 x hxa hxb, log_one, log_nonpos (hnp x hxa hxb)]

/-- **And the rewrite is positive at every node.** Kept nodes keep a positive argument (their value
is unchanged by `declamp_eval`); rewritten nodes have argument `1`. -/
theorem declamp_logArgPos (t : EMLTree) (a b : Real) (h : LogArgStable t a b) :
    LogArgPos (declamp t a b) a b := by
  induction t with
  | const c => exact True.intro
  | var => exact True.intro
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨h1, h2, hd⟩ := h
      by_cases hpos : (∀ x, a < x → x < b → 0 < t2.eval x)
      · rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (declamp t2 a b) from by
            simp only [declamp, if_pos hpos]]
        refine ⟨ih1 h1, ih2 h2, fun x hxa hxb => ?_⟩
        rw [declamp_eval t2 a b h2 x hxa hxb]
        exact hpos x hxa hxb
      · rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (EMLTree.const 1) from by
            simp only [declamp, if_neg hpos]]
        exact ⟨ih1 h1, True.intro, fun x _ _ => zero_lt_one_ax⟩

/-! ## §3 — feeding the existing encoder -/

open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain in
/-- **The encoder applies to the rewritten tree.** `enc_isCoherentOn` unchanged, with the
disjunction-shaped hypothesis in place of the positivity-shaped one. -/
theorem enc_declamp_isCoherentOn (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (a b : Real)
    (hchain : chain.IsCoherentOn a b) (h : LogArgStable t a b) :
    (enc (declamp t a b) chain).1.IsCoherentOn a b :=
  enc_isCoherentOn (declamp t a b) chain a b hchain (declamp_logArgPos t a b h)

/-! ## §4 — the depth induction supplies `LogArgStable` on a ray

One ray for the whole tree, by structural induction: each node contributes its own child's `EvSign`
verdict and the children contribute theirs, and the three rays are joined. -/

private theorem ray_join3 {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

/-- **Eventual stability, from sign-definiteness at every node.** Given `EvSign` for every tree — what
`evSign_of_hard` and `evSign_of_uniformBounds` both deliver — every tree is `LogArgStable` on every
interval far enough out. -/
theorem logArgStable_of_evSign (hs : ∀ s : EMLTree, EvSign s.eval) (t : EMLTree) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b := by
  induction t with
  | const c => exact ⟨1, le_refl 1, fun _ _ _ _ => True.intro⟩
  | var => exact ⟨1, le_refl 1, fun _ _ _ _ => True.intro⟩
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨X1, hX11, hst1⟩ := ih1
      obtain ⟨X2, hX21, hst2⟩ := ih2
      obtain ⟨XS, hXS1, hsign⟩ : ∃ X : Real, 1 ≤ X ∧
          ((∀ x : Real, X ≤ x → 0 < t2.eval x) ∨ (∀ x : Real, X ≤ x → t2.eval x ≤ 0)) := by
        rcases hs t2 with ⟨X, h1, hp⟩ | ⟨X, h1, hn⟩
        · exact ⟨X, h1, Or.inl hp⟩
        · exact ⟨X, h1, Or.inr hn⟩
      obtain ⟨Y, hY1, hYX1, hYX2⟩ := ray_join3 hX11 hX21
      obtain ⟨X₀, hX01, hX0Y, hX0S⟩ := ray_join3 hY1 hXS1
      refine ⟨X₀, hX01, fun a b hab hlt => ?_⟩
      have haX1 : X1 ≤ a := le_trans hYX1 (le_trans hX0Y hab)
      have haX2 : X2 ≤ a := le_trans hYX2 (le_trans hX0Y hab)
      have haXS : XS ≤ a := le_trans hX0S hab
      refine ⟨hst1 a b haX1 hlt, hst2 a b haX2 hlt, ?_⟩
      rcases hsign with hp | hn
      · exact Or.inl (fun x hxa _ => hp x (le_of_lt (lt_of_le_of_lt haXS hxa)))
      · exact Or.inr (fun x hxa _ => hn x (le_of_lt (lt_of_le_of_lt haXS hxa)))

/-! ## §5 — the capstone -/

open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain in
/-- **Every EML tree is eventually encodable by a coherent chain, on the existing obligation.**

On every interval far enough out, `declamp t a b` computes `t` and its encoding is a coherent — hence
analytic — Pfaffian chain. The clamped branch, which `LogArgPos` could not express and
`EMLNoCrossingAt` rejected outright, is absorbed by rewriting the node to its `exp` factor. -/
theorem eventually_coherent_encoding_of_hard (h : SignHardCase) (t : EMLTree) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ a b : Real, X₀ ≤ a → a < b →
      (∀ x : Real, a < x → x < b → (declamp t a b).eval x = t.eval x) ∧
      ∀ {N : Nat} (chain : PfaffianChain N), chain.IsCoherentOn a b →
        (enc (declamp t a b) chain).1.IsCoherentOn a b := by
  obtain ⟨X₀, hX01, hst⟩ := logArgStable_of_evSign (evSign_of_hard h) t
  refine ⟨X₀, hX01, fun a b hab hlt => ⟨declamp_eval t a b (hst a b hab hlt), ?_⟩⟩
  intro N chain hchain
  exact enc_declamp_isCoherentOn t chain a b hchain (hst a b hab hlt)

/-- The same, on the zero-control obligation instead. -/
theorem eventually_coherent_encoding_of_uniformBounds (h : SignHardUniformZeroBound)
    (t : EMLTree) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b :=
  logArgStable_of_evSign (evSign_of_uniformBounds h) t

end MachLib
