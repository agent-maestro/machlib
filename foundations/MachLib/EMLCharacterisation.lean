import MachLib.EMLRingClosure

/-!
# What EML **is**: exactly the `exp`/`log` closure of `ℝ`

Twenty-eight sessions asked *"is `1/x` in EML?"*. With `EMLRingClosure` the class-level question
collapses, because every closure operator is now **unconditional**:

> **`InEML f ↔ ExpLogClosure f`** — EML is precisely the closure of the constants and `id` under
> `+`, `−`, `×`, `exp`, `log`.

`⊆` was always easy: an EML tree *is* an `exp a − log b` expression. `⊇` is what needed the
unconditional gadgets — its induction wants one closure lemma per constructor with **no**
side-condition, and before `EMLRingClosure` every one of them carried a positivity hypothesis.

**`log` here is MachLib's TOTALISED `log`** on both sides of the equivalence. The theorem is about
*this* class.

**Nothing here bounds DEPTH.** `EML_k` for fixed `k` is untouched; the constructions are
depth-expensive and unoptimised. **The hierarchy remains open.**

**No tension with `sin`/`cos`:** `sin` is not an `exp`/`log` expression over `ℝ`, and the Pfaffian
zero-count barrier proves its exclusion independently.
-/

namespace MachLib

open Real

/-- The closure of the constants and `id` under `+`, `−`, `×`, `exp`, `log`. -/
inductive ExpLogClosure : (Real → Real) → Prop where
  | const (c : Real) : ExpLogClosure (fun _ => c)
  | id : ExpLogClosure (fun x => x)
  | add {f g} : ExpLogClosure f → ExpLogClosure g → ExpLogClosure (fun x => f x + g x)
  | sub {f g} : ExpLogClosure f → ExpLogClosure g → ExpLogClosure (fun x => f x - g x)
  | mul {f g} : ExpLogClosure f → ExpLogClosure g → ExpLogClosure (fun x => f x * g x)
  | exp {f} : ExpLogClosure f → ExpLogClosure (fun x => Real.exp (f x))
  | log {f} : ExpLogClosure f → ExpLogClosure (fun x => Real.log (f x))

/-- `f` is realised by an EML tree, everywhere. -/
def InEML (f : Real → Real) : Prop := ∃ t : EMLTree, ∀ x : Real, t.eval x = f x

/-- **`⊇` — every `exp`/`log` expression is an EML tree.** Unconditional in `x`. -/
theorem inEML_of_expLogClosure {f : Real → Real} (h : ExpLogClosure f) : InEML f := by
  induction h with
  | const c => exact ⟨.const c, fun _ => rfl⟩
  | id => exact ⟨.var, fun _ => rfl⟩
  | add _ _ ih1 ih2 =>
      obtain ⟨a, ha⟩ := ih1; obtain ⟨b, hb⟩ := ih2
      exact ⟨addGen a b, fun x => by rw [addGen_eval, ha, hb]⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨a, ha⟩ := ih1; obtain ⟨b, hb⟩ := ih2
      exact ⟨subGen a b, fun x => by rw [subGen_eval, ha, hb]⟩
  | mul _ _ ih1 ih2 =>
      obtain ⟨a, ha⟩ := ih1; obtain ⟨b, hb⟩ := ih2
      exact ⟨mulGen a b, fun x => by rw [mulGen_eval, ha, hb]⟩
  | exp _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨expOf a, fun x => by rw [expOf_eval, ha]⟩
  | log _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨logTree a, fun x => by rw [logTree_eval, ha]⟩

/-- **`⊆` — every EML tree is an `exp`/`log` expression.** -/
theorem expLogClosure_of_tree : ∀ t : EMLTree, ExpLogClosure (fun x => t.eval x) := by
  intro t
  induction t with
  | const c => exact ExpLogClosure.const c
  | var => exact ExpLogClosure.id
  | eml t1 t2 ih1 ih2 =>
      exact ExpLogClosure.sub (ExpLogClosure.exp ih1) (ExpLogClosure.log ih2)

theorem expLogClosure_of_inEML {f : Real → Real} (h : InEML f) : ExpLogClosure f := by
  obtain ⟨t, ht⟩ := h
  have h1 : ExpLogClosure (fun x => t.eval x) := expLogClosure_of_tree t
  exact (funext ht : (fun x => t.eval x) = f) ▸ h1

/-- # **EML is EXACTLY the `exp`/`log` closure of `ℝ`.** -/
theorem eml_eq_expLogClosure (f : Real → Real) : InEML f ↔ ExpLogClosure f :=
  ⟨expLogClosure_of_inEML, inEML_of_expLogClosure⟩

end MachLib
