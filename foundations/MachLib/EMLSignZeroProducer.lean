import MachLib.EMLEventualContinuity
import MachLib.EMLSignReduction
import MachLib.EMLZeroBoundRay

/-!
# The zero-counting producer, and the obligation it refutes on the way

`EMLEventualContinuity` reduced sign-definiteness at every depth to a statement about the node value
`exp (A x) − log (B x)`, with eventual continuity manufactured by the induction rather than assumed.
Two candidate obligations were stated there. This module connects the corpus's zero-counting bridge
to one of them — and **refutes the other**.

## `SignHardNonzero` is false

`exp ∘ exp ∘ t` is again an EML tree (`expExpTree_eval`, `EMLSignReduction`). So for any `A`, taking

```
B := expExpTree A          B.eval x = exp (exp (A.eval x)) > 0   for every x
```

satisfies the positivity hypothesis on the whole line, and

```
exp (A.eval x) − log (B.eval x) = exp (A.eval x) − exp (A.eval x) = 0
```

**identically**. A function that is everywhere zero is never eventually non-vanishing, so
`not_signHardNonzero` closes it. The theorems in `EMLEventualContinuity` that take `SignHardNonzero`
as a hypothesis remain true and are now known **vacuous**; they are kept as the record of the step,
not as usable results, and their docstrings say so.

This is the same failure `EMLZeroBoundRay` documents for the unconditioned form of
`bipolyNoOscillation`'s hypothesis (`N = []` has an identically-zero germ and therefore no bound). The
lesson transfers exactly: **an obligation that demands non-vanishing must be conditioned on not being
eventually zero**, or the identically-zero member refutes it.

Worth stating plainly: the earlier reading of `SignHardNonzero` as "a sufficient condition, stronger
than `SignHardCase`" was right about the *direction* and wrong about the *value*. A false sufficient
condition is not a stronger obligation; it is no obligation at all.

## What survives, and why it was worth shipping

`SignHardNonzeroOrClamped` is untouched by the counterexample: the identically-zero germ satisfies its
**second** disjunct (`≤ 0` on a ray) rather than falsifying the statement. That is precisely the
disjunct that made it debt-neutral — implied by `SignHardCase` as well as implying it — and the
counterexample shows the disjunct is load-bearing rather than decorative.

## The producer

`eventually_nonzero_of_uniformZeroBoundFrom` (`EMLZeroBoundRay`) turns a zero bound uniform **in the
interval** into eventual non-vanishing, with no analyticity and nothing about `f` beyond the bound.
`SignHardUniformZeroBound` is that demand for the node value, conditioned on `¬ EvZeroF` exactly as
`bipolyNoOscillation_of_uniformBounds` conditions its own, and restricted to the ray `[X₀, ∞)` the
obligation actually controls. The chain closes:

```
SignHardUniformZeroBound → SignHardNonzeroOrClamped → SignHardCts → ∀ t, EvSign t.eval ∧ EvCont t.eval
```

and it now runs through the **same** bridge lemma that `oneQueryDichotomy_of_uniformBounds` uses. The
shared frontier is a shared *lemma*, not an analogy between two prose descriptions.

## Scope

`SignHardCase` stays open and no ledger row moves. This module supplies no `UniformZeroBound` for any
EML node value; establishing one is the open work, and `EMLZeroBoundRay`'s own note applies verbatim —
the Khovanskii statements would first have to quantify `N` **before** the interval.
-/

namespace MachLib

open Real

/-! ## §1 — the counterexample

`expExpTree` names the term `expExpTree_eval` is about, so the refutation and the specimen below can
share it. -/

/-- `exp ∘ exp ∘ t`, as an EML tree. -/
noncomputable def expExpTree (t : EMLTree) : EMLTree :=
  EMLTree.eml (EMLTree.eml t (EMLTree.const 1)) (EMLTree.const 1)

/-- Its right child is positive everywhere, so it satisfies `SignHardCase`'s hypothesis on any ray. -/
theorem expExpTree_pos (t : EMLTree) (x : Real) : 0 < (expExpTree t).eval x := by
  rw [show (expExpTree t).eval x = exp (exp (t.eval x)) from expExpTree_eval t x]
  exact exp_pos _

/-- The node value over that right child is **identically zero**, for every left child `A`. -/
theorem expExpTree_node_eq_zero (A : EMLTree) (x : Real) :
    exp (A.eval x) - log ((expExpTree A).eval x) = 0 := by
  rw [show (expExpTree A).eval x = exp (exp (A.eval x)) from expExpTree_eval A x, log_exp]
  mach_ring

/-- **`SignHardNonzero` is refuted.** Pure eventual non-vanishing at the hard node cannot hold: the
right child `exp ∘ exp ∘ A` is positive everywhere and drives the node value to `0` everywhere.

The obligation was not merely stronger than `SignHardCase` — it was unsatisfiable, and every theorem
assuming it is vacuous. -/
theorem not_signHardNonzero : ¬ SignHardNonzero := by
  intro h
  obtain ⟨R, hR1, hne⟩ :=
    h (EMLTree.const 0) (expExpTree (EMLTree.const 0)) 1 (le_refl 1)
      (fun x _ => expExpTree_pos (EMLTree.const 0) x)
  exact hne R (le_refl R) (expExpTree_node_eq_zero (EMLTree.const 0) R)

/-- And the witness lands in `SignHardNonzeroOrClamped`'s **second** disjunct rather than refuting it
— the disjunct is what absorbs the counterexample. -/
theorem expExpTree_witness_is_clamped (A : EMLTree) :
    ∃ R : Real, 1 ≤ R ∧ ∀ x : Real, R ≤ x → exp (A.eval x) - log ((expExpTree A).eval x) ≤ 0 :=
  ⟨1, le_refl 1, fun x _ => le_of_eq (expExpTree_node_eq_zero A x)⟩

/-! ## §2 — the conditioned producer

The conditioning on `¬ EvZeroF` is not cosmetic: §1 is exactly the member it must exclude. -/

/-- **What the zero-counting arc would have to deliver at the hard node.** A bound on the number of
zeros that is uniform **in the interval** (`K` quantified before `a b`), for node values that are not
eventually zero.

Same conditioning as `bipolyNoOscillation_of_uniformBounds`'s hypothesis, and demanded only on the
ray the obligation actually controls: `UniformZeroBoundFrom … X₀ …`, not `UniformZeroBound`. The
positivity hypothesis says nothing about `B` below `X₀`, so asking for zero control there would be
asking the producer for information this statement never gives it. The stronger form still suffices
(`uniformZeroBoundFrom_of_uniformZeroBound`), so nothing is lost by asking for less. -/
def SignHardUniformZeroBound : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    ¬ EvZeroF (fun x => exp (A.eval x) - log (B.eval x)) →
    ∃ K : Nat, UniformZeroBoundFrom (fun x => exp (A.eval x) - log (B.eval x)) X₀ K

/-- **The producer, wired.** Eventually-zero node values take the clamped disjunct; the rest go
through `eventually_nonzero_of_uniformZeroBound` — the same bridge
`oneQueryDichotomy_of_uniformBounds` uses. -/
theorem signHardNonzeroOrClamped_of_uniformBounds (h : SignHardUniformZeroBound) :
    SignHardNonzeroOrClamped := by
  intro A B X₀ hX₀ hpos
  rcases Classical.em (EvZeroF (fun x => exp (A.eval x) - log (B.eval x))) with hz | hz
  · obtain ⟨Y, hY1, hzero⟩ := hz
    exact ⟨Y, hY1, Or.inr (fun x hx => le_of_eq (hzero x hx))⟩
  · obtain ⟨K, hK⟩ := h A B X₀ hX₀ hpos hz
    obtain ⟨Y, hY1, hne⟩ := eventually_nonzero_of_uniformZeroBoundFrom hK
    exact ⟨Y, hY1, Or.inl hne⟩

/-- **The full chain.** Uniform zero bounds at the hard node give sign-definiteness *and* eventual
continuity for every EML tree, at every depth — continuity manufactured by the induction, sign by the
producer. -/
theorem evSignCont_of_uniformBounds (h : SignHardUniformZeroBound) :
    ∀ t : EMLTree, EvSign t.eval ∧ EvCont t.eval :=
  evSignCont_of_cts
    (signHardCts_of_nonzeroOrClamped (signHardNonzeroOrClamped_of_uniformBounds h))

/-- The sign half, stated where `evSign_of_hard` states its own. -/
theorem evSign_of_uniformBounds (h : SignHardUniformZeroBound) :
    ∀ t : EMLTree, EvSign t.eval :=
  fun t => (evSignCont_of_uniformBounds h t).1

/-! ## §3 — discrimination

Two specimens, because the hypothesis could fail to mean anything in two different ways. -/

/-- **The conditioning fires on the counterexample.** `expExpTree A`'s node value *is* eventually
zero, so `SignHardUniformZeroBound` demands nothing there — which is why §1 does not refute it too. -/
theorem counterexample_is_conditioned_out (A : EMLTree) :
    EvZeroF (fun x => exp (A.eval x) - log ((expExpTree A).eval x)) :=
  ⟨1, le_refl 1, fun x _ => expExpTree_node_eq_zero A x⟩

private theorem const_node_eval (x : Real) :
    exp ((EMLTree.const 0).eval x) - log ((EMLTree.const 1).eval x) = 1 := by
  show exp (0 : Real) - log (1 : Real) = 1
  rw [log_one, exp_zero]
  mach_ring

/-- **And the hypothesis is not vacuous.** `A = const 0`, `B = const 1` has `B > 0`, is *not*
eventually zero, and carries the uniform bound `0` — so there is a pair at which the demand is real
and satisfiable. Without this the conditioning could have emptied the statement instead of repairing
it. -/
theorem signHardUniformZeroBound_specimen :
    ¬ EvZeroF (fun x => exp ((EMLTree.const 0).eval x) - log ((EMLTree.const 1).eval x))
      ∧ UniformZeroBoundFrom
          (fun x => exp ((EMLTree.const 0).eval x) - log ((EMLTree.const 1).eval x)) 1 0 := by
  constructor
  · intro hz
    obtain ⟨Y, hY1, hzero⟩ := hz
    have h1 : exp ((EMLTree.const 0).eval Y) - log ((EMLTree.const 1).eval Y) = 0 :=
      hzero Y (le_refl Y)
    rw [const_node_eval Y] at h1
    exact zero_ne_one_ax h1.symm
  · intro a b _ _ zeros _ hmem
    cases zeros with
    | nil => exact Nat.le_refl 0
    | cons z _ =>
        exfalso
        have hz0 : exp ((EMLTree.const 0).eval z) - log ((EMLTree.const 1).eval z) = 0 :=
          (hmem z List.mem_cons_self).2.2
        rw [const_node_eval z] at hz0
        exact zero_ne_one_ax hz0.symm

end MachLib
