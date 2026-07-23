import MachLib.SinNotInEML
import MachLib.IterExpChain
import MachLib.Log

/-!
# Track C, item C5: EML subsumes the iterated-exponential tower (existence direction)

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). C5 asked for a
"chain-N ⊊ chain-(N+1)" hierarchy theorem bridging `EMLTree` (this arc's own grammar),
`IterExpDepthN`'s iterated-exponential-tower `Khovanskii` zero-count development, and the
(separate, Python/SymPy, non-Lean) chain-5 census. Investigated end-to-end this round rather than
assumed; the honest findings (recorded in full in the decision doc, cont. 90) are:

1. **A genuinely new structural fact, checked by reading source, not assumed**: `EMLEncoder.lean`'s
   `enc` and `IterExpChain.lean`'s `IterExpChain` are BOTH literal instances of the SAME general
   `PfaffianChain n` structure (`PfaffianChain.lean`) — `enc t chain : PfaffianChain (len t N)`,
   `IterExpChain N : PfaffianChain N`. "Chain order" genuinely has one uniform meaning across both
   developments, contrary to the "three unrelated formalisms" framing this arc had used since
   cont. 74 (that framing is still right about the THIRD leg — the Python census — which has no
   Lean presence and is not a `PfaffianChain` at all).

2. **The muses' proposed obstruction mechanism does not combine as stated.** `TailSign`
   (oscillation/eventual-sign) and Pfaffian chain ORDER are orthogonal axes: `sin`'s own classical
   ODE (`y'' = -y`) gives it chain order 2, yet `EMLTree` cannot represent it — not because of any
   chain-order deficiency, but because `EMLTree`'s grammar (`exp(t1) - log(t2)` only, no bare
   subtraction/multiplication/sin-shaped primitives) simply does not contain sin-shaped values at
   ANY chain order. A genuine "chain-N barrier" would need an obstruction sensitive to chain order
   itself (e.g. a growth-rate argument), which `TailSign` is not, and which was not built this
   round — flagged, not forced, matching this document's own discipline for C2/C4/C5's earlier
   scoping entries.

**What THIS file builds: the existence-direction bridge, concretely.** Before any obstruction
claim can even be stated meaningfully, the represented CLASSES need a real point of contact.
`emlTower : Nat → EMLTree` (using the `eml t (const 1)` idiom — `log 1 = 0` collapses `eml t
(const 1)` to `exp(t.eval ·)` exactly, unconditionally, no clamp ever triggers) matches
`IterExpChain`'s own `iterExp` EXACTLY at every depth: `(emlTower n).eval x = iterExp n x`, no
hypothesis, no restriction. So `EMLTree` already reaches every level of the iterated-exponential
tower family — the depth-`(n+1)` tower is a genuine `EMLTree` of `EMLTree.depth = n+1`. This is a
real, checked, previously-unconfirmed connection between the two arcs (not the full hierarchy
theorem C5 originally asked for, but its necessary and non-trivial prerequisite).

`sorryAx`-free, zero new axioms — pure structural induction plus the already-proven `log_one`.
-/

namespace MachLib

open MachLib.Real
open MachLib.IterExpChainMod

/-- **The EML tower idiom.** `eml t (const 1)` collapses to `exp(t.eval ·)` exactly (§ below),
unconditionally — so nesting it `n` times reaches the `(n+1)`-fold iterated exponential. -/
noncomputable def emlTower : Nat → EMLTree
  | 0     => EMLTree.eml EMLTree.var (EMLTree.const 1)
  | n + 1 => EMLTree.eml (emlTower n) (EMLTree.const 1)

/-- **`emlTower` matches `iterExp` exactly, at every depth, everywhere.** No hypothesis: the
`const 1` slot is unconditionally positive, so `EMLTree.eval`'s `log` never sees a non-positive
argument — this is a genuine equality of real functions on all of `ℝ`, not an eventual one. -/
theorem emlTower_eval (n : Nat) (x : Real) : (emlTower n).eval x = iterExp n x := by
  induction n with
  | zero =>
      show Real.exp (EMLTree.var.eval x) - Real.log (1 : Real) = iterExp 0 x
      show Real.exp x - Real.log (1 : Real) = iterExp 0 x
      rw [log_one, sub_zero, iterExp_zero]
  | succ k ih =>
      show Real.exp ((emlTower k).eval x) - Real.log (1 : Real) = iterExp (k + 1) x
      rw [log_one, sub_zero, ih, iterExp_succ]

/-- `emlTower n` has depth exactly `n + 1` — each nesting level adds one `eml` node on top of a
depth-0 `const 1` sibling. -/
theorem emlTower_depth (n : Nat) : (emlTower n).depth = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show 1 + max (emlTower k).depth (EMLTree.const 1).depth = k + 1 + 1
      have hconst : (EMLTree.const (1 : Real)).depth = 0 := rfl
      rw [hconst, ih]
      omega

/-- **`EMLTree` reaches every depth of the iterated-exponential tower.** The existence-direction
half of a genuine `EMLTree`/`IterExpDepthN` connection: for every `n`, some tree of depth `n + 1`
evaluates to `iterExp n` on all of `ℝ`. -/
theorem exists_emlTree_eq_iterExp (n : Nat) :
    ∃ T : EMLTree, T.depth = n + 1 ∧ ∀ x : Real, T.eval x = iterExp n x :=
  ⟨emlTower n, emlTower_depth n, emlTower_eval n⟩

end MachLib
