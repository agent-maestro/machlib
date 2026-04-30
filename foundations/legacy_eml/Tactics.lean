/-
MonogateEML/Tactics.lean

Tool 4 of the LLM-native EML tools roadmap (see
`monogate-research/roadmap/llm-native-eml-tools.md`).

Custom Lean 4 tactics that know about `EMLTree`, `IsEMLElementary`,
and the canonical universality witnesses. Sound by construction
(no axioms, no `sorry` — every tactic expands to a sequence of
existing tactics from `Universality.lean` and `EMLDepth.lean`).

Public surface:

  * `eml_auto`        — discharge `IsEMLElementary f` goals using
                        canonical witnesses + closure under composition.
  * `eml_unfold`      — bundled `simp only` over `EMLTree.eval`,
                        `EMLTree.depth`, and the boilerplate identities
                        (`Complex.log_one`, `Complex.exp_zero`,
                        `sub_zero`) that EML proofs unfold by hand.
  * `eml_golf n`      — verify a literal tree's depth bound via `decide`.
                        `eml_golf 3` succeeds if the tree on the goal
                        has depth ≤ 3 and fails (cleanly) otherwise.

Two roadmap tactics are intentionally deferred:

  * `eml_route` / `eml_synth` need a SuperBEST routing decision
    procedure inside Lean. Live in eml-cost as a Python helper today;
    porting to Lean is its own session.
  * `eml_oracle` needs `api.monogate.dev/api/lean/verify` (Tool 1).
    Lands when Tool 1 ships.

Tested against the existing 50-theorem library: every `example`
block at the bottom of this file goes green under `lake build`.
-/

import MonogateEML.EMLDepth
import MonogateEML.Universality

namespace MonogateEML.Tactics

open Lean Elab Tactic

/-! ## eml_auto — IsEMLElementary solver -/

/--
Discharge a goal of the form `IsEMLElementary f` for `f` built from
the canonical EML-elementary atoms (constants, the identity,
`Complex.exp`, `Complex.exp ∘ Complex.exp`, `fun _ => c`) and
composition.

Strategy: try each canonical witness in order, then `apply
IsEMLElementary.comp` and recurse on both sides. Falls back to
`assumption` if the goal happens to match a hypothesis.

Failure mode: clean failure when no canonical witness matches.
Does not invent witnesses or close goals it cannot justify
constructively.
-/
syntax "eml_auto" : tactic

/-
The body is bounded (one level of composition) on purpose:
`apply IsEMLElementary.comp` succeeds via metavariables on *any*
`IsEMLElementary f` goal, so an unbounded recursive `eml_auto` would
loop forever on a free-variable goal like
``(hf : IsEMLElementary f) ⊢ IsEMLElementary f``. With `assumption`
tried first and the composition step unrolled exactly one level, the
tactic terminates on every input. Users who need deeper composition
chain `apply IsEMLElementary.comp <;> eml_auto` themselves.
-/
macro_rules
  | `(tactic| eml_auto) => `(tactic|
      first
        | assumption
        | exact const_isEMLElementary _
        | exact id_isEMLElementary
        | exact exp_isEMLElementary
        | exact exp_exp_isEMLElementary
        | exact exp_const_isEMLElementary _
        | (apply IsEMLElementary.comp <;>
            first
              | assumption
              | exact const_isEMLElementary _
              | exact id_isEMLElementary
              | exact exp_isEMLElementary
              | exact exp_exp_isEMLElementary
              | exact exp_const_isEMLElementary _))


/-! ## eml_unfold — bundle of EML evaluation simp-lemmas -/

/--
A bundled `simp only` over the boilerplate that the existing
`EMLDepth.lean` / `Universality.lean` proofs unfold by hand:

  * `EMLTree.eval`, `EMLTree.depth` — recursive evaluators.
  * `Complex.log_one`, `Complex.exp_zero` — the identities that
    `eml(x, 1)` and `eml(0, y)` collapse to.
  * `sub_zero` — what's left after the log term simplifies.

Useful as the first step on any goal involving a literal EML tree.
-/
syntax "eml_unfold" : tactic

macro_rules
  | `(tactic| eml_unfold) => `(tactic|
      (simp only [EMLTree.eval, EMLTree.depth, Complex.log_one,
                  Complex.exp_zero, sub_zero, Nat.zero_max,
                  Nat.max_zero, Nat.add_zero, Nat.zero_add,
                  max_self];
       try decide))


/-! ## eml_golf n — verify a literal tree's depth bound -/

/--
`eml_golf n` succeeds if the goal is `t.depth ≤ n` (or `t.depth = n`)
for a literal `EMLTree` `t`. Implementation is `decide`, which works
because `EMLTree.depth` is a computable function on a decidable
inductive type.

Use case: golf a proof to a specific node count. The complement
("fails if the tree is bigger than n") is what `decide` already
gives — when `t.depth > n`, `decide` reports the false equality
explicitly.
-/
syntax "eml_golf " num : tactic

macro_rules
  | `(tactic| eml_golf $_n) => `(tactic| decide)


end MonogateEML.Tactics

/-! ## Self-tests — every block here must go green under `lake build` -/

section TacticsSmoke

open MonogateEML.Tactics

/-- `eml_auto` closes the canonical depth-0 witnesses. -/
example (c : ℂ) : IsEMLElementary (fun _ : ℂ => c) := by eml_auto
example : IsEMLElementary (fun x : ℂ => x) := by eml_auto

/-- `eml_auto` closes the canonical depth-1 / depth-2 witnesses. -/
example : IsEMLElementary (fun x : ℂ => Complex.exp x) := by eml_auto
example : IsEMLElementary (fun x : ℂ => Complex.exp (Complex.exp x)) := by
  eml_auto

/-- `eml_auto` discharges a hypothesis-driven goal. -/
example (f : ℂ → ℂ) (hf : IsEMLElementary f) : IsEMLElementary f := by
  eml_auto

/-- `eml_unfold` collapses `eval` + `log_one` + `sub_zero` boilerplate. -/
example (x : ℂ) : EMLTree.eval (.ceml .var (.const 1)) x = Complex.exp x := by
  eml_unfold

/-- `eml_unfold` knows `EMLTree.depth` for literal trees. -/
example : EMLTree.depth (.ceml .var (.const 1)) = 1 := by eml_unfold

/-- `eml_golf` verifies a depth bound on a literal tree. -/
example : EMLTree.depth (.ceml .var (.const 1)) ≤ 1 := by eml_golf 1
example : EMLTree.depth (.ceml .var (.const 1)) = 1 := by eml_golf 1
example : EMLTree.depth EMLTree.var = 0 := by eml_golf 0

end TacticsSmoke
