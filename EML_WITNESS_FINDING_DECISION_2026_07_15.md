# Decision draft: `eml_pfaffian_validon_from_sin_equality` — witness-finding options

**Date:** 2026-07-15
**Status:** DRAFT — options sketch, no decision made yet.
**Supersedes (partially):** `EMLPFAFFIAN_VALIDON_DECISION_2026_06_12.md`. That document's cost
estimate (weeks-to-month, needing a new `Smoothness`/connectivity module) is now obsolete — this
session took a completely different route and closed far more than it anticipated, at much lower
cost, with zero new axioms. What's left is narrower and better-characterized than either prior
document could have known.

## Context: what changed since June 12

The June 12 decision recommended shipping `eml_pfaffian_validon_from_sin_equality` as a named,
classically-true axiom, estimating a 300–500 line `Smoothness` module (smoothness preservation
under `+`/`-`/`·`/`∘`, a `Continuous_of_HasDerivAt` bridge, and a connectivity/IVT argument) as the
closure path — multi-session, not attempted at the time.

A single long session (this one) attacked the problem from a different angle — never building
`IsSmoothOn` or a general smoothness-preservation module at all. Instead: a local, structural
"no crossing" predicate (`EMLNoCrossingAt`, weaker than full validity, provable by ordinary
induction with no circularity) gives differentiability for free; a linear-ODE/integrating-factor
technique (`const_ratio_of_shared_ode` + `eml_ode_step_general`/`eml_E_step_general`) forces an
EML node's log-argument into an explicit closed form wherever positivity already holds; and a
minimal-violation-point argument (via the completeness axiom `sup_exists`/`inf_exists`, already in
MachLib) extends that closed form to the boundary, producing a contradiction if positivity ever
fails. A second, independent mechanism (value blow-up, exploiting `log`'s clamp discontinuity and
`|sin| ≤ 1`) covers a different but overlapping class of tree shapes.

Net result: **zero new axioms beyond one** (`HasDerivAt_congr`, a small local-invariance fact added
early on) and roughly 2200 new lines in `EMLSmoothness.lean`, closing far more of the axiom's
content than the June 12 estimate treated as in scope at all.

## What's actually proven now

| Class of tree shape | Status | Needs a witness? |
|---|---|---|
| Depth-1 (root `= eml t1 t2`, offender `= t2`) | Closed, any `b > 0` | Yes — but free (any zero of `sin`/`cos`) |
| Right-descent then arbitrary-length left-chain, optionally one more right turn at the root | Closed, any chain length (value-blow-up mechanism; round 5 proves this is that mechanism's ENTIRE reach) | Yes, supplied |
| Arbitrary-depth left-descent spine (ODE mechanism) | Closed, any spine length | Yes, one witness at the bottom |
| Arbitrary-depth pure right-descent chain (ODE mechanism) | Closed, any chain length | Yes, one witness per level |

All four rows: fully mechanized, zero new axioms, verified via `#print axioms` after every theorem.

## What remains: witness-finding

Every row above except depth-1 takes its witness(es) as a hypothesis rather than deriving them.
Depth-1's witness is free because ANY zero of `sin` (there are infinitely many) makes the defining
equation `exp(t1.eval x) − log(t2.eval x) = sin x` force `log(t2.eval x) = exp(t1.eval x) > 0`
unconditionally — no case split, no assumption on `t1`.

An investigation into whether this generalizes (attempting to prove a witness ALWAYS exists, for
ANY tree, from `t.eval = sin` alone) found a concrete obstruction: the natural inductive invariant
("the node's effective target dips non-positive somewhere") does not propagate through one step of
left-descent. Tracing the algebra: whether the next level down also gets a non-positive point
depends on the RANGE of the sibling subtree at that level — and nothing in `EMLTree`'s definition
constrains that range. A sibling subtree that stays bounded well above the needed threshold
everywhere defeats the propagation outright; this isn't a proof-technique weakness, it's a real
degree of freedom in what `EMLTree` allows.

## Three ways forward

### Option A — Restrict scope: prove witness-existence for a documented non-degeneracy condition

Add an explicit hypothesis to a new, narrower closure theorem — e.g. "every sibling subtree
encountered along the descent is unbounded above at some point" (or a similarly concrete,
per-subtree condition) — and prove witness-existence holds under it. Ship this as the operative
closure; leave fully unconstrained trees as a separately named, narrower residual axiom.

- **Pros:** directly targets the SPECIFIC failure mode found (bounded siblings defeat the
  invariant) — "require unboundedness" is the natural repair. Concrete and likely buildable at a
  similar scale to rounds 15–18 of this session (each landed in 1–2 rounds once the right
  abstraction was found).
- **Cons:** doesn't close the axiom as currently stated. The non-degeneracy condition needs
  checking against realistic use (trivial for `var`, needs verifying for compound subtrees) —
  possible it's still too strong or too weak once formalized.
- **Rough scale:** 1–3 more rounds, comparable to recent history.

### Option B — Continue researching the fully general case

Keep looking for an invariant or argument that survives arbitrary sibling behavior, with no
non-degeneracy hypothesis at all.

- **Pros:** if found, closes the axiom exactly as stated, no added conditions.
- **Cons:** this session already spent real, focused effort here and hit a concrete wall (not
  "didn't look hard enough" — found and verified a specific counter-scenario). No candidate next
  idea identified. Open-ended, no way to bound the effort in advance.

### Option C — Check whether the axiom is actually false as stated

Attempt to CONSTRUCT an explicit MachLib `EMLTree` (using real `const`/`var`/`eml` nodes, not an
abstract argument) where `t.eval = sin` holds globally and some offender genuinely has no witness
anywhere. This is a different kind of work than A/B — concrete construction and computation, not
proof search.

- **Pros:** either outcome is valuable. Success means the axiom needs an explicit side-condition —
  a significant, directly actionable finding (and would sharpen exactly what Option A's condition
  needs to rule out). Failure to construct one is useful negative evidence supporting A or B.
- **Cons:** building a genuine counterexample satisfying the GLOBAL equation `t.eval = sin` (not
  just "some point") is itself a nontrivial constraint most naive attempts won't satisfy — may
  turn out to be comparably hard to the original problem.
- **Rough scale:** worth a bounded, cheap check (a session, not a multi-round commitment) before
  committing further effort to A or B.

## Recommendation

Option A first, with a lightweight Option C gut-check alongside it (not instead of it). Reasoning:
round 18's mechanism-building is essentially complete and this session's failure mode (round 19)
is concrete rather than vague, which is exactly the situation where "restrict scope, ship the
restricted result, name the residual gap" (the same pattern the June 12 document already used
successfully for the axiom as a whole) is the right move. A quick attempt at Option C first is
cheap insurance — if a real counterexample turns up, it directly informs what Option A's
non-degeneracy condition needs to say, rather than guessing at one and discovering later it's
either too weak (doesn't actually enable the proof) or too strong (excludes trees that matter).

Option B is not recommended as the NEXT step — not because it's worthless, but because it has no
natural stopping point and this session already gave it a genuine, focused attempt.

## Update 2026-07-16 — Option A, first concrete point scored

Built `eml_depth2_witness_of_const_var` (`EMLSmoothness.lean`, commit `f29390ef`): if the depth-2
offender `S3` (in `t = eml T1 (eml S2 S3)`) were identically `≤ 0`, its log-branch collapses to the
constant `0`, and — via `log∘exp = id` unconditionally, the same asymmetry `eml_leftchild_explicit_value`
already exploits — the whole tree collapses to `exp(T1.eval x) − S2.eval x = sin x` for all `x`. For
`T1` globally constant and `S2` a leaf (constant or the identity), this is refutable by direct
evaluation at one or two points (`x = 0`, `x = π/2`). Result: a witness for `S3` with **no
hypothesis needed at all** — the first case where witness-finding is fully resolved beyond depth-1.
Compiled with zero errors on the first attempt; zero new axioms.

This does not touch compound `T1`/`S2` — those reopen the round-19 recursive difficulty exactly.
The natural next step under Option A is pushing the same "collapse + evaluate/differentiate"
technique to `T1`/`S2` being simple-but-not-leaf, to map out how far elementary reasoning reaches
before the recursion genuinely bites.

## Update 2026-07-16 (cont.) — the T1-constant restriction pinned down exactly

Checked whether `T1`-constant was load-bearing in BOTH of the previous update's branches, or just
one. It's only load-bearing for ONE narrow sub-case:

- `eml_depth2_witness_of_var_sibling`: `S2 = var`, `T1` COMPLETELY ARBITRARY. Evaluating at `x = 0`
  alone forces `exp(T1.eval 0) = 0` — impossible regardless of `T1`'s shape. No constant hypothesis
  needed at all.
- `eml_depth2_witness_of_const_le_one_sibling`: `S2` constant `c2 ≤ 1`, `T1` COMPLETELY ARBITRARY.
  Evaluating at `x = −π/2` forces `exp(T1.eval(−π/2)) = c2 − 1 ≤ 0` — impossible for any `T1`. For
  `c2 > 1` this specific point gives no contradiction (`c2 − 1` could be a genuine `exp` value) —
  this is EXACTLY round 19's failure mode, now localized to a single precise sub-case rather than
  a vague "compound siblings might defeat it."

Net effect: witness-finding for the whole depth-2/leaf-sibling family is closed EXCEPT for exactly
one sub-case — `S2` constant `> 1`, `T1` non-constant. Down from "`T1` must be constant, full
stop" at the start of the day. Both compiled clean (one needed swapping an unavailable `set`
tactic for the file's established `let`+`show` idiom); zero new axioms.

## Update 2026-07-16 (cont.) — both natural broadenings reopen the round-19 wall; a circularity trap identified

Traced (paper only, no code) whether the "collapse + evaluate" technique extends to deeper trees
(offender 3 levels down) or compound `S2` (`= eml P Q`). Both reopen the exact difficulty round 19
found — the collapse trick only telescopes ONE level (`log(exp(v)) = v` simplifies cleanly;
`log(exp(v) − w)` does not), confirmed by direct algebra, not assumption.

Also checked, and REJECTED, a tempting shortcut: `sin_not_in_eml_any_depth` (already a theorem
elsewhere in the codebase) cannot be used to argue "the axiom's hypothesis is vacuous, so it's
trivially true" — that theorem's OWN current proof (`EMLExplicitBoundSinBarrier.lean`) depends on
`eml_pfaffian_validon_from_sin_equality` itself. Using it here would be circular. Recorded so no
future attempt wastes time on it.

## Update 2026-07-16 (cont.) — Option C attempted: no counterexample, but a real generalization

Tried to construct an explicit compound `T1` making the residual `c2 > 1` gap genuine. Every
natural candidate failed for the same reason: compound `T1` choices tried were either secretly
constant (collapses to a fixed number, not a real test) or UNBOUNDED — and unboundedness alone
gives an immediate elementary contradiction, regardless of `T1`'s shape. Built
`eml_depth2_witness_of_const_sibling_unbounded_T1` (commit `475502bf`): if `T1` is unbounded above,
picking a point where `T1.eval x` exceeds `c2+2` forces `exp(T1.eval x)` past the range `sin`
allows, via `exp_grows_strictly_thm` alone — no Khovanskii machinery needed. Covers the ENTIRE
`c2 > 1` gap for compound OR non-compound unbounded `T1`. Zero new axioms.

Net effect: the residual gap is now precisely "`T1` BOUNDED and non-constant, `S2` constant `> 1`"
— narrower than "compound `T1`" was. No counterexample found (weak evidence the general claim may
hold for this shape), but the search itself produced real, reusable infrastructure.

## Update 2026-07-16 (cont.) — periodicity route checked and ruled out as a shortcut

Considered whether the last residual (`T1` bounded, non-constant, `S2` constant `> 1`) could close
via periodicity: the collapse equation forces `T1` to be `2π`-periodic (inherited from `sin`), and
a non-constant periodic function has infinitely many critical points — which looks like it should
contradict a "boundedly many critical points" fact for elementary/EML functions.

Checked the actual infrastructure (`AnalyticFiniteZerosReal.lean`) rather than assuming it would
work. `analytic_open_interval_bounded_zeros`'s zero-count bound is explicitly documented as
**non-uniform** in the interval — it can grow as the interval grows, so extending the periodicity
argument to `[0, 2Nπ]` for large `N` gives no contradiction. The uniform bound this route would
actually need IS the Khovanskii/Pfaffian-chain machinery itself — comparable in scale to the axiom
being closed, not a nearby shortcut. Ruled out; no code written (checking against source first
avoided a wasted build attempt).

## Update 2026-07-16 (cont.) — the mechanism side reached its own capstone; re-scoping this document

After the witness-finding investigation above, the session pivoted to generalizing the ODE
mechanism itself (rounds 25–27, `EMLSmoothness.lean`): first demonstrating it composes across
MIXED left/right descent paths (not just pure-left or pure-right), then generalizing that to
ANY length/shape mixed path (`eml_moves_pos_of_pos_witness`), and finally — the actual capstone —
`eml_pfaffian_validon_of_sin_and_witnesses`, which closes `EMLPfaffianValidOn t x0 b` in FULL
(every node, not one offender) for ANY tree shape, via structural induction on `EMLTree` itself.

**This changes the scope of this document.** It's no longer "how do we find witnesses for the
specific offender shapes closed so far" — the mechanism now handles every tree shape uniformly.
The witness-finding options above (A/B/C) apply UNCHANGED, just now understood to be the ENTIRE
remaining gap for the axiom in full generality, not one piece among several. The one other gap:
`eml_pfaffian_validon_of_witnesses` only reaches `[x0, b)` for `b > x0` (forward from the witness
point) — a backward-direction mirror (mirroring `eml_depth1_pos_of_pos_witness_backward` via
`sup_exists`) is needed to cover `b` smaller than the witness point, i.e. literally "any `b > 0`".
Not yet built; expected mechanical given the session's track record.

## Update 2026-07-16 (cont.) — backward mirror built; a genuine gluing subtlety found, not closed

Built the backward-direction mirror (`eml_pfaffian_validon_of_sin_and_witnesses_backward`,
line-for-line mirror of the forward capstone via `sup_exists`) — mechanical, as expected, one
small fix. Both directions are now independently complete.

Attempting the natural final step — one theorem covering `EMLPfaffianValidOn t 0 b` for ANY `b>0`
from a single witness point `p`, combining forward + backward — hit a genuine gap, not a quick
fix: `EMLPfaffianValidOn`'s definition is a fully OPEN interval `a<x<b`. The backward piece claims
`(0,p)`, the forward piece claims `(p,b)` — their union misses the single point `x=p`, even
though the UNDERLYING mechanisms individually reach `x=p` (their raw conclusions use `≤`, not `<`,
at the witness endpoint — it's packaging into `EMLPfaffianValidOn`'s fixed shape that loses it). A
real fix needs a THIRD combined structural induction, not gluing two packaged results together.
Documented honestly rather than patched with an incorrect proof; not yet built.

## Update 2026-07-16 (cont.) — the gluing gap CLOSED. Mechanism side is complete.

The fix was not a third combined induction gluing two packaged results — it was avoiding the
packaging problem entirely. Built `eml_ode_closure_general_twosided`: takes the witness at an
INTERIOR point `p` directly and covers the whole `(a,b)` via a case split on `x` vs `p` BEFORE any
`EMLPfaffianValidOn` packaging happens, so there's no open-interval endpoint left to lose. Ran the
same structural induction as the forward capstone with this as the base mechanism
(`eml_pfaffian_validon_of_witnesses_twosided`).

**`eml_pfaffian_validon_of_sin_and_witness_at_point`** is the result: given a SINGLE witness
structure `EMLWitnesses t p` at ONE point `p`, `EMLPfaffianValidOn t 0 b` holds for literally ANY
`b > 0` — the exact shape of `eml_pfaffian_validon_from_sin_equality` itself. One small fix
(missing explicit function arguments, a compiler-caught mechanical error). Zero new axioms.

**The mechanism-building side of this whole investigation is now complete.**
`eml_pfaffian_validon_from_sin_equality` reduces, for literally any tree and any `b>0`, to exactly
one hypothesis: `EMLWitnesses t p`. Nothing else stands between "nothing" and the full axiom.

## Status

- Mechanism-building (rounds 1–18, then 25–29 this session): COMPLETE — any tree shape, any
  `b > 0`, from one witness point, zero new axioms beyond `HasDerivAt_congr`. This is the
  endpoint of this line of attack; no further mechanism work is expected to be needed.
- Witness-finding (`EMLWitnesses t p`): the ONE remaining hypothesis, open in general. Depth-2/
  leaf-`S2` family closed except one maximally narrow residual: `T1` bounded and non-constant,
  `S2` constant `> 1`. Probed from three independent angles (direct evaluation,
  growth/unboundedness, periodicity) — all either close cleanly or require Khovanskii-scale
  machinery. This is a well-triangulated boundary, not an unexplored gap.
- Option A: exhausted for this tree shape at the elementary level — the remaining residual needs
  either genuinely new (Khovanskii-scale) machinery or acceptance as a named side-condition.
- Option B: not recommended (see original rationale above).
- Option C: attempted once, no counterexample found, produced a real generalization instead.
  Further attempts would need to target deeper/compound trees specifically, which reopens
  round-19-scale difficulty rather than being cheap.
- This document: living draft. The mechanism side is done; only the witness-finding options above
  remain open for whoever picks this up next.
