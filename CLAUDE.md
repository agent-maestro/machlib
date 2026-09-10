# CLAUDE.md — MachLib

**What this is.** A Mathlib-free Lean 4 corpus that proves things about EML kernels — the little
functional language Forge compiles to hardware — so that claims about compiled silicon rest on
machine-checked theorems rather than on prose.

## Architecture

Everything of substance is under **`foundations/`** (the repo root is docs, evidence, and site
material). `foundations/MachLib/` holds **1 104 `.lean` files** (790 top-level + 314 in subdirectories) /
**251 760 lines** / **7 700 theorems**, re-exported through the aggregator
**`foundations/MachLib.lean`** — a module not reachable from there is **invisible to
`lake build` and to every gate**, which is the single most common way to ship dead work.

The theorem count is exactly this command, run from `foundations/`, and nothing else:

```bash
find MachLib -name '*.lean' -not -path '*/Discovered/*' -exec grep -hcE '^ *theorem ' {} + \
  | paste -sd+ | bc                                    # 7 700
find MachLib -name '*.lean' -exec grep -hcE '^ *theorem ' {} + | paste -sd+ | bc   # 8 420
```

The two differ by **720**, which is `Discovered/`, and that 720 is the cross-derivation that says the
method is right — the same figure was recorded independently when this was last measured.

**Two revisions of this file have carried a theorem count nobody can reproduce**: `5 851` by an
unrecorded method, then `8 231`, which exceeds the largest number the corpus can produce by any
file set (`8 097` as measured when it was caught, every `.lean` outside `.lake`). It is almost certainly the
**unquoted-glob inflation** below. Do not restate a count without re-running the command above.

**`MachLib/Discovered/` (292 files) is deliberately outside the aggregator**: each file is
self-contained and they cannot be imported together; it is the Forge `@verify(lean)` corpus and has
its own harness, `scripts/closerate.sh`. The numeric
substrate is **`MachLib.Real`**, an *axiomatised* real field (274 `axiom` declarations, every one
disclosed in **`foundations/axiom_ledger.json`**): there is no Mathlib, no `Complex`, and
`Real.log` is **totalised** — `log y = 0` for `y ≤ 0`, which is load-bearing in EML proofs and a
frequent source of surprise. Custom tactics **`mach_ring`** and **`mach_mpoly`** replace `ring`/
`linarith`.

## The axiom count, reconciled (do not re-derive this)

`lake env lean AxiomLedger.lean` reports **243 axioms pinned**. That number decomposes exactly, and
grepping the sources will *not* reproduce it:

```
221  MachLib.*   axioms in the environment after `import MachLib`
 22  Certcom.*   IEEE-754 floor axioms
---
243  = what the ledger pins
```

(Re-derive the split with a `#eval` over `getEnv` partitioning `.axiomInfo` by name prefix — that is
how these two were measured, not by grep.)

A further **15** axioms are present but *not* pinned — they are Lean's own kernel/compiler trust
base, not project axioms: `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `Quot.lcInv`,
`Lean.{ofReduceBool,ofReduceNat,trustCompiler}`, `isScalarObj`, and the `lc*` compiler internals.

**Why grep disagrees:** `grep -c '^ *axiom '` over `MachLib/*.lean` returns **278** (511 including
subdirectories, which the environment mostly does not see). When this was last decomposed by hand the
gap was docstring prose plus axioms in unreachable modules; those two sub-counts are **not**
re-derived here and should not be quoted as current. Use the environment (`getEnv`, `.axiomInfo`), never grep —
this is the same rule as *"axiom-absence claims must be read off `#print axioms`."*

## How many of them are MODELED (the number a reviewer actually wants)

The count above says how many axioms there are. It says nothing about whether they are
*satisfiable* — and a disclosed-but-misstated axiom is worse than an undisclosed one, because the
disclosure buys confidence the statement has not earned. The honest headline is **"zero unmodeled
axioms"**, never "zero axioms".

The check cannot live here: MachLib is Mathlib-free, so nothing inside it can exhibit a model.
It lives in the sibling project **`monogate-lean`**, which imports *both* Mathlib and MachLib and,
for each trusted axiom, verifies a Mathlib term inhabits the axiom's **interpreted type**
(`MachLib.Real ↦ ℝ`, `exp ↦ Real.exp`, …). That is a certificate *about* MachLib, never a
dependency *of* it — the Mathlib-free property is untouched.

Current state — read `foundations/AXIOM_MANIFEST.md`, which is **generated**, one row per axiom:

| class | n | |
|---|---|---|
| witnessed | 112 | a Mathlib term inhabits the interpreted type, kernel-checked |
| mapped | 12 | carrier/function symbols — interpreted, not propositions |
| standard | 3 | `propext`, `Classical.choice`, `Quot.sound` |
| **float-bridge** | **22** | about IEEE floats — **no Mathlib witness can ever discharge these** |
| tracked gap | **0** | closed 2026-09-02; every witnessable axiom is witnessed |
| unmodeled | **0** | gate 13 fails if this is ever nonzero |

**Every mathematical axiom in the trusted footprint now has a kernel-checked Mathlib witness.**
`112 + 12 + 3 + 22 = 149`. The only axioms without one are the 22 float-bridge rows, which are
unwitnessable *in principle* rather than pending — see below.

**The 22 float-bridge axioms are a different kind of trust and must not be averaged in.** They
assert a concrete float `exp`/`atan`/`sqrt` rounds to within `ε` of the real function. Mathlib has
no IEEE-754 semantics, so they are validated by *measurement*, not by a model. **This is what a
hardware certificate actually rests on** — anyone shown an atan/tan bench certificate should be
pointed at that block first.

> **It went dark once, for 33 days, and nothing said so.** MachLib moved to Lean v4.32.2 on
> 2026-07-31; `monogate-lean` stayed on v4.14.0. Because it requires MachLib *by path*, it was
> compiling MachLib's current source under the old toolchain and could not build — while the
> ledger went on reporting "trusted", because "trusted" meant *listed* and the thing that turns
> listing into evidence was not running. Its `trustedFootprint` was also a hand-pinned snapshot
> (78 names against a live 149) whose own cross-check passed **against the copy**. When it was
> finally rebuilt it rejected two witnesses immediately — Mathlib v4.32 had *flipped*
> `add_lt_add_left` to add on the right. **Gate 13 (`tools/soundness_witness_audit.py`) now fails
> on toolchain skew between the two repos**, on any trusted axiom with no witness and no
> classification, and on a stale excuse entry. Never re-pin that footprint by hand.

## Where the content comes from

Self-contained. EML semantics live in `MachLib/SinNotInEML.lean` (the `EMLTree` type and `eval`);
the forward-error certifier is documented in `foundations/docs/forward_error_certifier.md`; the
authoritative claim inventory is **`foundations/docs/what_is_proven.md`**.

## How to run the gates

**All seven run from `foundations/`, not the repo root** (this is what CI does):

```bash
cd foundations
lake build                                     # 803 jobs, ~3 s warm
bash scripts/check_aggregator.sh               # every module reachable
bash scripts/check_consistency_model.sh        # flagship closure has an external ℤ-model
bash scripts/check_discovered_compiles.sh 4    # the 292 Forge @verify files still compile (~1 min)
lake env lean AxiomLedger.lean                 # "243 axioms pinned; 57 headline footprints ⊆ trusted"
python3 tools/claim_audit/claim_audit.py       # "all 506 claims resolve against #print axioms"
bash tools/check_obligations.sh                # EMLDepthTameness's open/discharged rows ↔ the corpus
```

`python3 tools/witness_audit.py` is the newest **measurement harness** and is likewise **not** a CI
gate. It reports every registered claim-theorem that takes hypotheses and is referenced nowhere else
in `MachLib/` — i.e. nobody has ever supplied its hypotheses. That is the one signal that was present
and unread when `positive_branch_impossible` was vacuous: it had no caller and no specimen. The
baseline is pinned as a **set** (`tools/witness_baseline.json`, 65 entries), not a count, so the
ratchet turns one way — a new entry fails, a witnessed one must be removed. It carries two convict
specimens of its own. Read its scope note before trusting it: no-caller is not a defect on its own,
and it cannot see vacuity, only drift.

> **It counted PROSE as an instantiation until 2026-09-06, and its own motivating example was one
> of the false positives.** `corpus_text()` concatenated the `.lean` files raw, so a theorem was
> "witnessed" if its name appeared anywhere at all — and this corpus cross-references itself in
> docstrings constantly. Stripping comments moved the true count from 35 to **65**:
> **30 registered capstones had no code use whatever**, among them `positive_branch_impossible`,
> which appears 17 times in `MachLib/` as one declaration and sixteen comments. The audit built
> after that theorem was found vacuous was being satisfied by the prose written about it.
> The baseline was re-set **once** for the instrument fix, every added entry annotated
> `prose-only`; the ratchet turns one way from there. Found because a docstring cross-reference in
> an unrelated commit flipped a capstone to "witnessed", and ratcheting it down would have
> recorded an instantiation that does not exist.

`python3 tools/hypothesis_audit.py` is `witness_audit`'s **mirror**, and also not a CI gate. Where
the witness audit finds *capstones nobody instantiates* (a conclusion with no consumer), this finds
**propositions consumed as hypotheses that nothing ever concludes** — a premise with no producer.
Both are "conditional theorem, unvalidated"; only one had a harness until 2026-08-27, when
`ValueGapBound` was introduced, taken as a hypothesis by two theorems, and satisfied by nothing at
any depth. **A Prop with consumers and no producers is not exercised; it is assumed** — and that is
the easy half to miss, because the consumers make it look exercised. Baseline
`tools/hypothesis_baseline.json`, 33 entries, a **set** not a count. Read its triage note before
trusting a hit: most entries are correct (named open obligations belong there, and definitional
predicates like `Lipschitz` are supplied from outside rather than proved). What to watch for is a new
name that is *neither*.

`python3 tools/absence_audit.py` closes the gap this file names two paragraphs down: the claim
auditor *"is structurally blind to a claim about a theorem that does not [exist]"*, and
`check_obligations.sh` covers **one** case of that. The general shape — *"these lemmas do not exist
here"*, *"the existing machinery cannot answer this"* — was checked by nothing and **decays
silently**: someone adds the thing, and the sentence saying it is missing keeps reading as true.

It registers each absence claim with **something that could falsify it** (`tools/absence_claims.json`,
11 entries) and fails when that thing starts holding. Two check kinds, and the difference matters:

* **search** — a regex, for *"no such declaration"*;
* **probe** — a Lean snippet that must FAIL to compile, for *"no such tactic"*. A grep for
  `^syntax "linarith"` proves nobody *declared* it here; only compiling proves it is **unavailable**,
  which is what the gotcha actually claims, since a tactic can arrive from a dependency. `by_contra`,
  `conv_lhs` and `set`/`linarith`/`ring` are all registered this way and verified by compilation.

A probe that fails for the *wrong* reason is reported broken, not passing — a typo in a probe would
otherwise read exactly like the absence it was meant to establish. And a claim registered with
**neither** is `UNAVAILABLE`: an absence claim nothing can refute is not checked, merely written down.

Not a CI gate yet; five canaries including a control, and — more to the point — a **firing specimen
against a real defect**: run against this file's former *"`min` and `abs` do not exist"*, it reports
`NOW-FALSE, 2 hits`.

**It found three false claims in this file on its first pass** (`mul_lt_mul_of_pos_left`, `min`,
`abs` — all three exist, and the `min`/`abs` entry told the reader to hand-roll a replacement). An
unchecked absence claim is not merely stale; it costs work. Registering one *without* a falsifying
search is the anti-pattern the registry exists to discourage.

`lake env lean tools/sorry_audit.lean` is useful (`1 sorryAx`, allowlisted) but is **not** a CI gate,
and note its scope: it walks the **environment** after `import MachLib`, so it cannot see
`Discovered/`. Neither is `scripts/closerate.sh`, which is a *measurement* harness (close-rate,
79.9% at the last sweep), not pass/fail. The CI gate set is exactly the seven above
(`.github/workflows/build-time.yml`).

Note what the last two gate, because it is *not* the same thing. The claim auditor pins prose to the
axiom footprint of a theorem that **exists**; it is structurally blind to a claim about a theorem
that does not — including "this obligation is still open". `check_obligations.sh` covers that one
case: it fails if a row says open and the corpus disagrees, or says discharged and the cited theorem
does not conclude the proposition. Neither gate can tell you a claim with no registered theorem
behind it is missing — registration is still a human act.

## Gotchas

- **`lake` from `foundations/`.** From the repo root it silently resolves the wrong toolchain (v4.14).
- **Stale `.olean`s.** `lake env lean Foo.lean` typechecks against *old* dependencies; run
  `lake build MachLib.Foo` first or `#print axioms` will report unknown constants.
- **A new module must be REACHABLE from `MachLib.lean`** or it is never built and never gated.
  Being imported by a sibling is **not** enough — an island of mutually-importing modules is
  unreachable. `check_aggregator.sh` does a real transitive closure (**800 of 1104 reachable**).
- **`open Real` shadows `max`** — write `Nat.max`, and feed `omega` the `Nat.le_max_*` lemmas.
- **`set`, `linarith`, `ring` do not exist here.** Use `mach_ring` / `mach_mpoly`.
- **`by_contra` does not exist here either** — reach for the contrapositive lemma instead
  (`Real.mul_left_cancel`, `Pdvd_of_peq`, …). It is gated by its own compile probe,
  `by-contra-absent` in `tools/absence_claims.json`, and it has still cost a compile three times.
  The failure is **not** a missing check, it is not consulting one that already exists: read the
  absence registry before reaching for a tactic.
  (Kept as a separate bullet on purpose — the line above is the literal anchor of
  `claudemd-tactics-absent`, and rewording it edits the guard rather than the claim.)
- **Keep coefficients symbolic.** `mach_mpoly` times out on `16·P²` and proves `(c·c)·(a·a)` instantly.
- **EVERY INSTRUMENT MUST BE SHOWN CAPABLE OF BOTH VERDICTS BEFORE EITHER IS READ.** One rule, two
  halves, and it covers every failure this corpus has paid for:
  * **positive control** — run the pattern against a line you *know* matches before believing
    "zero matches". A pattern that cannot match returns exactly what a true absence returns:
    `PIrred \[` can never match `PIrred ([0, 1] : List Real)`, and a `ugrep`-rejected backreference
    prints nothing at all.
  * **negative control** — feed the checker a known-bad input; if it passes, the run is worthless.
    This is what `sorry_audit.lean`'s allowlisted RED skeleton *is*, and what
    `check_aggregator.sh --selftest`'s canaries are.

  Instruments that can only return one value: an errored grep, a `lake build` over a
  heredoc-gutted docstring, a launcher exiting 0 while `GATE_RC=127`, a seed grid reported as a
  census, a cut-off reported as a property of the object. Same defect, five costumes.
- **Never chain a measurement to the commit that quotes it.** `measure && git commit -F-` puts the
  number in the message from *expectation*, and verifies it afterwards or not at all. It was correct
  three times running on 2026-09-01, which is what makes it a habit rather than an obvious error.
  Measure, **read the output**, then commit as a separate command — the same rule as gate-then-act,
  turned on the commit message.
- **A green gate line is a claim about the gate's SCOPE, not about your theorem.** `witness_audit.py`
  excludes theorems concluding `False` **by design** — it now prints how many (60) it cannot examine,
  rather than leaving `OK` to read as coverage. Check your theorem is in the class a gate examines
  before citing it.
- **DO NOT EDIT THE TREE DURING A GATE RUN — and the freeze you can see is not the only one.**
  `check_all.sh` fingerprints `git status --porcelain | sha1sum`: a NAME-and-STATUS list.
  `claim_audit.py` keeps its **own, stricter** fingerprint that also hashes the **CONTENTS** of every
  dirty file — added 2026-08-23 for exactly the case the weaker one misses, and pinned by its
  canary 14. So editing an **already-dirty** file mid-run leaves the porcelain hash **byte-identical**
  while the audit's moves, and the audit returns **rc 2** (UNAVAILABLE, never a pass) while still
  printing its green `CLAIM-AUDIT PASS` line. `check_all.sh` then reports
  *"gates green, but 1 could not run — treat as UNKNOWN, not PASS"* and the whole ~25-minute run is
  void. Cost one full run on 2026-09-07, and the reasoning that lost it was *careful*: the porcelain
  fingerprint was checked before and after the edit and was genuinely unchanged. **Verifying the
  weaker of two guards does not license the edit.** Wait for `GATE_RC`, then edit.
- **`cmd | head; echo $?` reports `head`'s status.** Live instance 2026-08-31: a grep that matched
  nothing reported `rc=0` inside the very check meant to settle whether it matched. Use
  `${PIPESTATUS[0]}`, or redirect to a file and test that.
- **Write files with a QUOTED heredoc (`<<'EOF'`).** Unquoted, bash executes every backticked token
  in the body, so a Lean docstring lands with **every backticked name deleted** — and `lake build`
  passes anyway, because Lean does not read docstring content. Pass paths via `export VAR` +
  `os.environ`, never by interpolating into the body. After a heredoc write, read back the
  *docstring*, not just the part the compiler checks.
- **Deep `rfl` needs `set_option maxRecDepth`** (29 M-node terms check fine at 40 000 000).
- **Axiom-absence claims must be read off `#print axioms`, never a name-grep** — `exp_gt_one_plus_self`
  and `exp_tangent_line_strict` are the same content under two names.
- **`open MachLib.Real` + `open …AerospaceActuatorGuardBandRate (le_min …)` collide.** Both export a
  `le_min`; a bare `apply le_min` is then ambiguous. Qualify it. (This broke 5 `Applications/`
  modules for an unknown length of time — they were in an unreachable island, so no gate saw it.)
- **These order lemmas do NOT exist here**: `lt_or_ge`, `lt_trans`, `lt_irrefl`, `le_or_lt`,
  `add_lt_add_right`. The local idioms are `rcases lt_total`, `lt_of_lt_of_le … (le_of_lt …)`,
  `(ne_of_lt h) rfl`, `add_le_add_wit`, `add_lt_add_left`.
  (`mul_lt_mul_of_pos_left` **was on this list and does exist** —
  `WitnessResidualGrowthCompetitionNumeric`. Removed 2026-08-28; registered in
  `tools/absence_claims.json` so the remaining five are re-checked rather than trusted.)
- **A new module needs `open Real`** inside `namespace MachLib`, or `exp`/`log` are unknown.
- **Casing on a tree then applying a lemma with an implicit tree argument leaves a metavariable** —
  pass `(A := EMLTree.const c)` explicitly, or the shape-specific proof term fails to typecheck.
- **Forward references bite**: a theorem is only usable *below* its declaration in the same file.
- **`min`, `max` and `abs` DO exist** — `MachLib/Basic.lean`, under `namespace MachLib.Real`, and
  they are used (`abs` in `EMLFTranscendence`, `min` across `Applications/`). This entry previously
  read *"`min` and `abs` do not exist"* and told the reader to hand-roll `two_bound_witness` instead.
  **That was false and cost work**; it is the finding that motivated `tools/absence_audit.py`.
  `two_bound_witness` is still the right tool when you need a value strictly *below both* of two
  positives without a case split — which is a different job from `min`.
- **`mach_mpoly` stalls in `Lean.Meta.acLt` when nested `(1+1)` constants must be DISTRIBUTED over
  sums.** Four specimens pin it: nested `64` under pure commutativity is fine (1 s); the same
  constant in a degree-3 identity with subtractions dies (69 s at 4 000 000 heartbeats); the
  identical identity with `natCast` constants **completes in 1.9 s**; so does the flagship numeral
  obligation (2.3 s) that previously exhausted the same budget. So it is the encoding under
  distribution, not degree, not presentation, and not constants per se.
  **First try splitting the call**: keep each binomial product atomic (bind it to a variable) so no
  single call distributes two brackets — a degree-3 identity that died at 4 000 000 heartbeats
  closes as four ~1 s steps that way.
  **Otherwise:** write constants as `natCast N`; `mach_mpoly` then treats each as one atom and
  normalises fine, but cannot do their arithmetic — supply products via
  `rw [← natCast_mul]` (instant, `Nat` literal equality) *before* calling it.
- **`first | … | …` does not backtrack out of errors inside a nested `by` block** — only out of
  tactic failure. A branch whose `mach_mpoly` makes partial progress and then errors is committed
  to, not abandoned. Use explicit per-case bullets when the branches are genuinely different proofs.
- **`OfNat Real` exists only for `0` and `1`.** `(2 : Real)` does not elaborate. Write constants as
  `natCast N` (`NatCastArith`), **never** as `1+1+…`: `mach_mpoly`'s AC matching diverges on unary
  numerals — a degree-2 identity with constants near `1.4·10⁴` exhausted 4 000 000 heartbeats (20×
  the default) without progress. This is the operational form of "keep coefficients symbolic".
- **A literal `-0` (or `0 * t`) makes `mach_mpoly` GRIND, not fail.** Instantiating an existential
  constant at `0` produced `-(0 : Real) + -exp (exp x) = -0 - exp (exp x)`, and the normaliser did not
  finish inside a ten-minute build (2026-09-04). Any other witness — `1` — compiles in seconds. The
  tell is a build that *hangs*: `mach_mpoly` fails fast on goals it cannot close, so a long-running
  one is a normalisation blow-up. When `0` is genuinely needed, rewrite with `zero_mul`/`zero_add`
  (axioms) before any normaliser sees it.
- **`pgrep -f "lake build"` / `pkill -f pattern` MATCH THE SHELL RUNNING THEM** and have killed the
  session twice on one day (2026-09-04). Use `ps -eo pid,args | grep -F <pattern> | grep -v grep`.
- **`forbid_axioms` in `claims.json` is a SUBSTRING match, not a name match.** It is what lets one
  entry forbid a family (`"analytic_"`), but it also means `analytic_finite_zeros` forbids
  **`analytic_finite_zeros_compact`** — and the compact one is the only one that exists as a
  declaration. Copying the usual `sorryAx / zero_count_bound_classical / analytic_finite_zeros` trio
  onto a claim whose theorem legitimately rests on the compact axiom makes the gate **fail a true
  claim** (cost me a full audit cycle on 2026-08-29). For the reverse containment — a sound axiom
  whose name contains an unsound one, `rolle_ct` ⊃ `rolle` — use `forbid_axioms_exact`, which matches
  whole tokens. Audit a new entry alone first: `claim_audit.py --registry <two-entry file>` takes
  seconds where the full registry takes many minutes, and it lets you run the convict copy too.
- **A theorem whose conclusion is a ledger obligation needs a BINDER, not an arrow.**
  `tools/obligation_ledger_check.py` reads a conclusion as the tail after the last top-level `:`,
  having first stripped binders of the obligation's own type. So `foo : A → B` has tail `A → B` and
  is counted as a **discharger of `A`** — if `A` is a *refuted* row the gate reports a contradiction
  that does not exist, and if `A` is *open* it reports the row as stale. Write `foo (h : A) : B`,
  which strips correctly. (`depth3DecayExp_of_hard` is the worked case; both forms were run against
  the parser before choosing.)
- **A CONDITIONAL THEOREM IS NOT EVIDENCE UNTIL ITS HYPOTHESES ARE INSTANTIATED.** Two hypotheses in
  the `S > 0` pole layer were *unsatisfiable for every `q`*, so the flagship
  `positive_branch_impossible` was vacuously true and proved nothing — and **every gate passed**, for
  weeks. `False → P` is provable, cites no bad axioms, and discharges any obligation. Build a
  **specimen** (`GermClearedSpecimen`) discharging every hypothesis, and ship it with the capstone;
  it then fails to compile if a hypothesis ever becomes unsatisfiable again. Tell-tale before it was
  found: the capstone had **no caller and no specimen anywhere**.
- **Suspect `∀ n` hypotheses at indices nobody consumes.** `∀ r, DerivCoprime q r` was false at
  `r = 0` (`pnsum 0 _ = []`, and everything divides the zero polynomial) while every proof site used
  `r + 1`. If no site applies a hypothesis at index `k`, ask whether it *holds* at `k`.
- **`pderiv` is LENGTH-PRESERVING, so its output always carries a trailing zero** (`pderiv [a,b] =
  [b, 0]`) and is **never `PNormal`**. Any hypothesis asserting canonicity of a `pderiv`/`pnsum`
  image is unsatisfiable. Use `pnorm` first, or a normalisation-invariant lemma — `euclid_lemma'`
  drops `euclid_lemma`'s `PNormal` side condition entirely, since `Pdvd` already sees only `pnorm`.
- **`obtain` on a `GEvEq` entry against `expCoeffs` yields an UNREDUCED application** —
  `a x = (fun C x => bipev C x (exp (S x))) C x` — so `rw [← e]` will not match the beta-reduced
  goal. Bind it through a typed `have e' : a x = bipev C x (exp (S x)) := e x hx`.
- **`find … -not -path '*/Discovered/*'` UNQUOTED silently double-counts.** The shell expands
  `*/Discovered/*` against the working directory before `find` sees it, so `-not -path` excludes one
  matched file and every *other* match becomes an extra search root — the same files are then walked
  twice. **Measured once, 2026-08-28, under `bash` from `foundations/`**: quoted **7 393**, unquoted
  **8 888**. Deliberately *not* refreshed with the other counts, because the figure is fragile in
  exactly the way it documents — a script recomputing it broke twice, and the reason is worth more
  than the number: **the unquoted form gives 8 888 under `bash` and NOTHING under `sh`**, since the
  two shells differ on an unmatched glob. So it varies with the corpus, the working directory *and*
  the shell. It fails *upward* under bash and reads as a bigger corpus, which is why it survived into
  this file.
  Sanity check any corpus count against the all-files total; an "excluding X" figure that exceeds it
  is impossible.
- **A gate's own self-test can go stale when the corpus improves.** `obligation_ledger_check.py`'s
  canary 9 is a literal specimen, and its `open` row must name something no theorem can conclude —
  it named live obligations twice and both were discharged the same day, failing the gate because
  work succeeded. `discharged`, `refuted` and `reduced` specimens are stable; `open` is not.

- **A GRINDING TACTIC DOES NOT JUST BURN TIME — IT CAN TAKE THE MACHINE DOWN, and `maxHeartbeats`
  does not bound it.** On 2026-09-08 this box (121 GB RAM, 16 GB swap) went unresponsive and was
  power-cycled by hand. The journal settles the cause: in **13 days of uptime there were exactly
  two days with any memory pressure at all** — Sep 05 (598 events, ending with VSCode OOM-killed,
  which is the "vscode crashed" of that session) and Sep 08 (608 events, starting 14:35:04, power
  key pressed 27 minutes later). Both are days this corpus was worked on; no other day produced a
  single event. Nothing was OOM-killed on the 8th, because the kernel never got the chance — the
  desktop stopped responding first.
  **Measured, same day:** one `lake env lean` on ONE emitted Forge artifact peaks at **3.4 GB RSS**.
  Adding ONE `mach_linarith` arm to ONE theorem's closer alternation takes it to **7.8 GB**, and it
  still only reaches the heartbeat timeout rather than a conclusion — a wide `first | … |` pays for
  every arm that fails. The trap is the obvious next move: when a proof times out you RAISE
  `maxHeartbeats`, which buys the grinding tactic more time **to allocate**. The budget is denominated
  in heartbeats and **nothing is denominated in bytes**.
  This is the resource face of gotchas already in this file (`mach_mpoly` GRINDS rather than fails on
  a literal `-0`; the tell is a long run, not an error). What is new is that the blow-up escapes the
  build. **Run exploratory elaborations through `tools/capped_lean.sh`** — a transient scope with
  `MemoryMax` and no swap, so a runaway is killed by its own cgroup and the desktop survives. It
  reports a kill as a RESOURCE verdict in as many words, because a killed run read as a failed proof
  is this corpus's five-costume "instrument that can only return one value" all over again.
  Three canaries (`--selftest`): a hog is killed, a control survives, an ordinary exit status passes
  through. Default cap 16 G, per invocation — parallel harnesses multiply it.

- **`mach_decimal` PROVES `0.5 + 0.5 = 1.0` AND DOES NOT PROVE `0.5 + 0.5 = 1`.** The two differ
  only in how the right side is spelt: `1.0` is `realOfScientific 10 true 1`, `1` is the `OfNat`
  literal, and `Basic.lean` bridges them **by axiom** (`realOfScientific_one_dot_zero`) rather than
  by computation. Nothing in the decimal simp set crosses that line, so the tactic stalls one
  rewrite short and leaves `1 = realOfScientific (5 + 5) true 1` open — which reads exactly like
  "the fact is false" rather than "the tactic stopped". Use **`mach_decimal_ofnat`**
  (`MachLib/Decimal.lean`), which retargets the goal through the bridge first. `OfNat Real` exists
  only for `0` and `1`, so `2`/`3` arrive as `1+1`/`1+1+1`; those bridges are covered too.
- **`first | mach_ring | X` IS WRONG WHENEVER `mach_ring` CAN PARTIALLY SUCCEED.** On
  `1*0.5 + 1*0.5*1 = 1` it normalises to `0.5 + 0.5 = 1` and stops. It does **not fail**, so
  `first` counts the arm as successful and never tries `X` — the goal is simply left open, and the
  error surfaces later as "unsolved goals" pointing at the wrong place. Sequence instead:
  `(try mach_ring) <;> mach_decimal_ofnat`. This is the sharper form of the `first`-does-not-
  backtrack entry above: the hazard is not only an arm that ERRORS, it is an arm that makes
  PROGRESS without closing. Cost an hour on 2026-09-08; found only because the isolated tactic
  worked and the alternation did not.
- **`affine_lower` / `affine_upper` (`MachLib/Linarith.lean`) are what let a Forge caller USE its
  callee's proved range.** `A ≤ a + b·x ≤ B` from `b ≥ 0` and `lo ≤ x ≤ hi`, with the endpoint
  values arriving as *hypotheses* (`A = a + b·lo`) rather than being computed. That is deliberate:
  a kernel's declared bound is written in its own constants (`AUDIO_CENTER_HZ * (1 - AUDIO_SPAN)`,
  not `220.0`), so left as an equation it is a pure ring identity with every constant an opaque
  atom, and decimal arithmetic is needed only when the bound is a bare numeral. Forcing the
  literals early would push decimal arithmetic into every step. Forge emits these for callers that
  compose; see forge's CLAUDE.md for the emission side.

- **A LEMMA STATED IN `OfNat` FORM CANNOT UNIFY WITH A DECIMAL GOAL, AND NOTHING REPORTS IT.**
  `OfNat Real` exists only for `0` and `1`, so this corpus states band lemmas over
  `(1+1+1) - (1+1)*s`. Forge emits `3.0 - 2.0*t`, which elaborates to
  `OfScientific.ofScientific 30 true 1`. Same number, different term, no unification, no
  diagnostic — the lemma simply never fires, and the goal it can no longer reach gets written up
  as needing new mathematics.
  **It cost a theorem for months.** `smoothstep_le_one` has been here for years, built on the
  certificate `1 - s²(3-2s) = (1-s)²(1+2s)` (`one_sub_smoothstep_factored`), while Forge's
  CLAUDE.md recorded that same bound as wanting "a real polynomial-positivity route". Nothing was
  missing. `smoothstep_nonneg`'s docstring *still* claims it "matches the form Forge emits" — it
  did, until the emitter changed under it. **A stale docstring asserting compatibility is worse
  than none: it is the thing you check before concluding the lemma is unusable.**
  Use **`mach_ofnat_numerals`** (`MachLib/Decimal.lean`) to bridge the spelling. It covers `2.0`
  and `3.0` only, because `OfNat` reaches no further and those are the band-lemma coefficients.
  Generalisation of the rule already in this file under `iterate_affine_bound`: **check whether
  the lemma EXISTS and cannot UNIFY before pricing new mathematics.** On 2026-09-08 that rule
  would have saved three separate wrong diagnoses in one session.

- **`BoundedGermTranscendence`: route `(fm)`'s three legs now all stand — and that is an ASSEMBLY, not
  the obligation.** The legs to `not RatGerm (log ∘ S)` are (1) differentiate the germ identity
  (`deriv_eq_of_eq_on_ray`, `GermDerivFbasis`), (2) clear denominators (`LogDerivCleared`, added
  2026-09-08), (3) promote a pointwise identity to `PEq` (`peq_of_ev_eq`, `PevEvEq`). Leg 2 was the
  untouched one; its content is that two rational functions agreeing on a ray have equal
  cross-products *as polynomials*, and it mentions neither `log` nor `S`.
  **`logderiv_count_composes` is the join, by instantiation** — `logderiv_cleared`'s conclusion is
  syntactically `no_rational_logarithm`'s `hident`, and rather than assert that, the module
  typechecks the composition. 31 axioms, algebra spine only: no `sorryAx`, no `HasDerivAt`, nothing
  analytic. That standard comes from `(fk)`, where a duplication audit was "a reading of two files"
  until it became two typechecked instantiations.
  **ASSEMBLED 2026-09-08** (`LogGermAssembly`, `no_rational_log_germ`): a rational germ `S = P/Q`,
  positive on a ray, whose denominator has a genuine pole at an irreducible `q`, admits no rational
  germ for `log ∘ S`. 44 axioms, no `sorryAx`, nothing analytic. Every step was already present —
  the two derivative rules (`logComp_hasDerivAt`, `div_hasDerivAt`, `DerivQuotientLog`) were built
  for this route and I nearly rebuilt them; the only arithmetic added was `logderiv_normalise`,
  turning `logComp_hasDerivAt`'s `s / S x` into one fraction over `P·Q`.
  **`witness_audit` IS STRUCTURALLY BLIND TO IT.** The theorem concludes `False`, so it lands in the
  audit's *"refutation theorem(s) NOT APPLICABLE"* bucket — a green `WITNESS-AUDIT OK` says nothing
  about it, which is precisely the position `positive_branch_impossible` was in while vacuous for
  weeks with every gate green. So `no_rational_log_germ_specimen` discharges every hypothesis
  **except** the one being refuted, at `S = 1/x`: a full specimen is impossible on purpose, and what
  needed showing is that the premises are not contradictory for some unrelated reason.
  **Both pole positions are covered.** `no_rational_logarithm` needs the pole in the DENOMINATOR,
  so `no_rational_log_germ` alone is silent on `S = x` (`Q = 1`, no irreducible divides it).
  `no_rational_log_germ_num_pole` runs the same theorem on `1/S = Q/P`, and the only germ-level
  content is `log_recip_germ`: inverting a rational germ NEGATES its logarithm (`log_div` twice,
  then `neg_div`). Together they cover every non-constant rational germ in lowest terms — `S`
  non-constant means `P` or `Q` is non-constant, hence has an irreducible factor, and lowest terms
  says that factor misses the other.
  **UPGRADED to the germ form 2026-09-09** (`not_ratGerm_log_of_pole`): `¬ RatGerm (log ∘ S)`
  outright, not merely "this named `N/D` fails". The gap was that `RatGerm` hands over an ARBITRARY
  `N`, `D` while `no_rational_logarithm`'s `q ∣ D` branch needs lowest terms at `q`;
  `CrossIdentities.exists_common_ord_split` peels the common `q`-power and returns exactly that.
  Two things make the peel free: the cancelled factor is non-zero on the ray because `pev D` is (a
  product vanishes only if a factor does — no root-counting), and the degenerate `N ≡ 0` case is a
  separate three-line argument, not a nuisance (it forces `P/Q ≡ 1` by `exp_log`, hence `q ∣ P`,
  contradicting the pole hypothesis). 47 axioms, no `sorryAx`, nothing analytic.
  **The ledger did not move and must not be read as if it had** — still 4 distinct open obligations.
  `BoundedGermTranscendence` consumes `not RatGerm (log ∘ S)` through further steps that are not this
  module.
  **The separation is proved too** (`log_separation`, 2026-09-09): from `A + B·log (S x) ≡ 0` with
  `A`, `B` RATIONAL germs and `log ∘ S` not one, `EvZeroF B`. The rationality of `B` is not
  decoration — "not eventually zero" gives a general germ NO zero-free tail, and the division needs
  one; `evNonvanish_pev` supplies it only because `B = pev U / pev V`.
  **The rationality bridge is written too** (`ratGerm_pev`, `log_separation_pev`): `GEvRel` and
  `GProperRel` put NO rationality constraint on their coefficients — they are arbitrary germs — so
  the hypothesis does not come from the germ layer. It comes from the obligation, which supplies
  POLYNOMIAL coefficients (`bipevLead A Ls`), and a polynomial is a rational germ with denominator
  `1`. Easy to assume rather than write, which is why it is its own theorem.
  **What is still NOT done, and a fork to settle before doing it.** Every named route-A step is a
  theorem, but nothing derives `A + B·log (S x) ≡ 0` from anything, and there are TWO candidate
  equations needing DIFFERENT inputs. `fbasis_top_two_identity` concludes over `exp (S x) + 1/S x`
  and contains no `log`; separating it would need `¬ RatGerm (exp ∘ S)`, which the bounded branch
  cannot supply — every exclusion instrument here argues by growth and
  `polyEnvelope_of_Fbasis_floor` proves `F ∘ S` IS polynomially enveloped there.
  `fbasis_relation_substituted`'s coefficients DO carry `log`.
  **The fork is RESOLVED** (`top_two_multiplier_splits`, 2026-09-09): the multiplier is
  `s·u + fbasisSubMul S s`, so in `A + B·log` form the top-two identity has `A` carrying
  `u = exp ∘ S + log ∘ S` — not a rational germ on this branch — while `log_separation` needs
  `RatGerm A`. So it does NOT apply to the top-two identity, and the substituted coefficients are
  the only candidate. That took one small ring identity; it was held as an explicitly-marked
  inference for exactly one step first, which is what kept a guess out of this file.
  **The wiring is written** (`substituted_coeff_splits`): each coefficient of the substituted
  relation is `A + B·log (S x)` with `A = es[j] + (s·(0::gyd cs))[j] + s·(1/S)·(gyd cs)[j]` and
  `B = −s·(gyd cs)[j]`, both EXHIBITED rather than asserted to exist — the separation needs them to
  be rational germs, and that is a property of the exhibited expressions.
  **`RatGerm` is now closed under the field operations** (`ratGerm_add`, `ratGerm_mul`,
  `ratGerm_neg`, 2026-09-09) — the corpus had NONE of these, only `ratGerm_sub_const`. They are what
  turns "those `A`, `B` are built from rational pieces" into a proof, and they are reusable well
  beyond this route since `RatGerm` is the level-0 class the germ layer is stratified by.
  **The instantiation infrastructure is complete too**: `ratGerm_of_pev_div` and
  `ratGerm_inv_of_pev` for `s = S'` and `1/S`, and `allRatGerm_gadd`/`_gscale`/`_gyd` carrying
  coefficientwise rationality through the list operations. Those three are stated over MEMBERSHIP,
  not indices, on purpose: `gadd`'s elements are heads, tails or sums, which membership sees
  directly, while an index statement must case on the two lists' relative lengths at every step.
  **The composition is written** (`substituted_coeff_log_part_evZero`): a substituted coefficient
  that vanishes on a ray has `EvZeroF` `log`-part, i.e. `EvZeroF (−s·(gyd cs)[j])`. 36 axioms, no
  `sorryAx`, nothing analytic.
  **Prefer `crossDiff_log_part_evZero`, and here is why the other one nearly did not apply.**
  Checking what the descent supplies showed the vanishing on offer is NOT of a substituted
  coefficient: `GermDerivEntry` builds `gscaleSub cd dtop cs₀ ds₀`, entries `cd·d − dtop·c`, and
  minimality kills those. The separation survives — `cd·(A + B·log S) − dtop·c` is
  `(cd·A − dtop·c) + (cd·B)·log S`, still linear in `log` — so the cross-difference version is the
  one a caller can reach for.
  **The vanishing is available too** (`minimal_crossDiff_evZero`): minimality kills every entry of
  `gscaleSub cd dtop cs₀ ds₀` — `gcancel_top` then `all_gcoeffs_evZero_of_shorter'`, three lines
  that existed only INSIDE `minimal_grel_identity`'s proof and are now a theorem.
  **And it must be run on the SUBSTITUTED list, not `gdrel`.** `gdrel v cs es = gadd es (gscale v
  (gyd cs))` carries `v = (exp (S x) + 1/S x)·s x`, so its coefficients carry `exp`, and
  `top_two_multiplier_splits` already showed that shape is not separable. The substituted list is a
  DIFFERENT list with the same `gbipev` at `Fbasis ∘ S` whose coefficients carry `log`. Both
  descent lemmas are generic in the relation, so nothing stops running them there — that is how the
  two threads meet, and it is the answer to the fork this file records above.
  **Cite `not_ratGerm_log_comp_of_pole`, not `not_ratGerm_log_of_pole`**: the route carries an
  abstract `S` agreeing with `P/Q` on a ray, not a literal pair of polynomials, and the pole version
  concludes about `log (pev P x / pev Q x)` verbatim. `ratGerm_congr` is the transfer — `RatGerm`
  only sees the germ — and it was being done INLINE in `EMLLogNotRational` until this was the
  second copy. Say "every named step is proved", never "route A is closed". `(fm)`'s own warning is the right one to carry: *two green legs do
  not imply a third*, and it applies to the third as well.
  Also worth knowing before reading around here: **`GermDerivFbasis`'s docstring says the route needs
  "`exp ∘ S` transcendental over the rational functions". That is not the current frontier** — the
  step actually ABSENT is `not RatGerm (log ∘ S)`, a weaker and different statement, and the
  commit-letter for `b8ebfad2` states the four-line route status that supersedes the docstring.

- **READ THE MODULE NAMED AFTER THE ROUTE BEFORE ADDING TO IT.** `LogRatDeriv` already carried
  `logRat_deriv_eq` (leg 1 fully composed), `cross_of_div_eq_div` and `logRat_cross_identity` (the
  derivative identity cleared in one step). A first pass at `LogDerivCleared`/`LogGermAssembly`
  re-proved the last two and re-derived the first inline — and `LogRatDeriv`'s own header warns
  about exactly that failure, quoting `(fk)`: *"bricks re-deriving generic machinery because the
  summit was never checked"*. Deduplicated 2026-09-09; the theorem count went **down** (7 681 →
  7 679), which is the signature to expect.
  The search that would have caught it took one command — `grep -rn "RatGerm (log" MachLib/` — and
  I ran it only after building. **Grep the route's own name, not just the lemma you want.**
  Note also that `LogRatDeriv`'s header lists more as remaining than actually did: it names the
  cross-multiplication as open while `logRat_cross_identity`, in that same file, performs it. What
  genuinely remained of leg 2 was the `peq_of_ev_eq` promotion.

- **A CORRECT THEOREM YOU CANNOT REACH BECAUSE THE TERM DOES NOT MATCH — one failure mode, four
  costumes, and it cost this corpus four separate wrong diagnoses on 2026-09-08/09.**

  | mismatch | what it cost |
  |---|---|
  | `3.0` vs `1+1+1` | `smoothstep_le_one` existed and was written up as needing new mathematics |
  | `OfNat` vs `OfScientific` | `mach_decimal` stalls one rewrite short of `= 1` |
  | `0 - _` vs `-(_)` | `neg_div` silently does not fire; a backward `rw` against `= 0` finds the zero INSIDE `0 - _` — one instance was a 200 000-heartbeat timeout |
  | a literal quotient vs an abstract germ | `not_ratGerm_log_of_pole` was not citable by the route that needed it |

  Different mechanisms, one shape: the VALUES are equal and the TERMS are not, `rw` and `apply`
  match syntactically, and nothing reports it — a lemma that stops applying looks exactly like a
  lemma that was never strong enough.
  **The check: when a lemma "should" apply and does not, compare the TERMS before concluding
  anything about the mathematics.** Bridges that exist: `mach_ofnat_numerals` (numerals),
  `realOfScientific_*_dot_zero` (decimal↦`OfNat`), `ratGerm_congr` (germ equality on a ray).
  Two of the four are now compile PROBES in `tools/absence_claims.json`
  (`machdecimal-ofnat-boundary`, `negdiv-vs-zero-sub`) rather than prose, so they fire if the
  mismatch is ever closed — notes decay, instruments do not, and this file has three stale route
  headers from 2026-09 to prove it.

## Counts: the gate is the source, prose is a copy

**No count in prose — a claim total, an axiom total, an open-obligation total, a job count — may be
written from memory or arithmetic-in-the-head. Run the gate, read its number, paste it.** Prose is a
copy of gate output and never authoritative.

This is policy, not advice, and it is empirical: in the 2026-08 arc three separate remembered counts
went into a changelog wrong (`claims 429` for 431, `claims 439` for 438, and an earlier `5 851
theorems` by an unrecorded method that nobody can reproduce). The gates were right every time and
cost about a second each. A wrong count is worse than a missing one, because it reads as measured.

Corollary for the gates themselves: **a check that is silent on success is indistinguishable from a
check that did not run.** Print the figure even when nothing is wrong — `check_obligations.sh` prints
its footprint tally for exactly this reason.

**Since 2026-09-05 this policy is enforced, not just stated.** `tools/prose_counts_check.py` reads
`tools/prose_counts.json`, a registry of every tracked figure in `README.md`, this file and
`what_is_proven.md` — each a regex over the prose plus the command or artifact that measures it —
and fails the run on drift (`DRIFT`, exit 1) or on a source it cannot evaluate (`UNAVAILABLE`, exit
2, never a pass). It is wired into `check_all.sh` with a three-canary selftest. **The discipline it
imposes: when you put a number in one of those documents, register it in the same change**, or it
is exactly as unchecked as before. The trigger was this very section: the file that carried the
policy had sixteen files and eighty theorems of drift in its own architecture paragraph, and
`what_is_proven.md` said "260 axioms" for ten weeks after the ledger said 243.

## Status

Lean `v4.32.2`, branch `poly-euclid-spine` (`master` is fast-forwarded to it on push since
2026-09-05; the CI workflows and the site's links read `master`). Run everything with
**`foundations/tools/check_all.sh`** (every gate and harness, `rc = 0` iff all green; `--selftest`
proves it conducts a failure to its own exit code; the run prints its own gate count). Do **not** assemble a `{ gate1; gate2; … }` block by hand — such a block exits with its
*last* command's status, which reported `exit 0` over a failing claim audit on 2026-08-30. Same
disease as `gate | tail` reading `tail`'s status, one level up. The aggregator prints its own coverage on every
run (**800 of 1 104 modules reachable, 12 documented unreachable** as of 2026-09-07); quote it from
the run, not from here. `sorryAx`: 1, allowlisted.
**243 axioms pinned — unchanged across the whole 2026-08 EML arc**, including the `S > 0` repair and
the entire depth/decay programme below. Obligations ledger: **23 rows, 7 open rows, 4 distinct open
obligations** (a reduction cycle and a proved equivalence each carry several rows for one debt).

**The depth-4 rung's `const_left` cell is proved from it** (`depth_four_decay_const_left_tower3`,
`MachLib/EMLDepth4ConstLeft.lean`, 2026-09-05): one of the four cells of `NodeDecayBound 3 3`, at
depth-3 children and tower height 3. The other three cells are not, and `EMLDecayLadderStep`'s
route map prices them at ~2 400 lines; `EmlGermApproachResearch.md` says the next move on the
ladder is the falsification search, not another cell. The ledger did not move — a cell is not a
rung.

**The `fxpid` join was SIZED on 2026-09-05 and BUILT on 2026-09-05/07** — four obstacles,
four modules, all reachable and `sorryAx`-free. Read `what_is_proven.md` §2 before touching any of
it, and do **not** re-derive these: `SignedFixedPoint` (signed Q16.16 as a pair-of-unsigned
difference, so negation is a swap and subtraction is exact), `TwoStateTracking` (the contracting
measure — a maximum of *linear functionals*), `SignedPILoop` (`spiloop_tracks_exact`, the join with
an integrator), `QuadTracking` + `spiloop_tracks_exact_complex` (the under-damped case in a squared
measure), `ThreeStateTracking` (the derivative term).

Four findings from that arc that will save a session:

* **`iterate_affine_bound` was ALWAYS generic** over any `s(k+1) ≤ L·s k + ε`. The thing recorded as
  a "missing non-scalar trajectory lemma" was a missing *measure*, not a missing lemma. Check
  whether the general form already exists before pricing a generalisation.
* **A componentwise measure cannot work, and this is proved, not observed** —
  `weighted_max_cannot_contract_integrator`. A weighted maximum of components never contracts a
  loop containing an integrator, for *any* gains, because moduli discard the sign that makes the
  feedback negative. `ρ(M) < 1` while `ρ(|M|) ≈ 1.03–1.14`. Do not try it again.
* **The eigenstructure is FORCED by the structural rows, so the contraction hypotheses are ring
  identities** — for the 2×2 real case, the 2×2 complex case *and* the 3×3. The caller supplies only
  the eigenvalues of its own quantised gains and a bound on their moduli; there is no side
  condition and no decimal arithmetic anywhere in these files.
* **`sfxmul` IS NOT THE MULTIPLY FORGE EMITS, and the gap is 1 ulp.** Forge's Verilog does
  `(A*x) >>> FRAC`; an arithmetic shift is FLOOR, toward `−∞`. `sfxmul` is a difference of
  truncated unsigned products, so it truncates toward ZERO. They agree on non-negative products
  and differ by one `ulp` otherwise — found by simulating the emitted RTL under Verilator for 40
  steps (floor matched every step, `sfxmul` diverged at step 3). Forge's own certifier uses floor.
  Both are inside the `2·ulp` envelope the proof consumes, so use `spidloopOf_tracks_exact`
  (`SignedLoopEnvelope`), which takes the envelope as a hypothesis, rather than assuming the model
  is the hardware. For the shift specifically use `spidloopOf_tracks_exact_floor`: its hypothesis
  is just "each product is `≤ 1 ulp` BELOW exact, never above", which is what `>>>` does, and it
  gives `K·3·ulp` per step — HALF what `sfxmul` gives, since one-sided-at-one beats
  two-sided-at-two.
* **A deadbeat specimen is VACUOUS for the PID measure.** `m3` is a norm only when the
  eigenvalues are distinct and none is `0` or `1`; at `λ = 0` every functional vanishes and the
  bound reads `0 ≤ 0`. `SignedPILoop` uses a deadbeat specimen as its evidence and that is correct
  *there*. Reusing the instinct one dimension up produces a bound that cannot fail, with every gate
  green. `SignedPIDLoop` ships its specimen at `λ = 1/2, −1/2, 1/4` for exactly this reason.
* **I predicted the 3×3 would NOT come free and was wrong.** A PID loop has *two* structural rows
  (integrator and delay `xₚ' = x`), not one. `ThreeStateTracking`'s header records the correction.
  The check was one sympy command; the estimate was made from the shape of the problem rather than
  from the algebra. When the next such estimate appears, run the command.

Do not write a positive-feedback "join" inside the unsigned model; it would be true and hollow.
And `pid_trajectory_from_bits` is **still** not the end-to-end result — it quantifies its per-step
error universally. The three-row `spidloop` datapath is **built** (`SignedPIDLoop`,
`spidloop_tracks_exact`, 2026-09-07): integrator exact, delay row a *wire*, all error in the state
row's three multiplies, scaled by the measure's leading coefficients. The complex-pair case is **also done**
(`ThreeStateQuadTracking`, 2026-09-07): the measure splits as `f² + (g₁² + g₂²)`, a step multiplies
the parts by exactly `r²` and `σ²+ω²`, and all nine relations are ring identities in `r, σ, ω`. So
every PID design is covered whatever its damping. It is joined to `spidloop` as well
(`spidloop_tracks_exact_complex`), so **both** PID theorems are joins about the same loop and the
whole PI/PID arc is closed: real and complex, 2x2 and 3x3, measure and datapath.

**`Depth3ApproachBelow` is DISCHARGED** (`depth3ApproachBelow_holds`, `MachLib/EMLDepth2Form.lean`,
2026-09-05) — the decaying-floor replacement for the refuted `depth_le_three_gap_below`: a depth-≤3
tree that dips below `k` on a ray does so by at least `exp (−C − exp (exp x))`. Footprint is the
plain algebra/`exp` spine (`one_add_le_exp`, `exp_gt_one_plus_self`, `mul_pos`, …), no analytic
axiom, `sorryAx` 0. The last branch — `A = eml a₁ a₂` bounded — was sized as needing a
rate-separation lemma the corpus lacked; it does (`d3b_sep`), and it is one lemma: both excesses
are `Θ(1/x)`, and a first-order tie is decided *against* the hypothesis by `log (1 + y) ≤ y` versus
`exp v − 1 ≥ v`. Ledger row added (`Depth3ApproachBelow`, discharged); `Depth3ApproachBelowEml`
removed from `tools/hypothesis_baseline.json` because it now has a producer. Read the module's
route-map section before extending the depth ladder: it records what the estimate got right and
wrong.

**The `S > 0` branch was VACUOUS and is now repaired** (`a10b3b5b`, 2026-08-24). Two pole hypotheses
were unsatisfiable for every `q`: `∀ r, DerivCoprime q r` (false at `r = 0`) and
`∀ r, PNormal (pnsum r (pderiv q))` (false at every `r ≥ 1`). The first was weakened to `r + 1`
(proof-neutral); the second was **deleted** — it fed one `euclid_lemma` call and was not merely
unsatisfiable but decorative. `GermClearedSpecimen` now discharges every hypothesis at `q = x`,
`P = 1`, `Q = x`, giving

```
no_proper_cleared_relation_inv_x : ClearsToExp (1/x) fs → GProperRel (log(1/x)) fs → False
```

with **no pole hypotheses assumed**. `pIrred_X` is the corpus's first `PIrred` construction. Read the
changelog's `(ci)` VOID before citing anything about this branch.

**Degree-`d` is closed.** `ClearsToExp` (a class whose members clear, over one common
eventually-non-vanishing denominator, to `expCoeffs` images) discharges all three obligations of
`minimal_expRel_identity_in`; `no_proper_cleared_relation` takes no `hmin`, no `Cs`, no split and no
degree bound. Two findings worth carrying: `gscaleSub` denominators do **not** multiply (the step is
asymmetric — only one factor per product is ever dirty), so no denominator *bound* is needed; and
`EvNonvanish` (non-zero on a tail) is required over "not eventually zero", because germs have zero
divisors and the weak form silently breaks properness.

**Still open.** Read the ledger, not this paragraph — a gate checks the ledger and nothing checks
prose, so if they disagree the ledger is right. Three obligations closed in the 2026-08 arc, taking
the count six → four: `SignHardCase` (`signHardCase_holds`, `d7b8d28c`),
`NegativeTranslationGrowingLeft` (`negativeTranslationGrowingLeft_holds`, 2026-08-28,
`EMLNegTranslation`), and `OneQueryDichotomy` (`oneQueryDichotomy_holds`, 2026-08-29,
`EMLCtxDivClamp` — via `divClamp`, supplying the two `div` side conditions the obligation omits).
The **four** distinct open obligations are: the `DecayFloor` ⇄ `EmlGermApproach` ⇄ `GrowthEnvelope`
cycle (**one** obligation, three rows), `TowerLowerBound` ⇄ `TowerReducesToSign` (one obligation, two
rows, equivalent since `SignHardCase` fell), `BoundedGermTranscendence`, and `OneQueryLevelSet` —
which does **not** follow from `OneQueryDichotomy`; it reduces to `q_F(sign) ≥ 2`, and
`EMLOneQueryGlobal` exists to keep the two apart.

Recent arc: **EML characterised** as exactly the `exp`/`log` closure of `ℝ`; then
`s(1/x) ∈ {7,9,11}` proved, `d(1/x)` frozen at `{3,4}`, and a depth- and size-indexed **growth
envelope** built. Start here:
`monogate-research/exploration/inv_x_termination_route_2026_08_06/EML_STATUS.md`, and
`FRONTIER_BRIEF_3.md` for the open questions.

**2026-08-26/27 — the decay programme, `(dk)`–`(dy)`.** Four things a new session should know before
touching it, because each was learned the expensive way:

1. **The induction search is closed, on both sides.** `EMLLadderMeasure`: no `Nat`-valued measure on
   trees that descends to both children can carry it — syntactic (`recipTree` costs two steps while a
   step buys one) or germ-based (`EMLGermApproach` §4: growth does not descend to the *right* child,
   unboundedly). Stated at that width and no wider: lexicographic orders, ordinal ranks and
   non-structural arguments are untouched.
2. **The missing input is named and placed.** `EmlGermApproach` (`EMLGermApproach`) is the obligation
   at its narrowest, equivalent to `DecayFloor`. Its *per-pair* form is a corollary of Hardy (1912);
   **the entire open content is the position of one `∃ k`**. **No axiom has been spent on it,
   deliberately.** It is now a **separate research programme with its own file — read
   `EmlGermApproachResearch.md` before writing any Lean against it.** That file carries the exact
   conjecture, the adversarial families already built, the three failed descent mechanisms, the
   surgical question for a specialist, and **exit criteria for PROVED / REFUTED / ASSUMED decided in
   advance.** Engineering effort on the other five open obligations should not wait on it.
3. **The ladder reaches the obligation.** `decayFloor_of_ladderInputs` (`EMLValueGap`): `DecayFloor`
   follows from per-depth `NodeDecayBound` + `LowerEnvBound`, footprint-clean. `decayFloorUpTo_three`
   is proved (the top was depth 2 for the whole arc); depth 4 needs `NodeDecayBound 3`, whose only
   known route is the depth-≤2 cell enumeration that `FRONTIER_BRIEF_3` §4 Q2 measured and
   **rejected**. Do not start it without deciding that a bounded rung is worth it — bounded rungs do
   not move the ledger.
4. **Depth was never the parameter — height is, and `EMLHeightVsDepth` proves the gap.** Syntactic
   exponential height `ehTree (eml A B) = Nat.max (ehTree A + 1) (ehTree B)` bounds every
   `HeightModel` (`eh_le_ehTree`), so the existing `eh_le_depth` **factors through it**, and the
   factorisation is strict: a right spine of depth 3 has height 1. The payoff is not cosmetic —
   `decayFloorByHeight_of_heightModel` gets a **strictly larger** conclusion from the *same*
   `LeadingMonomialFloor` input, covering right spines of any length at level 1 where the
   depth-indexed form needs level 3. The old reduction was lossy and nobody had noticed.
   Two further facts, both machine-checked: height satisfies `left_le` and **fails `right_le` with a
   gap of exactly zero** (`no_ladderMeasure_with_ehTree`) — the *same side* the germ route fails on,
   by a completely different argument; and `ehTree` itself **overcounts**
   (`ehTree_overcounts_witness`: `eml (eml (const 0) var) var` has height 2 but evaluates to
   `e/x - log x`), so the chain `eh ≤ ehTree ≤ depth` has slack at both steps. **None of it moves the
   ledger** — still 6 distinct open obligations — and none of it touches `LeadingMonomialFloor`,
   which is where `decayFloor_of_heightModel` is actually stuck. The prompt to look here came from a
   complex-analytic measurement that does *not* transport; see the module docstring.

5. **Everything above is pointwise on purpose.** The hypotheses of `NodeDecayBound` and
   `ValueGapBound` are guarded *inside* the `∀ x`. An eventual reading would need `evSign_all` and
   with it the analytic block, across the entire ladder. It also blocks two converses — see `(dx)`,
   `(dy)` — and that is the accepted price.
