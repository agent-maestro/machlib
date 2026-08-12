# Changelog

All notable changes to MachLib are recorded here. Format roughly follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Versions are
release-snapshot identifiers; see the release manifests for the authoritative
per-release status.

## [Unreleased] — 2026-08-12

### A bounded log names the shape — the dichotomy made composable

`depth_le_one_log_bounded_or_unbounded` answers *whether* the log is bounded. The open cells need to
know *which tree that leaves*, and a disjunction over "∃ a bound" does not say. So:

**`depth_le_one_log_bounded_forms`** — if `log (B x) ≤ Λ` on `[1,∞)` then `B` is `const β` or
`c′ − log x`. Exactly two of the five forms, named.

**Refactor rather than a second copy.** The three unbounded forms each need a point past a
prescribed `Λ`, and both theorems need the same three. They are now private lemmas —
`log_var_unbounded`, `log_exp_sub_const_unbounded`, `log_exp_sub_log_unbounded`, plus the shared
`big_point` and the `c′ − log x` cap `log_c_sub_log_cap` — and the dichotomy is five short lines
over them instead of ~90 inline. Net **+28 lines** for a theorem that would have cost ~120 duplicated.

*A statement that answers "is it bounded?" and a statement that answers "then what is it?" are
different theorems, and the second is the one that composes.* Worth noticing one increment after
building only the first.

**Everything the open cells need now exists:** exp gap, log dichotomy, log-bounded-forms, the three
∞ bounds, and the five-form classification. Split-A `q > 1` is case analysis and two-point
evaluation over them. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### The log-side dichotomy — and it is *not* the mirror of the exp gap

**`depth_le_one_log_bounded_or_unbounded`** — for a depth-≤1 `B`, `log (B x)` is either bounded above
on `[1,∞)` or unbounded above.

**Deliberately weaker than the exp gap, because the log side has three growth classes, not two:**
bounded (`const β`, `c′ − log x`), **logarithmic** (`var`), and **linear** (`exp x − d`,
`exp x − log x`). So there is no "bounded or dominates" statement to make — `var` is unbounded yet
dominates nothing. Writing the mirror would have been false, and the shape of the theorem is the
finding as much as its content.

Both unbounded branches share one step, **`exp_sub_pred_ge`**: `exp (x−1) ≤ exp x − exp (x−1)`,
because `exp 1 ≥ 2`. That gives `exp (x−1) ≤ B x` once the subtracted term is under `exp (x−1)` —
which holds for `d` past a threshold and for `log x` always, since `log x ≤ x − 1 < exp (x−1)`. Then
`log_le_log` delivers `x − 1 ≤ log (B x)`.

The `c′ − log x` bound needed care in the small-`c′` regime: `log c′ ≤ c′ + 1` holds for every
`c′ > 0` but by two different arguments either side of `1`, and the totalised branch contributes `0`,
so the cap must be non-negative as well as above `log c′`.

**The kit for the remaining cells is now complete.** Split-A left-branching `q > 1` reduces to `R₂`
bounded and strictly increasing; the exp gap forces `A` bounded, this forces
`B ∈ {const β, c′ − log x}`, and the four surviving combinations are eventually constant or
decreasing. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### A gap theorem: depth-1 exponentials are bounded, or they dominate `exp x`

**`depth_le_one_exp_bounded_or_grows`** — for a depth-≤1 `A`, either `exp (A x)` is bounded on
`[1,∞)`, or it eventually dominates `exp x`. **Nothing sits in between.**

This is the structural fact behind every `M·x` case: the split into `mx_A_bounded_absurd` and
`mx_A_grows_absurd` *was* this dichotomy, discovered case by case and never stated. The two bounded
forms are `const α` and `c − log x`; the three growing ones are `x`, `exp x − d`, `exp x − log x`.
There is no depth-1 tree whose exponential grows, say, **linearly** — which is precisely why `M·x` is
unreachable at depth 2, and the reason is now a theorem rather than five separate arguments.

It belongs to **T2** as much as to the 9-node map: "how does behaviour vary with depth" is exactly
this kind of statement, and a gap is a stronger answer than a bound.

**What it unlocks, and what is still missing.** The next open cell (split-A left-branching, `q > 1`)
reduces to: `exp(R₂ x) = exp(K − 1/x) + λ` with `λ > 0`, so `R₂` is **bounded and strictly
increasing**. The gap theorem forces `A` into the bounded class; finishing needs the **log-side**
companion — *for depth-≤1 `B`, `log (B x)` is either bounded above on `[1,∞)` or unbounded above* —
which then forces `B` into `{const β, c′ − log x}`, and in all four surviving combinations `R₂` is
eventually constant or decreasing, contradicting strict increase. That companion is not built yet.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The `−log x` cell CLOSES — split B's `κ = 0` is dead

The last surviving case was right-branching with `ℓ = var`, where `log(L₂ x) = exp x + log x` forces
**`L₂ x = x·exp(exp x)`** — a double exponential *multiplied by `x`*, and that extra factor is the
whole obstruction.

- **`depth_le_one_le_exp_shift`** — a depth-≤1 tree is under `exp x + D` on `[1,∞)`. The
  value-level companion to `depth_le_one_log_le_linear`, which bounds its *logarithm*.
- **`x_mul_exp_exp_not_in_eml_depth_le_2`** — hence `exp(A x) ≤ exp D · exp(exp x)`: a **constant**
  multiple of `exp(exp x)`. The target needs an `x`-growing multiple, and `x` outruns any constant.

So **every branch of split B's `κ = 0` cell is now dead**, and with it the question *can a depth-3
tree compute `−log x`?* — **no**. That was the sharpest open cell in the 9-node map.

The three ∞-side lemmas turn out to be a complete kit for this family: `log(B x) ≤ x + C` caps a
logarithm from above, `Cl ≤ log(B x)` caps it from below, and `A x ≤ exp x + D` caps the value. Every
kill in the last two sessions used exactly one or two of them.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The κ-trichotomy is a comparison with Ω — and the locus taxonomy closes

`κ = 0` **is** the Ω point. `EMLDepth2InvX` splits the depth-2 cancellation analysis three ways on
`κ := G − exp(−G)` — `kappa_pos_floor`, `kappa_zero_floor`, `kappa_neg_absurd` — and as written that
is a case split on an **opaque inequality between transcendentals**, with nothing saying which branch
fires when.

- **`kappa_strict_mono`** — `κ` is strictly increasing in `G`: `G` rises while `exp(−G)` falls.
- **`kappa_sign_by_omega`** — so the trichotomy is a comparison with a **single explicit constant**:
  below Ω the negative branch, at Ω the degenerate one, above Ω the linear floor.

Since Ω is caged in `(e⁻¹, 1)`, every `G ≥ 1` sits in the `κ > 0` branch — which is exactly why
`A = var` (where `G = 1`) never reaches the hard cases. That was previously a remark in a docstring;
it is now a consequence.

**The taxonomy closes, and the answer is not always a curve:**

| locus | shape | solved by |
|---|---|---|
| `exp(exp c₀) − exp(exp c₁) = 1` | **transcendental graph** over one parameter | `invX4gen_locus_is_a_graph` |
| `exp(−G) = G` (κ = 0) | **single transcendental constant** | `omega_point_is_a_single_caged_value` |
| `exp c = log β` (γ = 0) | **elementary graph**, `β = exp(exp c)` | `gamma_zero_locus` |

All three accidental loci in the arm are now solved. `sorryAx` 0; ledger 242 unchanged.

## [Unreleased] — 2026-08-11

### The Ω point solved completely — the degeneracy is real and isolated

Second T3 locus. `depth_le_one_trichotomy`'s third branch carries a clause conditional on
`exp (−G) = G` — the **Ω point**, `G·exp G = 1` — and it is where the linear floor degenerates and
the quadratic one is needed. It had only ever appeared as a hypothesis nobody had solved: it was not
known whether the degenerate case **occurs**, nor whether it could occur more than once.

- **`omega_point_bracket`** — every positive solution lies strictly inside `(e⁻¹, 1)`.
- **`omega_point_unique`** — at most one, because `exp(−G)` decreases while `G` increases.
- **`omega_point_exists`** — at least one, by IVT on `G ↦ G − exp(−G)`, negative at `e⁻¹` and
  positive at `1`. Uses `intermediate_value_of_hasDerivAt`, which needs only *some* derivative to
  exist — so the derivative never has to be computed.

**So the degeneracy is real and isolated: exactly one parameter value in the whole positive line.**
That is why the quadratic floor could not be avoided — it is not defending against an empty case —
and why no perturbation argument reaches it.

`omega_point_is_a_single_caged_value` packages all three. `sorryAx` 0; ledger 242 unchanged.

### T3, first artifact: an exceptional locus solved for exactly

`MachLib.EMLExceptionalLocus`. The arm keeps producing exceptional sets **by accident**, and it has
cost something — a 12,208-sample grid reported non-existence and missed a witness living on one. The
repair is to solve for them deliberately, and the template is: **prove the behaviour is equivalent to
an equation, then solve the equation.**

`EMLDepth2InvX` already had the *sufficient* direction (`invX4gen_eval`) and *existence*
(`invX4gen_witness_for_any_c1`). Neither makes a locus — only a supply of witnesses. What was missing
is **necessity**:

- **`invX4gen_iff`** — the depth-4 family computes `1/x` **iff** `exp(exp c₀) − exp(exp c₁) = 1`.
  The forward direction needs a **single point**, `x = 1`, where `log 1 = 0` collapses every branch.
- **`invX4gen_locus_unique`** — at most one `c₀` per `c₁`: the locus is a **graph**, not a region.
- **`invX4gen_locus_solved`** — and exactly one, `c₀ = log (log (1 + exp (exp c₁)))`. The locus is
  that explicit transcendental curve, nothing more and nothing less.
- **`invX4gen_off_locus`** — every other pair fails. This is what makes the grid failure
  **inevitable rather than unlucky**: the good set is a graph over one parameter, so sweeping `c₀`
  independently misses it unless a sample lands on the curve exactly.

`invX4gen_locus_is_a_graph` packages existence + uniqueness + the explicit formula.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Constant generation is vacuous in EML — proved, not argued

A research direction was proposed twice on the grammar `S → 1 | eml(S,S)`: *which irrational
constants are EML-representable, and how compactly?* MachLib's grammar has
`const : Real → EMLTree`, so `π` is `EMLTree.const π` — **depth 0, size 1**.

**`const_generation_is_vacuous`** states it as a theorem rather than a remark, because the refutation
is one line of the definition and should be checkable rather than debated. Every real is
representable, all at the same minimal cost, so the question orders nothing. `i` is out of scope
entirely: `eval` is `Real`-valued.

**Where the question does have content:** `EMLTree.unitOnly` restricts constants to `0` and `1`.
Then `e` is depth 1 / size 3 (`e_mem_unitOnly`) and `e − 1` is depth 2 / size 5
(`e_sub_one_mem_unitOnly`) — both leaning on the **totalised** `log`, which is what makes the depth-1
leaves usable rather than undefined. A different language from the one the rest of the corpus
studies; a side laboratory, not the main programme.

Research slate reorganised and written up:
`monogate-research/exploration/inv_x_termination_route_2026_08_06/RESEARCH_SLATE_T1_T4.md` — T1
compilation invariants (producing), T2 quantitative tameness by depth, T3 exceptional-locus geometry,
T4 certified synthesis with an untrusted searcher. Every claim in it names a theorem or is marked
open. `sorryAx` 0; ledger 242 unchanged.

### `M·x ∉ EML₂` — the gap question closes, and with it a 9-node branch

**`mx_not_in_eml_depth_le_2`**: for every `M > 1`, no depth-≤2 tree computes `M·x`. All five
`A`-forms fall — `var` and the two fast forms (`exp x − d`, `exp x − log x`) to
`mx_A_grows_absurd`, `const` and `c − log x` to `mx_A_bounded_absurd`. **`M = 1` is genuinely
excluded**: `var` computes `1·x` at depth 0, so the strict inequality is not slack.

The two fast forms needed one growth fact, `two_mul_le_exp` (`x + x ≤ exp x` on `[0,∞)`, from
`exp x = exp 1 · exp(x−1) ≥ exp 1 · x ≥ 2x`) — no calculus, and it gives both `exp x − d ≥ x` past
`1 + exp d` and `exp x − log x ≥ x + 1` past `1`.

**Stated on `[1,∞)`, not `(0,∞)`** — a strictly stronger theorem, and the reason is not cosmetic: it
dodges the wrinkle the totalised `log` creates downstream, where `log(L₂ x) = exp p + log x` only
forces `L₂ x > 0` away from `x = exp(−exp p)`, which is `< 1`.

**`neg_log_right_const_absurd`** then kills the branch that motivated all of it: the `−log x` cell's
right-branching `ℓ = const p` case needs `L₂ x = M·x` with `M = exp(exp p) > 1`, which is now
impossible. `mx_mem_EML` builds `M·x` at depth 4 and this shows depth 2 does not suffice.

**What survives of the `−log x` cell is one case**: right-branching with `ℓ = var`, where
`log(L₂ x) = exp x + log x` forces `L₂ x = x·exp(exp x)` — not a linear function, so none of this
transfers to it.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The mirror at `∞`, and the bounded-`A` half of `M·x`

**`depth_le_one_log_lower_at_infinity`** — a depth-≤1 tree's logarithm is bounded **below**
eventually. Each form carries its own threshold (`c − log x` only crosses into the totalised branch
past `exp c`; `exp x − d` only clears `1` past `exp d`), but past it the bound is uniform, and in
four of the five forms it is simply `0`.

**`mx_A_bounded_absurd`** covers both bounded `A`-forms in **one** statement — `const α` with
`K = exp α`, `c − log x` with `K = exp c` — because the only thing the argument uses is the bound:
`M·x` is unbounded and `K − Cl` is not. The witness point is `X₀ + (1 + exp(K−Cl))·(1/M)`, chosen so
that `M·x = M·X₀ + (1 + exp(K−Cl))` lands above `K − Cl` by `lt_one_add_exp`.

**`M·x ∈ EML₂?` now has three of five `A`-forms closed** — `var` (via the `∞` upper bound),
`const`, and `c − log x` (both via this) — plus the `B = exp x` shape. Remaining: the two
fast-growing forms `exp x − d` and `exp x − log x`, where `exp(A x)` must be bounded *below* by
`exp x` past a threshold and then run against the same linear cap.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Growth at `∞`: a shallow `log` cannot beat linear

Every bound in `EMLSizeNineShape` lived on `(0,1]`; the remaining `M·x` shapes need the other end.

**`depth_le_one_log_le_linear`** — for a depth-≤1 `B`, `log(B x) ≤ x + C` on `[1,∞)`. All five closed
forms, including the totalised branches where `B x ≤ 0` and the log is `0`. The `exp x − d` case
avoids needing `log_mul` via `exp_sub_le_exp_shift`: `exp x − d ≤ exp(x + exp(−d))` for `x ≥ 0`,
because `exp(e) ≥ 1 + e` and `exp x ≥ 1`.

That is what converts `exp(A x) − log(B x) = M·x` into `exp(A x) ≤ (M+1)·x + C`, where
`exp_beats_linear_past` finishes any `A` that grows. First application:
**`mx_A_is_var_absurd`** — `M·x` is out of reach when the left child is `var`, for **any** depth-≤1
`B` with no case analysis on `B` at all. That the `B` side needs no cases is the point of having the
`∞` bound rather than arguing shape by shape.

The `M·x` cell now has its `A = var` and `B = exp x` shapes closed. What remains there are the
`A`-forms that grow faster (`exp x − d`, `exp x − log x`) and the two that stay bounded
(`const`, `c − log x`) — the latter needing a *lower* bound on `log(B x)` at `∞`, which is the
mirror of what landed here and is not yet built.

`sorryAx` 0; ledger 242 unchanged.

### The splitter census: stop waiting for the next shape to bite

Two statement shapes broke the claim auditor's arrow-splitter today, and the second landed *after*
the "cover input shapes, not claim count" lesson was written down — because the first fix was patched
per-connective instead of generalised. Rather than add a third canary and wait, the shape question is
now **audited over the corpus on every run**.

**`hypothesis_scope_violations`** — an extracted hypothesis containing a **depth-0 binder** is always
a splitter bug and never a real hypothesis: the pretty-printer parenthesises higher-order
hypotheses, and telescope binders are stripped before hypotheses are collected. So a `∀`/`∃` still at
depth 0 inside a hypothesis means the antecedent chain was cut *inside* a binder body. Decidable from
the printed form.

It runs for **every registered claim**, not only those declaring `hypotheses_count` — `statement_of`
is now memoised, so the census is free. **0 violations across all 75 claims.**

**`canary 12`** proves the census would have caught both historic bugs rather than merely agreeing
with today's code: it restores each prior behaviour in turn — no guard at all, then the `∃`-only
patch that fixed the first bug and left the second — and requires violations to appear in each.
Specimens drawn from **historical faults, not invented ones**.

`sorryAx` 0; ledger 242 unchanged; seven gates green; 12 canaries; 75 claims.

### Depth-≤1 has exactly five closed forms — and `+log x` is not one of them

`depth_le_one_classification`: a depth-≤1 tree is **constant**, `x`, `c − log x` (`c > 0`),
`exp x − d`, or `exp x − log x`. Nothing else. The existing `depth_le_one_trichotomy` and
`depth_le_one_right_tetrachotomy` give *inequalities*; the remaining 9-node cells need to know what a
subtree **is**, not what it is bounded by.

**What the list does not contain is the useful part: `+log x`.** Only `c − log x` appears. Hence
`log_plus_const_not_depth_le_1` — **`k + log x` is unreachable at depth ≤ 1, for every `k`** — which
follows uniformly from `depth_le_one_lower_bound`: all five forms stay above a constant near `0⁺`,
and `k + log x` does not.

`mx_B_is_exp_absurd` applies it to the `M·x ∈ EML₂?` cell. When the right child is `exp x`,
`log(exp x) = x` **exactly**, so the equation forces `exp(A x) = (M+1)·x` — and `exp(A x) ≥ exp F` on
`(0,1]` while `(M+1)·x` can be driven below `exp F` (at `x = 1/(1 + (M+1)·exp(−F))`, where the
inequality reduces to `0 < exp F`).

**A duplicate caught and removed.** I rebuilt `depth_le_one_lower_bound` from scratch before
discovering it already exists in `EMLDepth2InvX`, with the same insight in its docstring. Reused
rather than kept. I had grepped before starting the `M·x` cell — for *results about linear
functions*, which is what I expected to need — and not for the lemma the proof actually turned out
to want. **Grep for the tool at the point you reach for it, not only when planning.**

**And the claim auditor's arrow-splitter broke again, on a new shape.** A five-way classification
ends in an unparenthesised `∀` disjunct; the splitter walked into it and reported 2 hypotheses
instead of 1. Same defect class as the existential-conclusion bug fixed earlier today, so the guard
is now general: **while scanning for a top-level `→`, abort on any depth-0 binder seen first** — the
leading telescope has already been stripped, so a binder still reachable at depth 0 is nested.
`canary 11` added.

Two shapes have now bitten in one day — existential conclusion, disjunctive conclusion — and both
were one specimen away. That is the "cover input SHAPES, not claim count" lesson arriving twice.

`sorryAx` 0; ledger 242 unchanged; seven gates green; 11 canaries; 75 claims.

### The `−log x` cell halves — and becomes a gap question about `M·x`

The sharpest open cell (split B, `κ = 0`) asks whether a depth-3 path computes `−log x`. Its
**left-branching half is free**, and one case is a one-liner. Writing `L = eml L₂ (leaf)`:

- `leaf = var` → `exp(L₂ x) − log x = −log x`, i.e. **`exp(L₂ x) = 0`**. Immediate
  (`neg_log_left_leaf_var_absurd`).
- `leaf = const q` → `exp(L₂ x) = λ − log x`, negative past `x = exp(λ+1)`
  (`neg_log_left_leaf_const_absurd`, every `λ`, so the totalised `log q = 0` case is included).

**`neg_log_path_is_right_branching`** assembles these: a depth-3 path computing `−log x` must carry
its *leaf on the left*. So the cell reduces to `log(L₂ x) = exp(ℓ x) + log x`, and for
`ℓ = const p` that is exactly **`L₂ x = M·x` with `M = exp(exp p) > 1`**.

**`mx_mem_EML` already builds `M·x` at depth 4.** So this cell is now a *gap* question about a named
function with no free structure left: **`M·x ∈ EML₄` — is it in `EML₂`?** That is a sharper and more
answerable question than the one it came from, and it connects the 9-node problem to `witT`, which
the arm already understands.

**Worth flagging as a correction of my own expectation.** I had classified this cell as
sign-consistent and therefore expensive. Half of it was free, and I only found that by checking
rather than trusting the triage rule's verdict. The rule predicts *where machinery is needed*; it
does not license skipping the cheap check. `sorryAx` 0; ledger 242 unchanged.

### Split B opens, and the 9-node map is now complete

`split_b_leaf_const_neg_absurd` — in split B (`t = eml L (leaf)`) the equation is
`exp(L x) = 1/x + κ`, so **the pole sits under an `exp` rather than a `log` and none of the split-A
arguments transfer**. The triage rule still finds the free cell instantly: `exp` is positive and
`1/x + κ` is not, once `1/x` drops below `−κ`. Dead by sign, any depth.

Full map written up: `monogate-research/exploration/inv_x_termination_route_2026_08_06/RESULT_NINE_NODE_MAP.md`.
**5 cells closed.** Both left-branching split-A families 3-of-4; split B 1-of-4; the right-branching
depth-3 paths untouched (and sign-consistent, so they will cost machinery).

**The sharpest open cell is split B with `κ = 0`**, which asks exactly: *can a depth-3 tree compute
`−log x`?* That is a clean membership question about a named function rather than a family with free
parameters, which makes it the right one to hand to someone.

Also recorded there: `1/x + log x > 0` for all `x > 0` (minimum `1` at `x = 1`), so split B's
`leaf = var` cell has **no** sign kill available — worth knowing before someone spends an hour
looking for one. `sorryAx` 0; ledger 242 unchanged.

### The triage rule predicts a family it wasn't derived from — `ℓ = var` closes 3 of 4 too

Generalised the pole obstruction and swept the second family. **`no_pole_at_depth_le_2`**: no
depth-≤2 tree can be *capped* by `C − 1/x` near `0` — stated as an upper bound rather than an
equation, so it applies wherever a pole appears however it is dressed.
`shifted_inv_not_in_eml_depth_le_2` is now a three-line corollary.

Two reusable primitives separate the trivial contradiction from the per-branch work of exhibiting a
point: **`exp_sub_log_absurd`** and **`exp_add_absurd`**. Worth noting the second does **not** need
the `0 < μ` one expects — `exp > 0` alone does it. With those, each branch is a few lines.

**`ℓ = var`, left-branching, reproduces the table exactly:**

| `leaf₂` | `log(leaf₂)` | status |
|---|---|---|
| `var` | `log x` | **dead** — `var_family_leaf_var_absurd`, sign |
| `const q`, `0 < q < 1` | `< 0` | **dead** — `var_family_leaf_const_neg_absurd`, sign |
| `const q`, `q = 1` or `q ≤ 0` | `= 0` | **dead** — `var_family_leaf_const_zero_absurd`, pole bound |
| `const q`, `q > 1` | `> 0` | **open** |

**The triage rule predicted which cell would cost anything, in a family it was not derived from.**
That is the reason to trust it for the rest: *check the sign first; buy a growth argument only where
the signs agree.* Both left-branching families are now 3-of-4 closed, by the same three arguments in
the same three positions.

Still open: the `> 0` cell in both families, the right-branching depth-3 paths, and all of split B.
`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Two more 9-node branches, closed by sign alone — and why the third needed machinery

`split_a_leaf_var_absurd` and `split_a_leaf_const_neg_absurd`. **Neither takes a depth hypothesis**:
they hold for *any* subtree. With the earlier pole argument, the left-branching sub-family of split A
now stands at three of four cells dead:

| `leaf₂` | `log(leaf₂)` | status |
|---|---|---|
| `var` | `log x` | **dead** — sign, *any* depth |
| `const q`, `0 < q < 1` | `< 0` | **dead** — sign, *any* depth |
| `const q`, `q = 1` or `q ≤ 0` | `= 0` | **dead** — `shifted_inv_not_in_eml_depth_le_2`, needs depth 2 |
| `const q`, `q > 1` | `> 0` | **open** |

**The pattern is the finding.** Only one of the three needed machinery. The other two collapse
because their right-hand sides go negative near `0` while a left-hand `exp` cannot. The
`log(leaf₂) = 0` case is exactly the one whose right-hand side stays *positive* — no sign clash
exists, so the pole must be chased through the growth bound, which is why
`depth_le_two_log_decay_floor` had to be built at all. **A case needs machinery precisely when it is
sign-consistent**, and that is a usable triage rule for the remaining branches: check the sign first,
and only reach for a growth argument where the signs agree.

Still open: the `q > 1` cell, the right-branching depth-3 paths, `ℓ = var`, and all of split B —
where `exp(L x) = 1/x + κ` puts the pole inside an `exp` rather than a `log`, and none of these
arguments transfer. `sorryAx` 0; ledger 242 unchanged.

### `s(1/x) = 9?` becomes a finite question about PATHS — and one branch closes

`MachLib.EMLSizeNineShape`. The last open integer in the reciprocal arm is now known to be about the
*tree encoding* only, which makes it a clean self-contained problem. This makes "finite" concrete.

- **`minimal_size_isPath`** — a tree meeting `2·depth + 1 ≤ size` with equality is a **path**: every
  `eml` node has a leaf child. General, any depth.
- **`inv_x_size_nine_isPath`** — `d(1/x) = 4` forces `depth ≥ 4` and `9 = 2·4+1` forces `depth ≤ 4`,
  so **a 9-node solution is a depth-4 path**. `2⁴·2⁴·2 = 512` shapes with ≤ 5 real parameters.
- **`inv_x_size_nine_split`** — only two top-level splits survive: `(1,7)` and `(7,1)`. The
  intermediate `(3,5)` and `(5,3)` are impossible; neither child could reach depth 3.
- **`invX4_not_isPath`** — the known 11-node witness is *not* a path. It spends its extra 2 nodes
  branching, so the 9-node family is a genuinely different shape, not a tightening of the known one.

**A growth companion to rung 2, and the first branch closed:**

- **`depth_le_one_upper_log_bound`** — a depth-≤1 tree grows at most like `E − log x` on `(0,1]`.
  The *upper* companion to `depth_le_one_right_tetrachotomy`, which supplies lower bounds.
- **`depth_le_two_log_decay_floor`** — a depth-≤2 tree falls at most logarithmically at `0⁺`:
  `F + log x ≤ t.eval x`. **No positivity hypothesis** — `exp ≥ 0` caps the first term and the
  lemma above caps the second. Where `rung2_positive_floor` needs positivity and bounds by `C·x²`,
  this needs nothing and bounds the value itself.
- **`shifted_inv_not_in_eml_depth_le_2`** — **`K − 1/x` is out of reach at depth 2, for every `K`.**
  A pole cannot be manufactured two levels up, because `−1/x` falls faster than any logarithm.

That closes one named branch of split A: `t = eml (const c) (eml R₂ (leaf₂))` with `log(leaf₂) = 0`
requires `R₂ x = K − 1/x` at depth 2, which is now impossible.

**What is not closed, stated plainly:** every other branch — `log(leaf₂) ≠ 0`, `leaf₂ = var`, the
right-branching depth-3 paths, `ℓ = var`, and all of split B. The `leaf₂ = var` branch *looks* easy
(a sign clash near `0`), and looking easy is not a proof; it is not claimed. **No counting argument
can finish this**: 9 nodes genuinely permit depth 4, so every remaining refutation must be semantic.

`sorryAx` 0; ledger 242 unchanged.

### The second arrow: DAG → scheduled datapath. Depth survives, area dies.

`schedule_ge_wdepth` — for any schedule `s` in which an `eml` instruction's result is available no
earlier than `L` after both operands (`SchedValid`), **`L · depth ≤ s i`**. Hence
**`inv_x_schedule_ge_four_L`: no schedule computes `1/x` in fewer than `4·L`** — however many blocks
it allocates, *including one*. At the measured `L = 5` cycles that is **20 cycles**.

This is the arrow on which the measured **×4.00 area multiplier dies.** A time-multiplexed datapath
reuses one block across cycles (forge already does this — the shared-MAC matmul is ~4 DSPs constant
in size), so area becomes `O(1)` in depth while the latency floor is untouched. The forge report's
area row has been amended: ×4.00 is a property of the *unshared* lowering, not of the quantity.

**The invariant ledger, two arrows deep:**

| quantity | tree → DAG (sharing) | DAG → schedule (resource sharing) |
|---|---|---|
| **depth / latency** | preserved exactly (`netDepth_eq_depth`) | **floor survives** (`schedule_ge_wdepth`) |
| **size / area** | destroyed — exponential (`sqProg_size`) | destroyed — one block serves every node |
| critical path | preserved (per-stage) | preserved (per-stage) |

**Depth is the only quantity that survives both.** Twice today the *area* figure has been the
misleading one — first as the wrong instantiation of the weighted-cost socket, then as the ×4.00 a
scheduler erases. Area agrees with depth exactly when the lowering happens not to share, which is a
fact about the lowering.

`schedule_ge_wdepth` uses the weighted machinery directly (`wdepth 0 0 L`), so the socket earns its
keep rather than sitting unused. `sorryAx` 0; ledger 242 unchanged.

### The weighted socket has a trap, and measuring found it

`forge` now measures the block (`forge/reports/eml_block_cost_2026_08_11.md`, yosys 0.40 +
verilator 5.024, generic gate mapping, Taylor-scaffold kernels). One block at Q16.16: **37,853
cells, 90 logic levels, 5 cycles**, functionally verified before being costed. A 4-deep serial
chain: **area ×4.00, critical path ×1.00**.

That ×1.00 is the finding. `netWDepth_eq_wdepth` says any path-additive cost survives sharing for
arbitrary weights — true, and it invites plugging in any measured per-block number. Three natural
instantiations, **one correct**:

- `we` = **cycles per block** → total latency. **Correct**; `d(1/x) = 4` gives `≥ 20` cycles.
- `we` = **logic levels** → returns `4 × 90 = 360`, a true fact about a weighted tree that **is not
  the physical critical path** (measured: 90). The theorem does not know registers exist.
- **area** → not a critical-path quantity at all; it sums over *blocks*, not along the *longest
  path*. Wrong theorem — and the one whose measured ratio (×4.00) looks most like a confirmation.

**A weight that is not path-additive in the physical artifact makes the conclusion false while
leaving the theorem true.** Written into `EMLNetlistDepth`'s header, next to the socket it qualifies,
because the failure mode is using a sound theorem on the wrong quantity — which no gate in this
repo can catch.

### `MachLib.EMLNetlistDepth`: which tree bounds survive SHARING

The question that decides whether the reciprocal lower-bound programme means anything downstream:
hardware is a DAG, not a tree, and every real datapath shares subexpressions. **Which tree bounds
survive?** The answer is asymmetric, and it inverts the naive guess.

- **Depth survives exactly.** A straight-line EML program is modelled directly (`EMLInstr`,
  `ProgWf`: an instruction may only read strictly earlier results). `netDepth` is defined on the
  *program*, `EMLTree.depth` on the *unfolding*, and `netDepth_eq_depth` proves them equal with **no
  hypothesis at all** — which is exactly the statement that sharing is invisible to depth.
  Consequently `inv_x_not_in_eml_depth_le_3` transfers verbatim:
  **`inv_x_netlist_depth_ge_four`** — no straight-line EML datapath computes `1/x` with
  combinational block-depth `< 4`. And since each level drops the index by at least one
  (`unfold_depth_le_index`), **`inv_x_netlist_index_ge_four`**: the output cannot sit before index
  4, so at least **five instruction slots**.

- **Size survives only as a logarithmic shadow — CORRECTED.** An earlier draft of this entry said
  size "does not survive at all". That is overstated, and an outside reader caught it.
  `unfold_size_le` bounds the unfolding by `2^(i+1)`, so `s(1/x) ≥ 9` *does* force an output index
  `≥ 3` (**`inv_x_netlist_index_ge_three_from_size`**) — a true bound, which the depth route's `≥ 4`
  **strictly dominates**. The right statement is "carries a logarithmic shadow, strictly dominated",
  not "carries nothing". The exponential loss is concrete: `sqProg_gap_at_four` — **5 instructions,
  31 nodes**.

- **Unfolding preserves semantics, and it is now a named theorem.** `progEval` evaluates the program
  the way hardware does — reading earlier results, sharing them — and **`progEval_eq_unfold_eval`**
  proves it agrees with the unfolding. This is load-bearing: without it `unfoldAt` is a definition
  nobody had to accept and a tree lower bound constrains nothing. Every transfer theorem now takes
  its hypothesis on `progEvalAt`, i.e. on the *program*. `inv_x_netlist_depth_ge_four` consequently
  **dropped its `ProgWf` hypothesis** — well-formedness is needed for the index bound, not the depth
  bound. The claim auditor flagged the strength change on the next run.

- **Any path-additive cost survives sharing, not just unit depth.** **`netWDepth_eq_wdepth`**
  generalises the invariance to per-kind block weights `(wc, wv, we)`, with
  `wdepth_unit_eq_depth` recovering ordinary depth at `(0,0,1)`. `(+, max)` is blind to sharing
  while node-counting is not — that is the algebraic reason for the whole asymmetry, and it is the
  socket a measured per-block latency, LUT-depth or energy figure plugs into without re-proving the
  bridge.

- **Therefore `s(1/x) ∈ {9,11}` refines a tree-encoding quantity that no datapath bound depends on,
  while `d(1/x) = 4` is a resource bound.** That inverts what the two arms looked like from the inside:
  the depth arm cost 28 sessions and a refuted conjecture, the size arm looked like the sharper
  number. Neither was chosen for this reason. Recorded because the useful one was not the one that
  looked useful.

- **Scope, stated rather than implied.** "Datapath" means a straight-line program over the EML
  primitive `(a,b) ↦ exp a − log b`, the block Forge's hardware lane emits. Nothing here bounds gate
  depth *inside* a block, and nothing here is a lower bound against arbitrary circuits — that would
  be a circuit-complexity claim and this is not one.

- **The overclaim this must never become.** If a synthesised block measures 6 ns, `d(1/x) = 4` does
  *not* license "every reciprocal circuit needs 24 ns". Four serial *abstract* EML dependencies is
  what is proved; retiming, pipelining, a different internal implementation and a different
  technology are all untouched. A measurement licenses a statement about **one synthesised
  artifact**, reported alongside the structural bound and never fused with it. Written into the
  module header so it survives the next reader.

- `netDepth_eq_depth` needs only `[MachLib.Real, MachLib.Real.zeroR]`; the transfer theorems carry
  the ordinary `MachLib.Real` base. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### Level 7 hardening: the relation vocabulary is now a pinned artifact

An outside reader found a real defect and named the pressure point correctly.

- **DEFECT, confirmed and fixed.** Canary 7 asserted `len(objections) == 3` — *cardinality*. A
  quietly weakened obligation list that swaps one obligation for a feebler one **at constant
  count** sailed straight through it. It now pins the obligation **names**. `canary 9` is the
  swap it previously certified: `proof_uses` (the composition obligation, the one that caught the
  flagship gap) → `statement_mentions`, count unchanged at 3.

- **`relations.lock.json`.** Once level 7 traded semantics for set membership, all remaining trust
  moved into the sentence templates and the obligation lists — and a template that renders prose
  stronger than its obligations warrant is the original overclaim one layer down, with a green
  checkmark. **No check can catch that**; it is the question level 7 deleted rather than solved.
  So it is not verified, it is made **expensive**: `RELATIONS` + `ENTAILS` are pinned by sha256,
  and any edit fails the **shipping path** until `--bless-relations` is run deliberately.
  Injection test (template strengthened to "*is fully verified … on real silicon*", obligations
  untouched): shipping-path exit **1**, naming the template. Reachability witness asserted first.

- **`ENTAILS`, deliberately empty.** `asymptotic_upper_bound` genuinely implies
  `pointwise_upper_bound`, and their obligation lists are *identical* — so a monotonicity check
  would admit it. The machinery still refuses, because the pair was never declared (`canary 10`).
  A specimen built on a **true** implication is the only kind that shows the refusal is about
  declaration rather than about correctness. Declared entailments are additionally checked for
  obligation-monotonicity.

- **A second independent renderer was suggested and is NOT being built.** Two renderers over the
  same table produce the same sentence from the same overclaiming template: agreement is
  guaranteed and says nothing about the concern that motivated it. The correlation lives in the
  *table*, not the rendering, so the answer is a pin and a ceremony.

- **Verbatim-only is permanent, not a tunable.** The cost is machine-stilted flagship sentences.
  Loosening to "paraphrase allowed if adjacent to the licensed form" is a one-way door.

- The phenomenon now has a name: **proof–claim drift** — `Valid(T)` does not give `Licensed(C,T)`.
  `tools/claim_audit/README.md` rewritten around it (the ladder is 7 levels, not 6, and level 3
  is documented as unable to certify absence).

- 10 canaries fire; seven gates green; ledger 242 unchanged; `sorryAx` 0.

### The `LogSafe` reduction: rung 2 replaces the tower-form requirement

- `depth_le_two_neg_log_bound` — a **positive depth-≤2 right child** satisfies
  `-log (b.eval x) ≤ N - log x - log x` near `0`. It follows from `rung2_positive_floor`'s quadratic
  floor `b x ≥ C·x²` by monotonicity of `log`.

- **Why this retires the quantitative half of the open item.** The corrected note on `LogSafe` said
  removing it needs a **tower-form** decay bound `b x ≥ exp(-E_j x)`. Rung 2 gives strictly more, and
  gave it already: a *polynomial* floor, whose `log` is a **log-scale** bound. A depth-≤3 tree has a
  depth-≤2 right child, so at depth ≤ 3 **nothing quantitative is missing**. The requirement was
  overstated by a whole scale, twice — first as a positive floor, then as a tower bound — and what
  fixed it was a theorem proved for an unrelated reason.

- `neg_log_bound_under_rung_one` — `N - log x - log x ≤ envelope 1 (log (exp N + 2)) x`, so the
  discarded term is bounded by **rung one regardless of `N`**. "Costs one extra level" is now a
  number, not a hand-wave.

- **What actually remains is sign stability, not a bound.** Rung 2 needs the right child positive on
  an *interval*; a pointwise sign fact gives that only if the child does not oscillate near `0`. That
  residue is a tameness statement — and it is where an o-minimality / Khovanskii citation **genuinely
  applies**, for *finiteness of sign changes*, which is what those theorems actually give. The
  original attribution asked them for a positive floor, which they cannot give. Same literature,
  different proposition, and this time the implication holds.


- **Typed claims** (relation `asymptotic_upper_bound` / `pointwise_upper_bound`, both new).
  These sentences are GENERATED from the claim objects, not written:

  > The negated log of a positive depth-≤2 EML tree is bounded above by N − 2·log x on a neighbourhood of 0 whose existence the theorem asserts rather than assumes.

  > The discarded −2·log x term is bounded above by rung one of the growth envelope on (0,1].
- `sorryAx` 0; ledger 242 unchanged; six gates green.

### Claim audit level 5: relation integrity — the prose is now GENERATED

- The rungs below are all string questions about a printed form. *"Does the statement assert this
  relation between these objects"* is not one, and pretending a substring search answers it would be
  the same error the ladder exists to catch. So the relation is **not verified — it is made
  binding.**

  A claim declares `subject / relation / object / bound / epistemic_type` from a **closed
  vocabulary**, and the relation names the structural obligations it entails. Declaring
  `end_to_end_tracking` obliges `conclusion_mentions`, `hypotheses_count` **and** `proof_uses`;
  omitting any of them is rejected. **Naming a stronger relation buys stronger obligations, not a
  stronger sentence.**

- **The prose is rendered from the record**, and the auditor requires the *generated* sentence to
  appear in the source document — not an author's paraphrase of it. That reverses the architecture:
  instead of *human prose → try to validate it*, it is *checked record → generate prose*. The two
  sentences the current records license:

  > The 3 ULP bound on fxpid's implementation error holds in the real domain.

  > The fixed-point affine datapath tracks the exact real trajectory to within one ULP per step, with the bound derived from the implementation rather than assumed.

- **Firing specimen**: `end_to_end_tracking` declared bare raises exactly three objections, one per
  shed obligation.

### Claim audit level 4: strength integrity

- **`hypotheses_count`** — the theorem's top-level antecedent count must be what the prose was
  written for. `hypotheses_of` keeps what `conclusion_of` discards, because the number and shape of
  a theorem's hypotheses **is** its strength.

  This catches the **mirror** of the flagship failure: not prose that outruns a theorem, but a
  theorem quietly *weakened* later — a hypothesis added — while the prose describing it stays put.
  Decidable both ways, since the antecedents are a syntactic prefix of the printed type.

- **Firing specimen** checks the counter *discriminates*: 1 hypothesis on `fxaffine_traj_tracks_exact`
  versus 6 on `pid_trajectory_from_bits`. A counter that always returned the same number would pass
  a strength check vacuously, so the specimen asserts a difference rather than a value.

- Registered: the end-to-end theorem at **1** hypothesis (`0 ≤ qval c`), and
  `fxpid_real_trunc_lt_3ulp` at **0** — mechanically confirming the "both are unconditional, the
  `Nat` premise is discharged inside rather than assumed" claim made when the bridge landed.

### Claim audit level 6: composition integrity

- **`proof_uses`** — the proof must actually go through the lemmas the prose credits. Extracted
  from the proof term (`#print thm`, everything after `:=`). A **third** question, distinct from the
  two the auditor already asked:

  | check | question |
  |---|---|
  | `#print axioms` | what could this rest on — the trust base |
  | `statement` / `conclusion` | what does this talk about — the subject |
  | `proof_uses` | what does this actually go through — the composition |

- **Asymmetry, opposite in direction to level 2.** A lemma *named* in a proof term was genuinely
  invoked, so presence is decisive for **direct** use. Absence is **not** decisive for non-use — the
  lemma could be reached transitively. So `proof_uses` is a positive obligation only; a passing
  `proof_uses` never means "nothing else was involved".

- **Firing specimen**: `pid_trajectory_from_bits`'s proof never invokes `fxpid_trunc_lt_3ulp`.
  **The flagship claim now fails independently at three levels** — subject, conclusion, and
  composition. One gate can be fooled; three agreeing is evidence the gap is real rather than an
  artifact of how any single check is written.

- Registered on the end-to-end claim: `fxaffine_traj_tracks_exact` must invoke both
  `affine_trajectory_bound` and `fxaffine_step_error`. It does — so the composition is now
  mechanically attested, not asserted.

### Claim audit level 3: conclusion integrity

- **`conclusion_mentions`** — the artifact must appear in what the theorem **concludes**, not merely
  somewhere in its statement. Strips top-level `∀ …,` binders and `→` antecedents (depth-tracked, so
  arrows inside a hypothesis's own type are ignored) and checks the consequent.

  This blocks the attack the outside reader named: *an unused hypothesis mentioning `fxpid` would
  pass the subject check while changing nothing.* It would not pass this one.

- **Firing specimen**: `depth3_bounded_left_absurd` mentions `t1` in its statement and concludes
  `False`. So a claim that it concludes something about `t1` is rejected — statement ✓, conclusion ✗.
  The specimen retires itself if `t1` ever reaches the conclusion.

- Registered on both bridge claims: `fxaffine_traj_tracks_exact` must conclude about `ulp` and
  `fxTraj`; `fxpid_real_trunc_lt_3ulp` must conclude about `fxpid`. Both do.

### ▸▸ Join 2 closed for the affine plant: the datapath's own error drives the trajectory bound

- **`MachLib.Real.fxaffine_traj_tracks_exact`** — for every bit-vector trajectory the netlist
  produces, its Q-value stays within `ulp · geom (qval c) n` of the exact real affine trajectory,
  and `(1 − qval c)·(ulp · geom …) ≤ ulp` makes that `n`-independent when the plant contracts.

  **The `ε` is `ulp`, produced by the netlist** — `fxaffine_step_error` derives it from
  `fxmul_real_trunc_lt_ulp`, and the theorem quantifies over `List Bool`, not over a free real.
  This is the composition the flagship sentence asserted and did not have.

- **The right subject was `fxaffine`, not `fxpid`.** The trajectory theorem's plant is the affine
  map `c·x + d`, and `FixedPointRTL` already documents `fxaffine` as "the PID plant / EMA / RC
  kernel"; `fxpid` is the *controller's* multiply-add. Part of why the chain never composed is that
  the two halves were about different datapaths.

- **Scope.** This closes the chain for the **affine plant kernel**. It does **not** close it for
  `fxpid`: `pid_trajectory_from_bits` still quantifies `ε` universally, and connecting the
  controller's output to the plant's state update needs a closed-loop model that does not exist
  here. The `--self-test` specimen therefore still fires, correctly.

- **Level 2: subject integrity modulo unfolding.** `statement_mentions_deep` walks the theorem's
  type and then the printed bodies of the constants it names, so it sees a subject that enters one
  δ-step away. `fxaffine` is **invisible** to the syntactic check and **visible** to this one —
  which is the specimen that validates it.

  **The two directions are not symmetric, and this is not an implementation limit.** Bounded
  unfolding can certify *presence* (stop the moment the target is found) but never *absence*
  (budget exhausted ≠ unreachable). So absence claims — including the flagship firing specimen —
  stay on the syntactic check, which is decisive for the statement as printed. Same lesson this
  corpus already learned from grid search: a bounded search cannot prove a negative. The auditor
  reports `truncated` explicitly rather than passing a search that found nothing.

## [Unreleased] — 2026-08-10

### Trust gates: the auditor now checks what a theorem SAYS, not only what it rests on

- **A seventh check, and the failure that forced it.** `pid_trajectory_from_bits` was documented as
  carrying the bit-level truncation into the closed-loop bound. Its statement mentions **no
  bit-level object at all** — it quantifies `ε` universally and takes the per-step bound as a
  hypothesis. `sorryAx`, the axiom ledger and the claim auditor all passed, because every one of
  them asks *what does this theorem depend on*, never *does the prose describe the theorem that
  exists*.

  `claim_audit.py` gains **`statement_mentions`**: a claim naming an artifact must be backed by a
  theorem whose **type** references it. `#check @thm`, not `#print axioms thm`. Had it existed, the
  flagship claim would have been rejected on the day it was written.

  Firing specimen in `--self-test` (house rule: a gate without one is unvalidated) — it asserts
  `pid_trajectory_from_bits`'s statement has no `fxpid` in it, and *fails loudly if that ever stops
  being true*, which is precisely the day the claim becomes legitimate.

- **`MachLib/FixedPointRealBridge.lean`** — join 1 of the flagship chain, closed.
  `fxmul_real_trunc_lt_ulp` / `fxpid_real_trunc_lt_3ulp` state the truncation
  bounds over `MachLib.Real`, derived from the `Nat` versions via `natCast_lt_mono`
  (proved here from `natCast_succ`; the corpus had monotonicity only as a file-local lemma and no
  strict version). Both unconditional — the `Nat` premise is discharged, not assumed. Join 2
  (controller error → closed-loop state-update error) needs a plant model and remains open.


### ▸▸ `d(1/x) = 4` — the depth question is SETTLED

- **`MachLib.inv_x_not_in_eml_depth_le_3`** — **no depth-≤3 tree is `1/x` on the positives.** With
  `invX4` a depth-4 reciprocal, `inv_x_depth_eq_four` closes the bracket the arm has carried since
  it began: 28 sessions trying to prove `1/x ∉ EML` at any depth (false — `inv_x_mem_EML` refuted it
  with a depth-6 witness), then `invX4` at depth 4, then `2 ≤ d`, `3 ≤ d`, and now `4 ≤ d`.

  The proof dispatches an arbitrary depth-≤2 left child into one of six behavioural classes, each
  closed separately and **none by enumerating configurations**:

  | left child | instrument |
  |---|---|
  | `const c`, `var` | leaf theorems |
  | `eml A B`, `A` grows at `∞` | `∞`-side rank mismatch |
  | `eml (const p) var`-headed | `0⁺`-side rank mismatch (a `1/x` pole) |
  | `eml a var` | leaf-var-right |
  | `eml A B`, `A` constant, `B` off `0` | bounded left child + **rung 2** |
  | `eml A (eml var (const q))`, `log q = 1` | log-scale pole |

- **`MachLib.inv_x_size_ge_nine`** / **`inv_x_size_nine_or_eleven`** — the size bracket sharpens to
  **`s(1/x) ∈ {9, 11}`**, since `2·depth + 1 ≤ size` turns `depth ≥ 4` into `size ≥ 9` and oddness
  kills 10. **Still not `s = 11`**: a 9-node depth-4 reciprocal would undercut `invX4`, and the depth
  arm cannot exclude it because 9 nodes permit depth 4. Flagged before the depth work began; it
  survives exactly as flagged.

- **`MachLib.rung2_positive_floor`** — the load-bearing input. *Every positive depth-≤2 tree is
  bounded below by `C·x²` near `0`*, so nothing at depth 2 can be positive and decay faster than
  quadratically — in particular nothing can imitate `exp(−1/x)`. A statement about the **grammar**,
  with the depth-3 case as a corollary rather than its motivation.

- **Three pole regimes, and they are genuinely distinct.** `exp (t1 x)` bounded; `t1 ≍ 1/x` (a
  *double* exponential); and `t1 ≍ −log x`, which sits between them and is fatal only because
  `exp c₀ > 1` **strictly** leaves a residue after the equation's own `1/x` is subtracted. The last
  shape of the arm fell through the first two for exactly that reason.


### ⚠ CORRECTION — the `LogSafe` removal was attributed to the wrong theorem

The growth envelope's header, and three frontier briefs, said that removing the `LogSafe` side
condition needs *"a shallow tree cannot be arbitrarily small while staying positive — i.e.
finiteness of sign changes, a Khovanskii/Pfaffian input"*. **Both halves were wrong.** Caught by an
outside reader, verified against the source, corrected in
`MachLib/EMLGrowthEnvelope.lean`'s header:

- **A zero count cannot give a positive floor.** `exp(−x)` is positive on `(0,∞)`, has no zeros at
  all, and still has infimum `0`. No Pfaffian zero-counting theorem discharges the condition — it
  was the wrong theorem, not merely an unproved one.
- **The induction does not need a positive floor.** `LogSafe` is consumed at exactly one step, and
  only to *discard* `−log(b x)`. What suffices is a lower bound on the right child of **tower form**
  (`b x ≥ exp(−E_j x)`), which costs one extra rung — a quantitative *decay-by-depth* bound, not a
  zero count. That is the exact restricted lemma to aim at, and it is Khovanskii-*adjacent* (effective
  bounds by Pfaffian format) with the caveat that **totalised `log` breaks Pfaffian-ness**: these
  terms are only piecewise Pfaffian and any citation applies per piece.

**No axiom was spent, and it is now unclear that one is needed** — `exp(−1/x)` is in EML and decays
faster than any polynomial, yet its `−log` is exactly `1/x`, which sits inside rung 1.

### MaxEnt: the uniform distribution maximises entropy

- **`MachLib.Real.maxent`** / **`maxent_log_perplexity`** (`MachLib/KLDivergence.lean`) — `H(p) ≤
  −log u = log(1/u)` for any unit-mass `p` against a uniform reference `q ≡ u`. **No new machinery:**
  `log n − H(p)` *is* `KL(p ‖ uniform)`, and `kl_nonneg` was already machine-checked, so the only
  work is `ncrossH_const` — one list induction collapsing `Σ pᵢ·log u` to `(Σ pᵢ)·log u`. Stated in
  the uniform weight `u` rather than a cardinality, so no `Nat` cast is needed; `log(1/u)` is the
  perplexity form and is literally `log n` on an `n`-point support. `sorryAx`-free, zero new axioms.
  The entropy cluster now carries all four classical facts: Legendre duality, Fenchel–Young,
  `KL ≥ 0`, cross-entropy ≥ entropy, and MaxEnt.

### EML depth 3: the last family, and the decay-by-depth ladder

- **Four of the six `A`-shapes of the last depth-3 family, closed by a RANK MISMATCH.** Read at
  either end, the equation is `exp(t1 x) = 1/x + log(t2 x)` — `exp` of a depth-2 tree against `log`
  of one, **two rungs apart**. `depth3_left_unbounded_absurd` closes the shapes where `A` grows at
  `∞`; `depth3_left_pole_at_zero_absurd` closes `A = eml (const p) var`, a pole at `0`. The
  substitution `x = exp(−t)` turns every `1/x` into `exp t`, so the pole problem *becomes* the growth
  problem and one instrument covers both ends, division-free. **No configuration enumeration and no
  parameter regimes** — neither argument asks what the constants are.

- **`MachLib.depth_le_one_positive_floor`** — **a positive depth-≤1 tree has a linear floor near
  `0`.** The base rung of the decay-by-depth ladder, and **sharp**: the only shape whose value
  actually reaches `0` is `eml var (const q)` at `log q = 1`, where `t x = exp x − 1 ≥ x` — linear,
  with no quadratic correction needed at this depth. Positivity is a *hypothesis*, not derived from
  a pin, which is what makes it reusable and is precisely what the leaf-`var` branch could not do:
  its floors were entangled with its own equation.

  > This is the theorem family **both** remaining open items point at. Removing `LogSafe` wants a
  > decay bound at all depths (weak); the last depth-3 case wants one at depth 2 (sharp). Two open
  > problems, one ladder.

- **The bounded-left core, generalised rather than re-derived.** `leaf_var_arith`,
  `leaf_var_floor_absurd`, `leaf_var_quad_arith` and `leaf_var_quad_floor_absurd` turn out to be the
  `W = exp 1` instances of `bounded_left_*` — every load-bearing lemma of that branch used only the
  bound `exp (t1 x) ≤ W`, never the shape `t1 = var`. Also `exp_beats_linear`/`_past` (`exp` outruns
  any line **at a point we can name**), `depth_le_one_neg_log_bound_at_infty`,
  `depth_le_two_bound_at_infty`, `log_le_of_le_exp_mul'`.

  **`d(1/x)` is UNCHANGED at `{3,4}`.** The remaining case is `A` constant-valued, where the
  arithmetic is now fully discharged and only `t2`'s shape analysis is left.

### EML depth 3: the `t1 = var` family is CLOSED

- **`MachLib.leaf_var_absurd`** — **no depth-≤2 right child lets `eml var t2` be `1/x`.** The first
  *complete family* of the depth-3 arm, closing the residue
  `t2 = eml A (eml var (const q))` that the previous two passes were left resting on. 28 new
  theorems, `sorryAx` 0, **zero new axioms** (ledger 242 unchanged).
  **This does not move `d(1/x)`**, which stays `{3,4}`: the other depth-3 family (`t1 = eml a b`,
  `b ≠ var`, unbounded left child) is untouched and could still hold a witness.

- **`MachLib.leaf_var_right_strict_mono`** — the reusable half. **The right child of a leaf-`var`
  reciprocal is strictly INCREASING below the cutoff**, for any `t2` at any depth: the equation
  gives `log (t2 x) = exp x − 1/x` pointwise and both terms rise. Every earlier closure in this arm
  read a *floor* off the tree; this reads a **direction**, which is what the shapes where the two
  terms cancel need — there the floor is `0` and carries no information. It kills both
  constant-valued `A` shapes outright, citing no floor dispatcher at all.

- **`MachLib.leaf_var_quad_floor_absurd`** + **`MachLib.exp_ge_three_mul`** — a **quadratic** floor
  on the right child is fatal too. Needed because the coincidence stratifies further than the
  constant-`B` case did: with a *moving* `log` the linear coefficient is `κ := G − exp(−G)`, whose
  sign is independent of `γ`, and at **`G·exp G = 1` (`G = Ω`, the omega constant) both `γ` and `κ`
  vanish** and the tree is second order, `≍ (G/4)·x²`. `leaf_var_arith` cannot take that floor —
  its last step is `exp t ≥ t + t`, which ties exactly against the `2t` a square contributes — so
  the peeling trick was applied at `k = 2` instead of `k = 1`: `exp t ≥ e²(t−1) > 4(t−1) ≥ 3t` for
  `t ≥ 4`, on the single numeric input `2 < e` squared.

  > The previous pass found that for **constant-valued** `B` the tangent bound supplies the linear
  > term for free, so the three-way `γ` split collapses to two. **That lesson does not survive a
  > moving `log`** — recorded because it was registered as a prediction and it failed in the
  > direction that mattered.

- **`MachLib.log_shift_ceiling`** / **`MachLib.log_shift_floor`** — two-sided linear bounds on
  `log (exp g + u)` around the cancellation point, both division-free (`exp(−g)` in place of `1/M`)
  and both from the same tangent bound applied to `v := log (exp g + u) − g`.

### EML complexity: the reciprocal in the metric that is priced

- **`MachLib.inv_x_size_ge_seven`** — **two `eml` gates can never compute a reciprocal.**
  `size ≤ 6` plus `size_odd` gives `size ≤ 5`; the bridge `2·depth + 1 ≤ size` then gives
  `depth ≤ 2`, which `inv_x_not_in_eml_depth_le_2` closes. With `invX4` as a witness at 11 nodes and
  oddness ruling out 8 and 10, a **minimal EML reciprocal has size 7, 9, or 11** —
  `inv_x_min_size_seven_nine_or_eleven`. First result of this arc stated natively in the axis
  `docs/cost_theory.md` T38-NNP actually prices. sorryAx-free, zero new axioms.
  **NOT proved: `s(1/x) = 11`.** Sizes 7 and 9 are open; a 528-configuration numerical search over
  all 3- and 4-gate shapes found no witness, but that is evidence, not proof.

- **`MachLib.two_mul_depth_succ_le_size`** — `2·depth + 1 ≤ size`, tight at every depth. Hence
  `size ≤ 10 ⟹ depth ≤ 4`: **the size question is finite in depth**, since any tree of depth ≥ 5
  already costs ≥ 11 nodes. Footprint is `propext, Real, Quot.sound` — pure tree combinatorics, no
  `Classical.choice` and no analysis.

- **`MachLib.growth_envelope`** — a depth-indexed growth ceiling
  `envelope 0 M x = M − log x`, `envelope (k+1) M x = exp (envelope k M x)`. One induction on the
  tree replaces the six ad-hoc shape cases and the cutoff of the earlier depth-1 and depth-2
  ceilings. `depth_gt_of_outgrows` is the contrapositive lower-bound tool, and `size_envelope`
  restates it in node count. Carries a **`LogSafe`** side condition (every `eml` right child `≥ 1`);
  removing it needs finiteness of sign changes for exp-log expressions, a Khovanskii/Pfaffian input.
  **⚠ That last sentence is WRONG and is corrected below (2026-08-10) — `exp(−x)` is positive with
  no zeros and infimum `0`, so a zero count cannot yield a positive floor, and the induction does
  not need a positive floor anyway.** See `MachLib/EMLGrowthEnvelope.lean`'s header.

- **`MachLib.inv_x_within_envelope_one`** — the honest limit: `1/x ≤ envelope 1 0 x`, so the
  reciprocal sits **inside the first rung** and **no growth argument at any rung can exclude it**.
  EML depth is gate complexity, not growth complexity; `d(1/x)` is frozen at `{3,4}`.

- **`MachLib.invX4gen_eval`** — the depth-4 witness is **not isolated**. With both `const 1` leaves
  making their `log`s vanish the tree collapses to `(exp(exp c0) − exp(exp c1))/x`, so the witness
  condition is one equation on two constants: a **curve** of size-11 depth-4 reciprocals.
  `invX4 = invX4gen (log (log (1+e))) 0`.

### Trust gates

- **`scripts/check_aggregator.sh` had two scope defects and now does a real transitive closure.**
  It iterated `find MachLib -maxdepth 1` (308 of 922 files invisible) and tested "imported by any
  `.lean`" rather than reachability, so an **island** of mutually-importing modules passed
  trivially. Found by an axiom count that would not reconcile. Reachable: **616 of 922**. Validated
  with two firing specimens — a subdirectory orphan and a two-module island — each of which the old
  gate passed and the new one fails.

- **`MachLib/Applications/` (12 modules) folded into the aggregator.** It was an unreachable island
  and five of its modules did not build: a bare `apply le_min` was ambiguous between
  `MachLib.Real.le_min` and the namespace-local `AerospaceActuatorGuardBandRate.le_min`. The two are
  the same theorem — identical statement and proof — so qualifying is semantically neutral. No
  hidden `sorry`: every match under those paths was prose in a docstring.

## [2026-07-26]

### New — 2×2 Joseph covariance update: structural PSD + full-width dot bound (`MachLib/Matrix2JosephPSD.lean`)

**`kalman2_joseph_psd`** + **`fxerr_dot2_fullwidth`**: the proof spine for the scheduled-linear-algebra /
Joseph arc (Forge `docs/scheduled_linear_algebra.md`), certifying two obligations *before* the datapath is
built. `kalman2_joseph_psd`: the Joseph-form posterior `P⁺ = (I−K) P (I−K)ᵀ + K R Kᵀ` stays symmetric
positive-semidefinite for any gain K — the numerical-robustness guarantee that makes a recursive covariance
update safe (no gain, and no round-off in the gain, can drive the covariance indefinite; this is *why* real
filters use the Joseph form). Scoped to 2×2 with a Mathlib-free PSD predicate — the quadratic form on entries
(`Psd2`): a congruence `G X Gᵀ` preserves PSD (`psd2_congruence`: its quadratic form at `v` is `X`'s at
`Gᵀv`) and a sum of PSD is PSD (`psd2_add`), so the Joseph update is `psd2_add` of two congruences (`G₁ =
I−K`, `G₂ = K`). `fxerr_dot2_fullwidth`: the full-width scheduled MAC (`seq_mac_fw`) keeps its products
exact and truncates ONCE per dot, so its forward error is a single rounding (≤ 2⁻ᶠ) — a factor-`K`
improvement on the per-product engine's `K·2⁻ᶠ`; it is exactly `fxerr_dot2` with the truncation moved off the
products onto the final add. `sorryAx`-free, ZERO new axioms (Real arithmetic + `mach_ring` + the existing
FxErr algebra; `Real` exposes `OfNat` only for 0/1, so the coefficient 2 is written `(1 + 1)`).

## [Unreleased] — 2026-07-25

### New — 2-D Kalman MMSE-optimality, trace loss (`MachLib/Matrix2KalmanMMSE.lean`)

**`matrix2_posterior_mean_mmse`** + **`matrix2_mmse_excess`**: the vector analogue of
`posterior_mean_mmse` — for a 2-D state the MMSE-optimal estimator is the posterior-mean vector,
minimizing `E[|X−c|²]` (the trace of the error covariance). The key that keeps it tractable in the
Mathlib-free base (no 2-D integration / Fubini): the trace loss **separates per component**,
`E[|X−c|²] = Σᵢ E[(Xᵢ−cᵢ)²]`, so the vector optimality is exactly the sum of the per-component scalar
conjugate MMSE — no new integral. `matrix2_posterior_mean_mmse`: the optimal total conditional MSE
`tr(Σ_post) = postVar₀+postVar₁` (attained by the posterior-mean vector) is `≤` any estimate's total
conditional MSE (`add_le_add_both` of two `posterior_mean_mmse`). `matrix2_mmse_excess`: the excess risk
of `(c₀,c₁)` over the optimum is *exactly* `|c−m|² = (c₀−m₀)²+(c₁−m₁)²` — a sum of squares, `≥ 0`
(`matrix2_mmse_excess_nonneg`) and `0` iff `c=m`, so the posterior-mean vector is the *unique* minimizer.
`sorryAx`-free, ZERO new axioms. (Trace/Euclidean loss, the standard MMSE criterion; the per-component
reduction is why the vector case needs no 2-D integration.)

### New — fixed-point stability of the 2×2 symmetric matrix inverse (`MachLib/Matrix2InverseFixedPoint.lean`)

**`matrix2_sym_inverse_fwd_error`** + **`matrix2_inverse_conditioning`**: the scoped-honest first step
of "scale the math to matrices" — a **fixed-size** inverse (no dynamic loops, no general Cholesky/LDLT),
at exactly the dimension the existing matrix Kalman uses (the EKF innovation covariance `S=H·P·Hᵀ+R` and
`kalman2d` covariance are 2×2, so the gain needs a 2×2 inverse). For symmetric `A=[[a,b],[b,d]]`,
`A⁻¹ = (1/det)·[[d,−b],[−b,a]]` — one reciprocal (of `det`) plus qmuls — so its fixed-point error composes
exactly like the scalar reciprocal forward-error (`kalman_update_1d_fwd_error`), `w:=1/det` carried
abstractly. `matrix2_inv_entry_fwd_error`: each entry `qmul(cofactor, recip)` is within `s + |cofactor|·Erec`
of the exact `cofactor/det`; `matrix2_sym_inverse_fwd_error` bundles all three distinct entries.
`matrix2_inverse_conditioning` is the **divergence bound**: `recip` really approximates `1/det_fx` (the
*computed* determinant), so as an approximation of the exact `1/det` its error is
`≤ Erec0 + Edet·|wf|·|w|` with `|wf|·|w| = 1/(|det_fx|·|det|)` — bounded exactly when the matrix is
well-conditioned (`det` away from 0), diverging as `det→0`. This is the precise sense in which fixed-point
rounding does not make the filter diverge — the numerical-stability companion to the existing
`kalman2d_joseph_psd` structural (PSD) stability. `sorryAx`-free, ZERO new axioms.

**Gain/update composition** (same file): the gain `K = P·Hᵀ·S⁻¹` is a matrix product, so each entry is a
dot product of a `P·Hᵀ` row with an `S⁻¹` column — and the inverse error just bounded flows into it,
boundedly. `fxerr_dot2` (reusable) folds two `fxerr_mul`s + one `fxerr_add` (the `FixedPointCertifier`
additive error algebra) into a perturbed-operand dot product; `matrix2_inv_entry_fxerr` repackages an
inverse entry as an `FxErr` (magnitude + the `s+|cofactor|·Erec` error); **`kalman2_gain_entry_via_inverse`**
plugs the two inverse-column entries (built from the shared reciprocal, carrying `Erec`) into the gain dot
product and bounds the gain entry's fixed-point error — with `Erec` appearing explicitly, so the inversion
error is shown to propagate into the gain with no hidden amplification. `sorryAx`-free, ZERO new axioms.

**State-update forward error** (same file): **`kalman2_state_update_fxerr`** closes the estimate path
`inverse → gain → x'`. One updated estimate component `x'_i = x_i + (K_i0·y0 + K_i1·y1)` — the prior plus
the gain row dotted with the innovation `y = z − H·x` — has bounded fixed-point error, folding `fxerr_dot2`
(the `K·y` dot) and `fxerr_add` (`+ x_i`) over the gain entries' `FxErr` (which carry the inversion error).
So for the 2-measurement 2×2 update the whole estimate path is now forward-error-bounded end to end. (The
covariance update is the same kind of fold; its PSD is the separate structural `kalman2d_joseph_psd`.)
`sorryAx`-free, ZERO new axioms.
(General n×n inversion-stability via Cholesky/LDLT remains the larger arc; at fixed 2×2 the closed form is
equivalent and lands on the current FPGA substrate. Next: matrix MMSE-optimality + a small-n unrolled RTL
kernel.)

### New — the AXI-Stream wrapper control FSM is deadlock-free + drop-free, proven (`MachLib/AxiStreamWrapper.lean`)

**`conservation`**, **`round_trip`**, **`validIn_pulse`**, **`no_stuck_state`** (+ the `*_leaves_on_*` /
`*_holds` lemmas): to feed the 100 MHz Kalman kernel live sensor data it needs a standard AXI4-Stream
`ready`/`valid` bus with backpressure — and the risk a hand-written wrapper carries is exactly that its
control FSM could **deadlock, drop a sample, or re-trigger the multi-cycle core mid-computation**. This
proves it can't. The wrapper is a 3-state Moore machine (`idle`/`busy`/`present`) around the multi-cycle
core; the proofs are **pure discrete reasoning over `Bool`/`Nat` — no `MachLib.Real`, zero MachLib axioms**
(`no_stuck_state` depends on no axioms at all; the rest only on Lean core). SAFETY: `validIn_pulse` — the
core's `valid_in` is a 1-cycle pulse, never re-asserted mid-run (timing contract respected);
`conservation` — `accepted n = emitted n + occ(state)` with `occ ∈ {0,1}`, so at most one sample in flight
and, since input is accepted only from `idle`, an in-flight sample is never overwritten (**no dropped
sample**, `no_drop`); `present_holds` — the output is held with `tvalid` asserted under downstream
backpressure (AXI no-retraction). LIVENESS: each waiting state `*_leaves_on_*` its enabling signal and
`*_holds` correctly meanwhile; `no_stuck_state` — no absorbing state; `round_trip` — from `idle`, once the
three signals arrive the wrapper accepts one input, runs the core, emits **exactly one** output, and
returns to `idle` in a bounded window, with `accepted`/`emitted` each advanced by one. The same FSM the
RTL wrapper implements — proof and circuit share one definition. `sorryAx`-free, ZERO new axioms.

### New — the Kalman **estimate recursion** fixed-point error, coupled (`MachLib/KalmanEstimateRecursion.lean`)

**`kalman_estimate_recursion_fixed_point`** and **`kalman_estimate_recursion_nonexpansive`**: the
coupled half of the recursive fixed-point error — the *estimate* `m`, not just the variance `P`. Unlike
the autonomous variance map, the estimate update `m_n = (1−K_n)·m_{n-1} + K_n·z_n` is a *time-varying*
affine map, and the computed and exact orbits follow *different* maps (computed gain `Kc_n` vs exact
`Ke_n`). Expanding the error gives `δm_n = (1−Kc_n)·δm_{n-1} + (Kc_n−Ke_n)(z_n−m⋆_{n-1}) + τ_n`, so two
forcings ride on the contraction: the gain error `Kc_n−Ke_n` (**where coupling to the variance error
enters** — `K` is a Lipschitz function of `P`) and the update round-off `τ_n`. Proven by a new general
backbone lemma **`nearby_maps_trajectory_bound`** (two orbits under nearby `L`-Lipschitz maps stay close:
`|xc n − xe n| ≤ (σ+ρ)·geom L n`), which generalizes `local_lipschitz_trajectory_bound` from same-map to
different-map — instantiated at `Ac n x = x + Kc n·(z n − x)`, `Ae n x = x + Ke n·(z n − x)`. The
gain-error×innovation bound `ρ` is the hypothesis carrying the coupling (the honest interface, exactly as
`kalman_update_1d_fwd_error` takes `E_recip` as a hypothesis); `σ` the estimate update's own round-off.
At gains in `[0,1]` the accumulation is additive `(σ+ρ)·n`; for a strict contraction it is bounded
uniformly at `(σ+ρ)/(1−L)`. Together with the variance bound this completes the recursion's fixed-point
error, both halves. `sorryAx`-free, ZERO new axioms.

The coupling is then made **numeric**, not a hypothesis: **`kalman_gain_map_lipschitz`** proves the gain
`K(P)=P/(P+r)` is `r/(b+r)²`-Lipschitz on `{P≥b}` (the variance map's `r²/(b+r)²` divided by `r`, since
`g=r·K`), so **`kalman_gain_error_bound`** derives `|Kc−Ke| ≤ γ + (r/(b+r)²)·|δP|` (gain round-off `γ`
plus the *variance* error propagated through the gain), and **`kalman_estimate_recursion_coupled`**
composes it with the estimate bound to give `|mc n − me n| ≤ (σ + (γ + (r/(b+r)²)·DP)·Z)·geom L n` — `ρ`
fully derived from the variance error `DP`, the innovation bound `Z`, and the two round-offs. The
variance → gain → estimate coupling is now machine-checked end to end. `sorryAx`-free, ZERO new axioms.

### New — the Kalman **variance recursion** has a bounded RECURSIVE fixed-point error (`MachLib/KalmanVarianceRecursion.lean`)

**`kalman_variance_recursion_fixed_point`** and **`kalman_variance_recursion_nonexpansive`**: the
*accumulated* fixed-point error over the recursion, not just one step — what a `filter` needs beyond a
`measurement update`. The posterior-variance map `g(P) = P·r/(P+r)` is autonomous (depends on neither the
estimate nor the measurement), so its recursion is a clean scalar contraction with no coupling. Writing
`w = 1/(P+r)` gives `g(P) = r − r²·w`, hence `g(P) − g(P⋆) = r²·(P−P⋆)·w·w⋆`, so `g` is
`r²/(b+r)²`-Lipschitz on `{P ≥ b}` (**`kalman_var_map_lipschitz`**): nonexpansive (`L=1`) at `b=0`,
strictly contracting (`L<1`) for `b>0`. This drops straight into the pre-existing contraction backbone
(`local_lipschitz_trajectory_bound` / `contraction_certificate`): the Q16.16 variance recursion stays
within `ε·geom L n` of the exact real recursion over `n` steps — `≤ ε·n` at `b=0` (additive `≈N·ulp`
growth, unconditional), and bounded UNIFORMLY for all `n` at `ε/(1−L)` when `b>0`. The estimate (`m`)
recursion is the coupled follow-on (its per-step error feeds on the variance error through the gain);
the variance bound here is its prerequisite. `sorryAx`-free, ZERO new axioms.

### New — the fixed-point Kalman kernel is near-MMSE-OPTIMAL, machine-checked (`MachLib/KalmanUpdateFixedPoint.lean`)

**`kalman_update_1d_fx_near_mmse`** and **`kalman_update_1d_conditional_mse_near_optimal`**: the
*composition* the flagship claim rests on, proved rather than asserted. Two prior results —
(1) the real posterior mean is MMSE-optimal (`posterior_mean_mmse`), and (2) the Q16.16 kernel output is
within `ε` of that real mean (`kalman_update_1d_fwd_error`) — do NOT by themselves give "the fixed-point
kernel is near-optimal". The join is proved: since the conditional MSE of any estimate `c` of `X | Y=y`
is exactly `τ² + (c − m(y))²` (parallel-axis, no cross term), the fixed-point output `kalman_hw`, being
within `ε` of the posterior mean `m`, has conditional MSE sandwiched
`τ² ≤ τ² + (kalman_hw − m)² ≤ τ² + ε²`. So the *implemented* estimator's excess risk over the *provably
optimal* one is `≤ ε²`, with `ε = s + |z−x|·(s + |p|·E_recip)` from the datapath forward-error. This
closes the "two rigorous things, join asserted" gap between MMSE optimality and finite precision.
`sorryAx`-free, ZERO new axioms.

### New — `∫₀^∞exp(-t²)dt = √π/2`, from scratch, zero new axioms (`MachLib/GaussianLaplaceRoute.lean`)

**`gaussianImproperIntegral_eq_sqrt_pi_div_two`**: `gaussianImproperIntegral = sqrt pi / (1 + 1)` —
the classical Gaussian integral, proven end to end in MachLib's Mathlib-free real-analysis base.
Built via a Laplace/Feynman parameter-differentiation trick: `F(t) := gaussianI(t)²`,
`G(t) := ∫₀¹exp(-t²(1+x²))/(1+x²)dx`, `F' = -G'` via a from-scratch Leibniz differentiation-
under-the-integral-sign theorem (`hasDerivAt_GFn`), hence `F+G` constant on `[0,∞)` (an
open-interval FTC-uniqueness argument extends it down through the boundary kink at `t=0`, where
`gaussianI` — hence `F` — has no two-sided derivative), hence
`gaussianImproperIntegral² = F(0)+G(0) = 0 + π/4`, hence the result via `sqrt_sq` +
`mul_left_cancel`. `π` enters ONLY as a bare trig fact (`cos(π/2)=0`/`sin(π/2)=1`) — `atan(1)=π/4`
is DERIVED, not axiomatized, via a double application of `ftc_riemann` to the same trivial
integral `∫₀^{π/4}1dθ`. `sorryAx`-free, ZERO new axioms anywhere in the arc that built this (300
pinned, unchanged from before this project started). ~2144 lines / 138 theorems/defs, built
across roughly 30 pushes. The earlier disk/square-sandwich route (`GaussianDiskSandwich.lean`,
`D(R)≤S(R)≤D(R√2)`) remains a complete, correct, standalone result — abandoned as the critical
path only because its own derivative needs genuine 2D polar coordinates this 1D-only codebase
doesn't have.

### New — the scalar Kalman/Gaussian update is MMSE-optimal, from scratch, zero new axioms (`MachLib/GaussianConjugacy.lean`)

On top of the √π result and a full from-scratch second-moment theory of the scalar Gaussian
(`MachLib/GaussianDensityIntegral.lean`: `∫dens=1`, mean `μ`, variance `σ²`, and the parallel-axis
decomposition `∫(x-c)²dens = σ²+(c-μ)²`), MachLib now proves the scalar Gaussian-conjugate Bayesian
(Kalman) update is the **minimum-mean-squared-error estimator** — with no measure theory, no 2-D
integration, and ZERO new axioms (300 pinned, unchanged).

- **`jointDensity_conjugacy`**: the Bayesian conjugacy factorization. For prior `X~N(μ,σ²)` and
  measurement `Y=X+N` with independent noise `N~N(0,r²)`, completing the square factors the joint
  density as marginal `Y~N(μ,σ²+r²)` times posterior `X|Y=y ~ N(m(y),τ²)`, where `m(y)=μ+K(y-μ)`,
  `K=σ²/(σ²+r²)` (Kalman gain), `τ²=σ²r²/(σ²+r²)`.
- **`jointDensity_marginal_tendsto`**: integrating `x` out leaves the marginal `Y~N(μ,σ²+r²)` — no
  new Gaussian-integral identity needed (validates the scalar-density scoping).
- **`posterior_mean_mmse`** / **`posteriorMSE_tendsto`**: the posterior/Kalman mean minimizes the
  conditional MSE `τ²+(c-m(y))²`, achieving the minimum posterior variance `τ²` (parallel-axis at
  the posterior).
- **`optimalMSE_tendsto`** / **`mse_lower_bound`**: the posterior-mean estimator's total
  (unconditional) MSE is exactly `τ²`, and no continuous estimator beats it — via the iterated-
  integral device (inner `x`-integral closed-form by parallel-axis, single 1-D outer `y`-integral).
- **`postMean_eq_kalman`**: cross-checks the optimal gain against the pre-existing purely-algebraic
  `kalman_gain`.

`sorryAx`-free. Honest scope: scalar state+measurement; "any estimator" = any continuous
`φ:Real→Real` (MachLib has no measurable-function type). Runtime witness:
`corpus/eml/lane5_open_problems/kalmanMMSE_witness.py` (quadrature confirms every closed form and
that the posterior mean is the numerically-verified MMSE estimator, min MSE = `τ²`).

## [Unreleased] — 2026-07-09

### New — absolute, cancellation-tolerant forward-error fold (`MachLib/AbsoluteError.lean`)

The certifier's `ForwardError.Renc` is a *relative* enclosure: it composes only on a cancellation-FREE
tree of non-negative quantities (`cosh`, `x²+y²`). General EML arithmetic cancels (`a − b` with `a ≈ b`),
where the relative bound is vacuous. This adds the honest general answer — the **absolute** running-error
bound (Higham, *Accuracy and Stability*, §3.4): **`MachLib.Real.AbsEnc E fl e := |fl − e| ≤ E`**, with
`sorryAx`-free node lemmas `absenc_exact` / `absenc_round` (leaves) and `absenc_add` / `absenc_sub` /
`absenc_mul` (arithmetic). The **`sub` node carries the SAME bound as `add`** — cancellation destroys
*relative* accuracy, never the *absolute* bound, which is exactly what makes this fold general.

Capstone **`absenc_sub_rounded`** reproduces the *exact* `u·(2+u)·(|xe|+|ye|)` bound that
`CompositeRuntimeError.eml_fwd_reduces_to_primitives` proves by hand for `eml = exp x − log y`, now a
two-line instance of the general `absenc_sub` fold (one ring identity). The bespoke composite-error proof
is thereby subsumed by a reusable per-node accumulation. `MachLib.Real`-only, no Mathlib.

**Wired through the emitted C (`MachLib/AbsoluteBridge.lean`).** `FloatRealBridge`'s `pipeline_*`
connected T1's emitted C to T3's *relative* forward error, but only for cancellation-free trees. The
absolute fold now closes that gap on the canonical CANCELLING kernel — the 2×2 determinant / cross-product
`x·y − z·w` (`detEML`). **`pipeline_det`**: the value the *emitted C* computes (`evalC ∘ emitC`), through
`toR`, is within `u·(2+u)·(|X·Y|+|Z·W|)` of the exact `X·Y − Z·W` — the same EML→emitC→evalC→toR span as
the relative pipeline, now VALID UNDER CANCELLATION (`X·Y ≈ Z·W`, where `Renc` is vacuous) and with NO
sign hypothesis on the inputs. `sorryAx`-free; assembled from two `br.mul` roundings + one `br.sub` via
`absenc_sub_rounded` + `emitC_correct`.

**Generalised to any arithmetic tree (`MachLib/AbsoluteFold.lean`).** `pipeline_det` was one kernel; this
folds the `absenc_*` nodes over an ARBITRARY literal/variable/`+`/`−`/`×` EML tree. Recursive `exactR`
(exact real interpretation) and `absErr` (accumulated absolute bound) — `noncomputable`, mutual with a
`List EML` companion like `evalEML` so the node equations reduce structurally — plus one structural
induction over the fragment `IsArith`. **`pipeline_arith`**: for any `IsArith e`, the value the emitted C
computes, through `toR`, is within `absErr … e` of the exact `exactR … e`; every node discharged by its
`absenc_*` lemma + the bridge rounding, leaves exact, cancellation handled by `absenc_sub`. `pipeline_det`
is now literally the `detEML` instance (`isArith_detEML`). `sorryAx`-free.

The `neg` node is included: `FPBridge` gains a `neg` field — an EQUALITY `toR (-a) = -(toR a)`, not a
`RoundsW`, because IEEE-754 negation is exact (sign-bit flip, no rounding) — and `absenc_neg` carries the
absolute error through unchanged (`|(-flx)−(-xe)| = |flx−xe|`). So `IsArith` / `pipeline_arith` now cover
literal / variable / `+` / `−` / `×` / **negation**.

**Transcendental node core — `absenc_lip` (`MachLib/AbsoluteError.lean`).** The forward-error rule for a
unary primitive `f`: if `f` is `L`-Lipschitz, the input is within `Ex`, and the primitive rounds within
`Eround`, then the output is within `Eround + L·Ex` — input error amplified by the Lipschitz sensitivity,
plus the primitive's own rounding. This is the reusable heart of the `tr1` (`exp`/`sin`/`tanh`/…) fold
node; instantiating it per primitive uses MachLib's existing Lipschitz lemmas (`TrigLipschitz`,
`HyperbolicLipschitz`) + the primitive's `RoundsW` spec. `sorryAx`-free.

**Transcendental over an arithmetic subtree, through the emitted C — `pipeline_tr1_of_arith`
(`MachLib/AbsoluteFold.lean`).** A unary primitive `t` (real semantics `f`, `L`-Lipschitz) applied to ANY
arithmetic `e`: the emitted C's value, through `toR`, is within `Eround + L·(absErr … e)` of the exact
`f (exactR … e)` — the arithmetic fold's absolute error amplified by the primitive's Lipschitz
sensitivity, plus its rounding. Composes `evalEML_absErr` (the whole arithmetic fold) with `absenc_lip`
across `emitC_correct`, so the absolute cancellation-tolerant certificate now reaches one transcendental
layer over any arithmetic tree (e.g. `sin(x·y − z·w)`). Honest scope: covers the GLOBALLY-Lipschitz
primitives (`sin`/`cos`/`tanh`/`arctan`/`abs`, `L = 1`); `exp`/`log`/`sinh`/`cosh`/`tan` need a
local-Lipschitz variant, and the binary `tr2` primitives (`eml`, `pow`) decompose into unary + arithmetic
nodes — the remaining follow-ons. `sorryAx`-free.

**Local-Lipschitz node + the `exp` instance (`MachLib/AbsoluteError.lean`, `MachLib/ExpLipschitz.lean`).**
`absenc_lip_local` — the same forward-error composition as `absenc_lip`, but `f` need only be `L`-Lipschitz
on `[lo,hi]` provided BOTH the input and the exact value lie there (the two range hypotheses are the honest
cost of leaving the globally-Lipschitz class). `ExpLipschitz` discharges the hypothesis for the canonical
unbounded-derivative primitive: `exp_lip_lt`/`exp_lip_local` prove `exp` is `exp hi`-Lipschitz on
`(−∞, hi]` (MVT slope `exp c ≤ exp hi`, via `mean_value_theorem_ct` + `HasDerivAt_exp` + `exp_monotone` —
the sound closed-interval MVT), and `absenc_exp_local` assembles the `exp` forward-error node: input within
`Ex`, both in `[lo,hi]` ⟹ output within `Eround + (exp hi)·Ex`. So the fold's transcendental layer now
reaches the unbounded-derivative primitives, not just the globally-Lipschitz ones. `sorryAx`-free.

**Remaining local-Lipschitz primitives — `log`/`sinh`/`cosh` (`MachLib/TransNodes.lean`).** Completes the
unbounded-derivative set. `log_lip_lt`/`log_lip_local`: `log` is `1/lo`-Lipschitz on `[lo, ∞)` (`lo > 0`) —
the MVT slope `1/c ≤ 1/lo` for `c ≥ lo`, via `mean_value_theorem_ct` + `HasDerivAt_log_pos` +
`div_le_div_pos`; `absenc_log_local` gives its forward-error node (`Eround + (1/lo)·Ex`). `sinh`/`cosh`
already have bounded-domain Lipschitz bounds in `HyperbolicLipschitz` (`cosh R`/`sinh R` on `|·| ≤ R`);
`absenc_sinh_local`/`absenc_cosh_local` wrap them into `absenc_lip_local` nodes. So all five
non-globally-Lipschitz primitives (`exp`, `log`, `sinh`, `cosh` — `tan` excluded, poles) now have absolute
forward-error nodes. `sorryAx`-free.

**Recursive nesting — arbitrary arithmetic + transcendental trees (`MachLib/AbsoluteFoldNest.lean`).** The
fold previously stopped at ONE transcendental layer; this closes the recursion. `IsFold` allows `tr1`
nodes ANYWHERE (transcendental-of-transcendental, arithmetic-of-transcendental, …) for the primitives a
`globLip` predicate marks globally-Lipschitz. **`nested_fold`/`pipeline_nested`**: for any `IsFold e`, the
emitted C's value, through `toR`, is within SOME absolute bound of the exact `exactRn … e` over the whole
nested tree. The move that makes recursion clean: the bound is EXISTENTIAL (`∃ E, AbsEnc E …`), so the
`tr1` step needs no weakening (the witnessed `E` may depend on the float eval) — each node just assembles
`E` from the sub-bounds via its `absenc_*` lemma. `exactRn` (exact interpretation with a `tr1` case) is the
only new recursive def (`noncomputable`, mutual-with-`List`). Non-vacuity: `sin(x·y − z·w)` — a
transcendental over the cancelling determinant — is in the fragment. Scope: globally-Lipschitz `tr1`
primitives (`sin`/`cos`/`tanh`/`arctan`/`abs`); the local-Lipschitz ones need per-node domain tracking
through the nesting, a further extension. `sorryAx`-free.

**Local-Lipschitz transcendental over an arithmetic subtree (`MachLib/AbsoluteFoldLocal.lean`).** The
local analog of `pipeline_tr1_of_arith`: an `exp`/`log`/… node over an arithmetic subtree, where the
primitive is Lipschitz only on `[lo,hi]` and both the computed and exact inputs are supplied to lie in
`[lo,hi]`. `pipeline_tr1_of_arith_local` composes `evalEML_absErr` with `absenc_lip_local`, and
`pipeline_exp_of_arith` (`L = exp hi`) / `pipeline_log_of_arith` (`L = 1/lo`) are the concrete instances
(from `ExpLipschitz`/`TransNodes`). So the emitted-C certificate now reaches `exp(x·y − z·w)`,
`log(…)`, etc. Honest scope: this is ONE local transcendental layer over arithmetic; FULL recursive
local-Lipschitz nesting is harder — the domain condition at each node depends on the accumulated absolute
error (existential), so range and error must propagate together (interval arithmetic with directed
rounding). That coupling is the remaining open piece. `sorryAx`-free.

**FULL local-Lipschitz nesting — via magnitude propagation (`MachLib/AbsoluteFoldNestMag.lean`).** Closes
the coupling above for the symmetric-domain locals. The move: propagate a MAGNITUDE bound `M ≥ |exactRn e|`
(clean — `|a+b| ≤ M_a+M_b`, `|a·b| ≤ M_a·M_b`, no interval sign-cases) alongside the existential error `E`;
the FLOAT-image magnitude is then DERIVED, not tracked (`|toR (evalEML e).toF| ≤ M + E` straight from
`AbsEnc`), so a local `tr1` node over a symmetric domain uses `R = M + E` (both inputs land in `[-R,R]`)
with per-primitive `LipOf t R` / `MagOf t M`. `nested_fold_mag`/`pipeline_nested_mag` carry `∃ E M,
AbsEnc E … ∧ |exactRn e| ≤ M` and reuse `exactRn`/`IsFold` unchanged. `pipeline_nested_exp` is the concrete
`exp` instance (Lipschitz `exp R` on `[-R,R]` from `exp_lip_local`; magnitude `exp M`), so `exp(exp(x·y −
z·w))` — a local primitive nested over itself over cancelling arithmetic — is covered end-to-end at
ARBITRARY depth (example: `exp(exp x)` ∈ the fragment). `log` stays out (one-sided domain). So both the
globally-Lipschitz (`AbsoluteFoldNest`) and the symmetric-local (`exp`/`sinh`/`cosh`) recursive nestings
are now done. `sorryAx`-free.

### Hardened — the unsound open `rolle` axiom is RETIRED; the library has no Rolle but the sound `rolle_ct` (`MachLib/Rolle.lean`)

Grounding MachLib.Real against Mathlib's ℝ surfaced that the old `rolle` axiom was **unsound as stated**: it
asked only for OPEN-interval differentiability (`a < c → c < b`) with **no** endpoint continuity, so it is not a
theorem of ℝ — counterexample `f x = x` on `(0,1)` with `f 0 = f 1 = 0` (differentiable on the open interval,
`f 0 = f 1`, yet `f' ≡ 1 ≠ 0`). This release completes the repair begun with `rolle_ct` (the sound
closed-interval form, witnessed verbatim against Mathlib ℝ by `MonogateEML.RealModel.rolle_witnessed`):

* **Every** consumer migrated to `rolle_ct` / `mean_value_theorem_ct`: the whole Khovanskii footprint
  (pure-exp explicit + unconditional bounds, the mixed exp/log barrier, the `…_le_47` and
  `eml_barrier_bounded_zeros` showcases) plus every utility (Sturm non-oscillation, Wronskian proportional,
  trig / hyperbolic Lipschitz — all differentiate entire functions or on strict subintervals, so closed diff
  is always available).
* The unsound `axiom rolle` **and** the open-hypothesis `theorem mean_value_theorem` (itself proved from
  `rolle`, hence unsound-as-stated) are **DELETED**. `rolle_ct` is now the library's only Rolle. Any future use
  of an open-interval Rolle is a compile error — it no longer exists.
* **Regression gate:** `tools/claim_audit/claim_audit.py` gains `forbid_axioms_exact` (whole-token axiom
  matching — a plain substring forbid can't tell `MachLib.Real.rolle` from the sound `MachLib.Real.rolle_ct`);
  the 8 Khovanskii flagship claims now forbid `MachLib.Real.rolle` exactly. `#print axioms` on all flagships:
  `rolle_ct` only, no bare `rolle`, no `sorryAx`. Claim-audit PASS (16/16), self-test PASS.

### Concrete showcase — `e^(e^x) − x·e^x` has at most 47 real zeros, machine-checked (`MachLib/KhovanskiiConcrete.lean`)

**`MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47`** — a named instance of the explicit Khovanskii
bound. The barrier `y₁ − x·y₀` is, along the depth-2 tower (`y₀ = eˣ`, `y₁ = e^(eˣ)`), exactly
`e^(e^x) − x·e^x`; it is a degree-1 chain-2 polynomial, so its zero count on any interval where it is
somewhere nonzero is `≤ Ndep 0 1`, and `Ndep 0 1` **computes to 47** (`Ndep` is a genuine kernel-reducible
`Nat` recurrence — the `= 47` is discharged by `decide`, not `native_decide`, so no `ofReduceBool` enters the
footprint). Non-vanishing is witnessed at `x = 0`, where the value is `e^(e^0) = e > 0` (`iterExp_pos`). This
turns the "at most 47 real zeros" figure from a hand-evaluated recurrence into a theorem, resting on `rolle`
alone — no `sorryAx`, no `zero_count_bound_classical`, and (being a pure-exp barrier) no analyticity, log, or
reciprocal.

The same file also exercises the **mixed** capstone on a genuinely exp+log function.
**`MachLib.KhovanskiiConcrete.eml_barrier_bounded_zeros`**: `e^x − log x` (the fundamental `eml` operation
applied to `x`) has finitely many zeros on any interval in the positive reals containing `1`, a machine-checked
instance of `eml_eval_boundedZeros_unconditional`. This one is qualitative (a finite ceiling exists) and carries
the honest *mixed* footprint — `rolle` plus the real-analyticity identity theorem
(`analytic_finite_zeros_compact`) and the logarithm — but is still `sorryAx`- and
`zero_count_bound_classical`-free. Together the two showcases pin the honest distinction concretely: the
pure-exp bound is Rolle-only with a literal ceiling; the mixed bound adds the identity theorem and gives
finiteness without an explicit constant.

### exp arm CLOSED — the full mixed exp/log/reciprocal EML barrier bound is unconditional (`MachLib/PfaffianExpHard.lean`)

**`MachLib.eml_eval_boundedZeros_unconditional`** — the Khovanskii-type finiteness bound for arbitrary-depth
**mixed** exp/log/reciprocal EML barriers, machine-checked. Both classical arms are discharged: the exp arm
(`exp_hard`) via the new `expEliminate` construction (B1–B4 in `PfaffianExpEliminate` / `PfaffianExpTrim` /
`PfaffianExpWronskian` / `PfaffianExpHard`), the log arm via `log_hard_proof`. `#print axioms` →
`propext` / `Classical.choice` / `Quot.sound`, the `Real` interface, `rolle`, plus the real-analyticity
package (`analytic_finite_zeros_compact` and the identity-theorem family) and the logarithm / reciprocal
derivative rules — with **no `sorryAx` and no `zero_count_bound_classical`**.

Honest scoping, held to on the public page too: the mixed bound is *qualitative* (a finite ceiling exists,
without an explicit constant), and its analytic footprint is genuinely **larger than Rolle** — the degenerate
"proportional" leaves are retired by the identity theorem (a real-analytic function has finitely many zeros
on a compact interval unless it vanishes identically). Rolle carries the descent; analyticity enters only for
those leaves.

By contrast the pure iterated-exponential bound stays Rolle-only, and is now *effective*.
**`MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit`** gives the explicit ceiling `Ndep m D`; its
`#print axioms` footprint has **no analyticity, no logarithm, no reciprocal** — `rolle` is the sole analytic
input. `Ndep` is now a genuinely computable, `#eval`-able closed-form recurrence (a gratuitous
`noncomputable` on `budgetMax` was removed), though its values are a height-`m` tower of exponentials, so
evaluating beyond a small depth overflows the interpreter.

Both claims are pinned in `tools/claim_audit/claims.json` so the distinction (pure-exp = Rolle-only; mixed =
Rolle + identity theorem, still `sorryAx`- and `zero_count_bound_classical`-free) is a standing CI gate.

### Hardened — analytic base collapses to a single axiom: `zero_count_bound_by_deriv` is now a THEOREM (`MachLib/Rolle.lean`)

**`MachLib.Real.zero_count_bound_by_deriv`** — previously an `axiom`, now **derived from `rolle`**. The whole
iterated-exponential tower's analytic foundation therefore bottoms out at the SINGLE axiom `rolle` (plus the
field/order interface); the separate zero-count axiom is gone. `#print axioms zero_count_bound_by_deriv` →
`propext`, `Classical.choice`, `Quot.sound`, `rolle`, and the `Real` order / `HasDerivAt` primitives — **NO
`sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

Construction (all supporting defs `private` to `Rolle.lean`): sort the `Nodup` zeros of `f` into strictly
increasing order via `List.mergeSort` with a classical `≤`-comparator (`leB`), then `interleave_from` applies
`rolle` between each consecutive pair to produce a zero of `f'` strictly between them. Those bracket points are
themselves strictly increasing (each lands in a disjoint sub-interval, enforced by the `> hd` recursion
invariant), hence `Nodup` and of length `zeros_f.length − 1`; feeding that list to `hf'_bound` gives
`zeros_f.length ≤ N + 1`. Uses Lean 4.14 core `List.mergeSort` / `List.Perm` / `List.Pairwise` (no Mathlib).
All 138 modules rebuild; every downstream consumer (`KhovanskiiReduction`, `SingleExpKhovanskii`,
`InnerKhovanskii`, `PolynomialRootCount`, …) picks up the theorem by name — signature unchanged.

### Added — Khovanskii ∀N: **ARC CLOSED** — the UNCONDITIONAL arbitrary-depth bound (`MachLib/IterExpDepthNBoundUncond.lean`)

**`MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional`** — for **every** depth and every chain-`N`
polynomial not identically zero on `(a,b)`, `chainNFn p` has finitely many zeros. NO hypothesis. `#print axioms`
→ `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` analytic interface (`rolle`, `exp`,
`HasDerivAt` calculus): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`** — the
forbidden-axiom grep is empty. (As of the hardening entry above, `zero_count_bound_by_deriv` is itself a
theorem derived from `rolle`, so it no longer appears in this footprint — `rolle` is now the sole analytic axiom.)

The reduce arm's `Reducing` precondition — previously the explicit hypothesis `hRD` of
`chainN_khovanskii_bound_of_reducing` — is now a **theorem**, `establish_hnz_or_trim` (for any `q ≢ 0`, either
`hnzTower m q` (the deepest true-degree is nonzero, so the absorbed reduce descent `chainNReduce_descends_hnz`
fires) OR an eval-equal `synMeasure`-smaller phantom-trim). The assembly runs on the augmented measure `M5⁺`
(`chainNMeasure5p` = `(chainNMeasureCanon, synMeasure(inner))`), since the eval-invariant `chainNMeasureCanon`
cannot be lowered by an eval-preserving trim — the deep phantom-trim (`liftInner`) ties it and drops `synMeasure`.
Double-, triple-, and arbitrary-depth: all unconditional, all clean.

### Added — Khovanskii ∀N: PHASE C CLOSED — the reduce-descent for every depth (`MachLib/IterExpDepthNDescentInduction.lean`)

**`chainNReduce_descends`** — for a reducing `q : MultiPoly (k+2)` at ANY depth `k`, the reduce with the
full graded multiplier strictly lowers the eval-invariant measure `chainNMeasureEI k` in `nestedOrder (k+2)`.
This is the ∀N analog of the deep depth-2 `chain2MeasureCanonEvalInv_descends`, now proven for **every depth**
by induction. `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
interface (incl. `rolle`): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

The induction, assembled from the whole Phase C stack:
- **`fullMult k q`** — the recursive graded multiplier: depth-2 base at `k=0`; at `k+1`, `gradedTop` +
  `liftLastY` of the lower multiplier for the projected leading coefficient (`dropLastY_liftLastY` recovers
  it — the multiplier-threading resolved).
- **`Reducing k q`** — the recursive reducing predicate (depth-2 conditions at `k=0`; non-phantom + positive
  top degree + `Reducing` of the projected leading coefficient at `k+1`).
- Base = `chainNReduce_evalinv_descent_base` (the transported depth-2 descent, via `chainNReduce 0 =
  chain2Reduce` + `chainNMeasureEI 0 = chain2MeasureCanonEvalInv`); step = the D-step
  `chainNReduce_evalinv_descent` fed the IH through `dropLastY_liftLastY`.

The ∀N reduce-descent — the tower's well-founded step — is complete. Remaining for the full ∀N Khovanskii
bound: Phase D (generalise Rolle/vehicle + the outer WF induction into `chainN_khovanskii_bound_unconditional`).

### Added — `liftLastY`, a right inverse of `dropLastY` (`MachLib/MultiPolyLiftLastY.lean`)

The ∀N descent's D(k)-by-induction wiring needs to thread the graded multiplier down the recursion: the
D-step's inner reduce carries multiplier `dropLastY m_rest`, and for the inductive `D(M)` (a *graded* reduce)
to match, `m_rest` must be the lifted lower multiplier. That requires a `dropLastY` right inverse, which did
not exist — this supplies it.

- **`liftLastY : MultiPoly n → MultiPoly (n+1)`** — embed as a polynomial free of the new top variable
  (structural: `y_i ↦ y_i` at a lower `Fin (n+1)` index; `const`/`varX` kept).
- **`dropLastY_liftLastY`** (`dropLastY (liftLastY x) = x`) and **`degreeY_top_liftLastY`** (`liftLastY x` is
  top-free). Pure structural induction; `#print axioms` clean.

Next: the recursive full graded multiplier (`fullMult`), the recursive reducing predicate, the base
reconciliation (`chainNReduce 0 (gradedTop 0 + const c) p = chain2Reduce c p`, holds since `Ffac 0 = y₀`),
and the `D(k)`-by-induction — then Phase D.

### Added — Khovanskii ∀N Phase C (brick 3b, steps 2a+2b): the S(k) and D(k) descent assembly (`IterExpDepthNDescent.lean`, `IterExpDepthNDescentD.lean`)

The mechanical core of the reduce-descent, both steps, given the inner descent:

- **`chainNReduce_syntactic_descent`** (S(k)) — the *syntactic* measure `(degreeY_top, chainNMeasureEI M of
  dropLastY(leadingCoeffY_top ·))` strictly drops under the depth-`(M+3)` graded reduce, given `hInner`
  (the depth-`(M+2)` reduce lowers the inner measure). Top degree preserved (`chainNReduce_fst_preserved`),
  inner drops via the transport + `hInner`, via `nestedOrder_of_snd`.
- **`chainNReduce_evalinv_descent`** (D(k)) — the *eval-invariant* measure `chainNMeasureEI (M+1)` strictly
  drops, via the phantom / non-phantom split: non-phantom ⇒ both measures = syntactic (brick 2) ⇒ S(k);
  phantom ⇒ `cdegYAt` of the reduce drops below `degreeY_top p` (brick 1) ⇒ first-component descent. The
  literal top index is confined to two `rw [Fin.ext hi]` wrappers; the main proof runs at the abstract index.

Both compile clean (`#print axioms` free of `sorryAx` / classical-citation). This is the ∀N analog of
`chain2MeasureCanonEvalInv_descends`, parameterized on `hInner`. What remains of Phase C: wire the
`D(k)`-by-induction (base `D(0)` = `chain2MeasureCanonEvalInv_descends`; step feeds `D(k)` as `hInner` to
`chainNReduce_evalinv_descent`) — the remaining subtlety is threading the *graded multiplier* + reducing
hypotheses through the recursion so the inductive `D(k)` matches `hInner`'s inner reduce.

### Added — Khovanskii ∀N Phase C (brick 3b, step 1): the inner-descent transport (`MachLib/IterExpDepthNDescent.lean`)

**`chainNMeasureEI_reduce_inner_eq`** — the eval-invariant measure of the depth-`(M+3)` graded reduce's
dropped top coefficient equals the measure of the depth-`(M+2)` reduce of `dropLastY (lcY_top p)`. Immediate
from brick 3a (full-env recursion) + Phase B (`chainNMeasureEI_eq_of_eval_eq`). This is the exact bridge the
syntactic descent `S(k)`'s inner step needs — with it, `S(k)`'s inner descent is `rw [this]; exact D(k−1)`.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction proper (the fst-preserved
outer + this transport + the phantom split + the reducing-hypothesis threading).

### Added — Khovanskii ∀N Phase C (brick 3a): the recursion brick, FULL-ENV (`MachLib/IterExpDepthNRecursionFull.lean`)

`chainNReduce_dropLastY_recursion` closes the depth-`(M+3)`→`(M+2)` recursion **only on the chain values**;
the measure descent needs it on **every** environment (the eval-invariant measure's eval-invariance
quantifies over all envs — exactly why depth-3 needed the separate `chain3Reduce_dropLastY_lcY2_eval_eq_full`).

- **`chainNReduce_dropLastY_recursion_full`** — the ∀N, full-env version: the depth-`(M+3)` graded reduce's
  dropped top coefficient, at *any* environment, equals a depth-`(M+2)` reduce of `dropLastY (lcY_top p)`
  with multiplier `dropLastY m_rest`. Re-derived by replacing the chain-values `dropLastY_eval_IterExp'` with
  the framework `MultiPoly.eval_dropLastY` (env-restriction bridge `extEnv`/`dropLastY_eval_full'`) +
  `dropLastY_cTD_commute`, keeping the abstract-index discipline (top index a variable `i`, `hi : i.val =
  M+2`; `[local irreducible]` on the stuck recursors). Compiled first try. `#print axioms` clean.
- This closes the sub-gap that stood between Phase B and the descent: the descent's inner step
  (`chainNMeasureEI k (dropLastY lcY_top(reduce)) = chainNMeasureEI k (reduce_{k+2} of dropLastY lcY_top)`)
  now has its full-env eval-equality. Remaining Phase C: brick 3b, the S(k)/D(k) mutual induction assembling
  3a + the phantom bridge + `chainNReduce_fst_preserved` + D(k−1).

### Added — Khovanskii ∀N Phase C (brick 2): eval-invariant measure = syntactic on non-phantom (`MachLib/IterExpDepthNMeasureSyn.lean`)

**`chainNMeasureEI_eq_syntactic_of_nonphantom`** — for `q : MultiPoly (j+3)` whose top `y`-coefficient is
non-phantom, the eval-invariant measure `chainNMeasureEI (j+1) q` equals the *syntactic* form `(degreeY_top q,
chainNMeasureEI j (dropLastY (leadingCoeffY_top q)))`. Depth-generic analog of the depth-2
`chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom`; assembled from Phase C brick 1
(`cdegYAt_eq_degreeYAt_of_top`, `canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`) + Phase B
(`chainNMeasureEI_eq_of_eval_eq`, `dropLastY_eval_eq_of_topfree`). This is the swap that lets the
eval-invariant descent `D(k)` fall through to the syntactic descent `S(k)` on the non-phantom branch.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction (S(k) assembles the
reduce machinery around the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase C (brick 1): the phantom / non-phantom bridge (`MachLib/IterExpDepthNCanonBridge.lean`)

The base descent `chain2MeasureCanonEvalInv_descends` works by a **phantom / non-phantom split**: when the
top `y_i`-coefficient is *non-phantom* the canonical measure equals the syntactic one (deep syntactic
descent applies); when *phantom* the canonical degree `cdegYAt` strictly drops (first-component descent
outright). This is the key that turns the canonical-outer descent D(k) into a well-defined induction. This
brick supplies both directions of the split, index/depth-generic (the depth-2 originals were `MultiPoly 2`,
index `⟨1⟩`):

- **`ytopAt i q`** — the syntactic top `y_i`-coefficient (`getLast` of `yCoeffsAt`).
- **`cdegYAt_eq_degreeYAt_of_top` / `canonLcYAt_eq_ytop`** — non-phantom ⇒ canonical = syntactic.
- **`cdegYAt_lt_degreeYAt_of_top`** — phantom (+ positive syntactic degree) ⇒ `cdegYAt` strictly drops.
- **`canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`** — non-phantom ⇒ canonical leading coeff eval-equals
  syntactic `leadingCoeffY` (what the measure-equality consumes next).
- `#print axioms` clean (no `sorryAx`, no classical-citation). Next: the syntactic top-level measure
  `chainNMeasureSyn` + `chainNMeasureEI = chainNMeasureSyn` on the non-phantom branch, then the S(k)/D(k)
  mutual induction (S(k) from the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase B: the uniform eval-invariant measure by recursion on depth (`MachLib/IterExpDepthNMeasureEI.lean`)

The depth-3 descent used the fully eval-invariant depth-2 measure (`chain2MeasureCanonEvalInv`) as its
inner nested component. The tower needs that inner measure at every depth, uniformly — this builds it.

- **`chainNMeasureEI k : MultiPoly (k+2) → NestedNat (k+2)`** — the depth-`(k+2)` eval-invariant canonical
  measure. Base `k=0` is *literally* `chain2MeasureCanonEvalInv` (so every induction bottoms out in the
  existing, already-proven depth-2 machinery — nothing to reconcile); step `k+1` pairs the canonical
  top-degree `cdegYAt` (Phase A) with the measure of the canonical leading coefficient projected one
  variable down via `dropLastY`.
- **`chainNMeasureEI_eq_of_eval_eq`** — the measure is **eval-invariant at every depth**, by induction:
  base `chain2MeasureCanonEvalInv_eq_of_eval_eq`; step combines Phase A's `cdegYAt_eq_of_eval_eq` (outer),
  `canonLcYAt_eval_eq_of_eval_eq` + the new `dropLastY_eval_eq_of_topfree` (the projected coefficient stays
  eval-equal), and the inductive hypothesis (inner).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + honest `MachLib.Real`; **no `sorryAx`**.
- **Next (Phase C, the hard frontier)**: the reduce-descent — that this measure strictly decreases under
  the graded reduce. The algebraic engine is already ∀N (`chainNReduce_dropLastY_recursion`) and the
  eval-invariance just landed transports it; the genuinely-uncertain step is the canonical-outer descent
  `D(k)→D(k+1)`, which generalizes depth-3's reduce/trim/inner-trim case analysis.

### Added — Khovanskii ∀N Phase A: the index-generic canonical `y`-degree + eval-invariance (`MachLib/IterExpDepthNCanonDegree.lean`)

The measure the ∀N descent will use is *eval-invariant* — it forgets phantom leading `y`-terms that only
cancel semantically. Depth-2/3 built that per index (`cdegY0` at `⟨0⟩`, `cdegY1` at `⟨1⟩`, both in
`MultiPoly 2`); the tower needs it at the **top index of any depth**, uniformly. This brick supplies it.

- **`canonZeroB c`** — the one index-specific ingredient (the coefficient canon-zero test) made generic
  by a single **classical** definition: `decide (c vanishes everywhere)`. This makes canon-zero congruent
  under eval-equality by construction, so eval-invariance is nearly free. Every list-level helper reused
  (`rdw_cons`, `dropWhile_all`, `rdw_zero_of_all`, `listSubN`, `yCoeffsAt_entry_eval_zero_of_eval_zero`,
  `eval_eq_of_env_agree_off`) was already index-generic.
- **`cdegYAt i q`** (canonical `y_i`-degree) + **`cdegYAt_eq_of_eval_eq`** — degree eval-invariance ∀
  index, ∀ depth. Generic analog of `cdegY1_eq_of_eval_eq`.
- **`canonLcYAt i q`** (canonical leading `y_i`-coefficient) + **`canonLcYAt_eval_eq_of_eval_eq`** — the
  leading coefficient is eval-invariant at EVERY point (the classical test gives everywhere-agreement
  directly, so — unlike the structural depth-2 `canonLcY1` proof — no `env0` restriction is needed).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` interface;
  **no `sorryAx`**, no classical-citation axiom. Phase B (the uniform eval-invariant measure by recursion
  on depth) plugs `cdegYAt`/`canonLcYAt` in at the top index and recurses via `dropLastY`.

### Added — Khovanskii ∀N: the depth-generic well-founded measure backbone (`MachLib/IterExpDepthNMeasure.lean`)

Next brick of the depth-N tower, on the critical path to the WF capstone. The depth-2/3 capstones each
cite a hand-built well-foundedness keystone for their arity (`natTripleLex_wf`, `natQuadLex_wf`); the ∀N
induction needs that family *uniformly*. This supplies it:

- **`MachLib.IterExpDepthN.NestedNat n`** — the depth-`(n+2)` measure codomain (`(n+1)`-deep nested `Nat`
  product); **`nestedOrder n`** — its nested lexicographic order (definitionally `nestedOrder 2` is the
  depth-2 `nestedLT`); **`nestedOrder_wf n`** — **well-founded for every `n`** by induction on depth
  (base `Nat.lt`, step `lexProd_wf`). `natPairLex/​natTripleLex/​natQuadLex_wf` are its `n = 1,2,3` slices.
- **`nestedOrder_of_fst` / `nestedOrder_of_snd`** — the two generic descent-lifting lemmas the capstone's
  arms need (drop the top component / tie it and drop the tail).
- `#print axioms` → **depends on NO axioms** (pure order theory; not even `propext`). This is the
  well-founded skeleton the ∀N reduce-descent will hang on. The algebraic heart of that descent — "the
  dropped top coefficient of the reduce IS a depth-(N−1) reduce" — is already machine-checked ∀N
  (`chainNReduce_dropLastY_recursion`). Still ahead: the uniform *eval-invariant* measure and its descent
  by induction on depth (base = chain2), then the ∀N Rolle/vehicle step and the capstone assembly.

### Added — verified day-count & accrual: coupon periods compose exactly (`MachLib/FinanceDayCount.lean`)

The second finance kernel — the lane is not a one-off. Same discipline as amortization, aimed at the
property a bond desk and an auditor argue about: **splitting a coupon period at an intermediate date must
preserve accrued interest.** Uses the **30E/360 (Eurobond)** convention, where every date `(y,m,d)` has a
single serial `360·y + 30·m + min(d,30)` and the day-count is the serial difference.

- **`MachLib.Finance.days30E360_additive`** — the headline: `days(A,B) + days(B,C) = days(A,C)` for ANY
  intermediate date. The day-count analogue of amortization's telescoping reconciliation — interest can't
  be manufactured by moving the accrual boundary. **Honest domain point**: this holds for 30E/360 because
  each date has one serial; the US 30/360 "bond basis" is *not* additive (its end-of-month rule depends on
  the other endpoint), so picking 30E/360 is a deliberate correctness decision.
- **`MachLib.Finance.accrual_additive`** — the money corollary: accrued interest (`notional·rateNum·days`)
  composes exactly across a split, because it is linear in an additive day-count.
- **`MachLib.Finance.days30E360_months`** — regularity: same day-of-month, `m` whole months apart ⇒ exactly
  `30·m` days. Equal calendar spacing ⇒ equal day-count ⇒ equal accrual (fair level coupons).
- **`MachLib.Finance.days30E360_full_year`** (`= 360`) and **`days30E360_nonneg`** (forward periods aren't
  negative).
- `#print axioms` (all five) → `propext`, `Quot.sound` ONLY — pure `Int`, not even `Classical.choice`
  (same minimal footprint as `amortization_reconciles`; calendars and money are exact integer objects, no
  float). Registered in `tools/claim_audit`. Runtime witness: `forge/reproduce/sims/daycount_sim.py`.

### Added — verified amortization (the finance-assurance lane opens) (`MachLib/FinanceAmortization.lean`)

- **`MachLib.Finance.amortization_reconciles`** — a fixed-rate amortization schedule in **integer
  cents** reconciles to the penny **exactly**: with per-period principal `b k − b (k+1)`, starting at
  the loan `P` and closing at `b N = 0`, the principal payments sum to exactly `P`. Exact (`=`, not
  `≤ ε`) and **rounding-mode-independent** (the final payment absorbs the accumulated rounding — how
  real schedules are built). `#print axioms` → `propext`, `Quot.sound` only (pure Int; not even the
  axiomatized-Real base — money is decimal fixed-point, and this proof never touches a float).
- **`MachLib.Finance.roundHalfEven_half_ulp`** — round-half-to-even (banker's rounding) is correct to
  within half a cent per period: `−den ≤ 2·(den·round − num) ≤ den`. `#print axioms` → Lean's three
  only, no `sorryAx`.
- **Why this lane**: the finance-translatable core of the project is the fixed-point/decimal-rounding
  + contraction infrastructure (FPModel / FixedPointCertifier / ClosedLoopSafety) — *not* the
  Khovanskii frontier, which is pure symbolic math with no dollar attached. This is the first brick
  pointing that infrastructure at money: the runtime schedule (`forge/reproduce/sims/amortization_sim.py`),
  certified.

### Added — the accumulated rounding error stays inside a certified envelope (`MachLib/FinanceEnvelope.lean`)

Deepens the amortization kernel from *reconciles* + *½¢-per-period* to a **global** bound: how far the
rounded balance trajectory can drift from the exact-arithmetic one over the whole loan. The drift obeys
`e_{k+1} = g·e_k + ρ_k`, `e_0 = 0`, `|ρ_k| ≤ c` (`g = 1+r`, `c = ½` cent) — a linear recurrence with
bounded input.

- **`MachLib.Real.error_within_envelope`** — the abstract core, the **expansion dual** of
  `MachLib.Real.safe_envelope_invariant`: for `g ≥ 1`, `|e_k| ≤ errEnvelope g c k` for all `k`. The
  safety envelope is a *contraction* (`g<1`) settling into a fixed box `X=δ/(1−ρ)`; this is the *growth*
  regime (`g>1`) where the compounded error still lives inside a growing, explicit envelope
  `cap_k = c·(gᵏ−1)/(g−1)`. Same proof shape (triangle + `mul_le_mul_of_nonneg_left` + `add_le_add_both`
  under induction).
- **`MachLib.Real.errEnvelope_eq_geomSum` / `geomSum_closed`** — `cap_N = c·Σ_{j<N} gʲ` and
  `(g−1)·Σ_{j<N} gʲ = gᴺ−1`, i.e. the recognizable `c·(gᴺ−1)/(g−1)`, both proven **without division**.
- **`MachLib.Real.amortization_drift_within_envelope`** — the punchline: the rounded schedule `b`
  (`b_{k+1}=g·b_k−pmt+ρ_k`) never leaves `cap_k` around the exact schedule `B` (`B_{k+1}=g·B_k−pmt`),
  for ANY per-period rounding `|ρ_k| ≤ c`. With `c=½` cent this bounds how far per-period interest
  rounding can push the balance off the exact-arithmetic path — connecting the local ½¢ fact to a global
  guarantee. For the zoo's `$250k @ 6% / 360mo` loan the certified **worst-case** `cap_N ≈ $5.02` (every
  rounding adverse and fully compounding); the **measured** drift is only `~$0.05`, because real
  per-period roundings mostly cancel — the rounded trajectory sits well inside the envelope, exactly as
  the safety envelope's margin works. (That worst-case cap is a separate quantity from the ~$3.66
  final-payment adjustment, which is dominated by rounding the level payment, not the per-period interest.)
- `#print axioms` (all four) → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
  interface ONLY: **no `sorryAx`**, no classical-citation math axiom — same footprint class as the
  safety envelope. **Mechanization note**: `mach_mpoly` reifies its bracket atoms in the *outer*
  elaboration context, so it cannot see an `induction`-introduced local (`geomSum g n`); each ring
  identity is therefore proven once as a top-level lemma over plain variables and `exact`-ed at the use
  site. (`mach_ring` avoided per its known silent-`sorry` failure mode.)

## [Unreleased] — 2026-07-01

### Added — Frontier-1 lemma (1) proven for EVERY depth `N` (`33a819a`)

- **`MachLib.IterExpDepthN.leadingCoeffYtop_cTD_eval_IterExpN`** — the
  top-`leadingCoeffY`-under-`chainTotalDeriv` product-injection identity, now
  proven for **every** depth `N = M+2` (not just the closed depths 2 and 3):
  `eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M · lcY_top p)`,
  top `⟨M+1⟩`, injection factor `Ffac M = y₀·…·y_M`. This is the first genuinely
  general-`N` brick of the depth-N tower and the step the frontier notes called
  "the one genuinely uncertain algebraic step". `#print axioms` → `propext` +
  `Quot.sound` + the honest `MachLib.Real` interface ONLY: **NO `sorryAx`, NO
  `zero_count_bound_classical`, NO `analytic_finite_zeros`** — and not even
  `Classical.choice` (the identity is purely algebraic). Verified by `tools/claim_audit`.
- **Why it was blocked, and the actual fix** (`MachLib/IterExpDepthNTopIdentity.lean`):
  the earlier `∀M` attempt diverged; the cause was **not** `whnf` of `prodVarYUpTo M`
  (marking the factor `irreducible` does not help) but `rw`'s `kabstract` re-`whnf`ing
  the *stuck* `leadingCoeffY`/`degreeY` recursors at the **literal symbolic index**
  `⟨M+1, by omega⟩`. Fix: keep the top index an **abstract variable** `i` with
  `hi : i.val = M+1`, confining the one unavoidable literal to three one-equation
  wrapper lemmas. Worst step: divergent → 0.5 s; whole file 0.8 s. Reusable for the
  rest of the tower.
- **The reduce operator, `∀N`** (`MachLib/IterExpDepthNReduce.lean`, also clean —
  `propext`/`Quot.sound`/`MachLib.Real.*` only): `chainNReduce M m p = cTD p − m·p`, with
  `chainNReduce_fst_preserved` (preserves the top y-degree) and `chainNReduce_lcY_top_eval`
  (its top leading coefficient, evaluated, `= eval(cTD(lcY_top p)) + degreeY_top p·eval(Ffac M)·
  eval(lcY_top p) − eval(m)·eval(lcY_top p)`) — the depth-N → depth-(N-1) recursion seam, for any
  top-free multiplier `m`, driven by lemma (1). When `m`'s top term is `degreeY_top p·Ffac M` the
  injection cancels, leaving a depth-(N-1) reduce of `lcY_top p`.
- **The graded-multiplier cancellation, `∀N`** (`MachLib/IterExpDepthNGraded.lean`, clean —
  `sorryAx`-free, no classical-citation axiom): `chainNReduce_graded_cancels` — with the top graded
  term `gradedTop = (degreeY_top p)·Ffac M`, lemma (1)'s injection cancels *exactly* and the reduce's
  top coefficient collapses to `eval(cTD(lcY_top p)) − eval(m_rest)·eval(lcY_top p)` — an honest
  reduce of `lcY_top p` by the remainder `m_rest`, for ANY top-free `m_rest`. This is the depth-`N` →
  depth-`(N-1)` step (the recursion's heart), the generic-`N` analog of chain-2's
  `chain2Reduce_lcY1_eval` and depth-3's `chain3Reduce_lcY2_eval`. The specific nested-degree
  `m_rest` plugs in later without redoing the cancellation.
- **The `dropLastY` bridge, `∀N`** (`MachLib/IterExpDepthNBridge.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): the ∀M analog of `IterExpDepth3Bridge`, so the depth-`(M+2)` reduce's
  dropped top coefficient can be read as a depth-`(M+1)` object and fed to the induction hypothesis.
  `chainValues_restrict_eq` (the `(M+2)`-chain restricted to `M+1` slots IS the `(M+1)`-chain),
  `dropLastY_eval_IterExp` (top-free `q`: `eval q [IExp(M+2)] = eval (dropLastY q) [IExp(M+1)]`),
  `dropLastY_prodVarYUpTo` (the relation polys `y₀·…·y_{k-1}` match under the drop), and
  `dropLastY_cTD_commute` (top-free `q`: `dropLastY (cTD_{M+2} q) = cTD_{M+1} (dropLastY q)`).
- **The recursion closes, `∀N`** (`MachLib/IterExpDepthNRecursion.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): `chainNReduce_dropLastY_recursion` — the depth-`(M+3)` graded reduce's
  dropped top coefficient, evaluated one chain down, **IS a depth-`(M+2)` reduce** of
  `dropLastY (lcY_top p)`, with multiplier just `dropLastY (m_rest)`. So the recursion is carried by
  `dropLastY`; no separate closed-form nested multiplier is needed. Assembled term-mode from bricks
  3+4 + `degreeYtop_cTD_eq'`. The generic-`N` analog of depth-3's `chain3Reduce_dropLastY_lcY2_eval_eq`,
  and the depth-induction's actual step. **Mechanization note**: the top index MUST be an abstract
  variable (`i` with `hi : i.val = M+2`), not the literal `⟨M+2,…⟩` — the literal makes `whnf` diverge
  on the stuck recursors at a symbolic index (rw / conv / term-mode / irreducible all diverge); two
  one-line wrappers confine the literal. This is the lemma-(1) fix, one level deeper.

### Added — depth-3 (triple-exponential) Khovanskii bound, unconditional and dirty-axiom-free (`ab77c5b`)

- **`MachLib.IterExpDepth3Bound.chain3_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-3 triple-exponential** Pfaffian chain
  (`y₀ = eˣ, y₁ = e^{eˣ}, y₂ = e^{e^{eˣ}}`), **proven, not cited**. For a chain-3
  polynomial nonzero at *some* interior point of `(a,b)`, the number of zeros on
  `(a,b)` is finitely bounded — NO `terminal_nonzero` hypothesis. `#print axioms`
  → only the honest `MachLib.Real` interface (`rolle`, `zero_count_bound_by_deriv`,
  the ring/order/field axioms, `natCast`) plus Lean's `propext`/`Classical.choice`/
  `Quot.sound`: **NO `sorryAx`, NO `zero_count_bound_classical`, NO
  `analytic_finite_zeros`**. Verified by `tools/claim_audit`.
- **How the climb works** (the `IterExpDepth3*` files): `WellFounded.induction` on
  an augmented measure `chain3Order5` (`(chain3MeasureCanon, degreeY₁ q)`), four
  arms — base (`degreeY₂ = 0` → the depth-2 bound above) / `degreeY₂`-trim /
  inner-trim (drop the phantom leading `y₁`-term of `lcY₂ p`; the crux — its own
  `reconstructY`/`leadingCoeffY` toolkit) / reduce (graded multiplier, then the
  integrating-factor vehicle for `reduct ≡ 0` or Rolle `+1`). The depth-2/single-exp
  frameworks are untouched.
- **Meaning + honest scope.** Frontier 1 (the depth-N iterated-exponential tower) is
  closed at **depth 3** — the depth-2 closure provably extends one level up by depth
  induction, entirely from honest Rolle. This does **not** discharge the
  arbitrary-depth axiom: `PfaffianFunction.zero_bound` still cites
  `zero_count_bound_classical` for general depth; only depths 1–3 are counted, not
  quoted.

### Added — depth-2 Khovanskii bound, unconditional and dirty-axiom-free (`dda2a58`)

- **`MachLib.ChainExp2NoZeros.chain2_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-2 double-exponential** Pfaffian chain
  (`x, eˣ, e^{eˣ}`), **proven, not cited**. For a chain-2 polynomial nonzero at
  *some* interior point of `(a,b)`, the number of zeros on `(a,b)` is finitely
  bounded. `#print axioms` → `propext, Classical.choice, Quot.sound`, the `Real`
  base, and the honest Rolle corollary `zero_count_bound_by_deriv`; **no
  `zero_count_bound_classical`, no `sorryAx`**. This is the first depth beyond the
  single-exponential case where the reducibility witness is *constructed* rather than
  supplied/assumed.
- **How the witness is built** (the `ChainExp2*` files): a *chain-aware nested
  descent measure* (`chain2MeasureCanon`, canonical y₀-degree so the reduce cannot
  inflate it), a *polynomial-multiplier Rolle transfer*
  (`zero_count_polyMultReduce_transfer`, the reduce `P' − ((degreeY₁ P)·y₀ + c)·P`),
  and — for the terminal `reduct ≡ 0` case that pure exponentials hit — an
  *integrating-factor vehicle argument*: `V = f·exp(−(d·eˣ+c·x))` has `V' = E·(reduct)`,
  so `reduct ≡ 0 ⇒ V` constant (MVT) ⇒ `f` nonzero everywhere once nonzero at one point.
  The single-exponential framework (`SingleExpKhovanskii`, `KhovanskiiReduction`) is
  untouched.
- **Honest scope.** This does **not** discharge the arbitrary-depth axiom. The legacy
  `zero_count_bound_classical` (Khovanskii 1991) still stands for the general
  `PfaffianFunction` bound; depth-3+ would mirror the depth-2 arc with a deeper nested
  measure. Tier summary now reads: *single-exp proven, depth-2 proven, arbitrary-depth
  cited.* See [`what_is_proven.md` §7](foundations/docs/what_is_proven.md).

## [Unreleased] — 2026-06-26

### Added — `MachLib.FPModel`: verified f64 forward-error (cross-target equivalence, leg 2)

- **`MachLib.FPModel`** — the first proof (not regression test) relating a
  kernel's IEEE-754 `f64` evaluation to its exact `Real` semantics. Adopts the
  standard model of FP arithmetic (Higham §2.2) as three Mathlib-free axioms
  (`u`, `0 ≤ u`, `u ≤ 1`; `u = 2⁻⁵³` for binary64). `length_sq2_fwd_error` and
  `length_sq3_fwd_error` (the `vec3_length_sq` kernel) prove the `f64` result is
  within the tight relative bound `(1+u)ⁿ − 1 ≈ n·u` of the exact value, for
  *every* rounding. `#print axioms` → only `propext` + the `Real` base + the 3
  `u` axioms; no `sorryAx`. EML's straight-line scalar restriction is what makes
  this a closed-form bound rather than a CompCert-scale semantics theorem.
  Full write-up: [`docs/cross_target_equivalence_2026_06_26.md`](foundations/docs/cross_target_equivalence_2026_06_26.md).
- **Conditioned bounds + precision-generic model** (same module): `RoundsW w`
  parameterizes the standard model over the precision's unit roundoff (f64 2⁻⁵³,
  f32 2⁻²⁴, bf16 2⁻⁸) — one theorem, every target, and *no* `u` axiom (rests
  only on `propext` + the `Real` base). `dot2_fwd_error` handles the mixed-sign /
  cancellation-prone case `length_sq` avoids: `|fl(a·b+c·d) − exact| ≤
  ((1+w)²−1)·(|a·b|+|c·d|)` — absolute error against the conditioning quantity,
  the honest statement when the result can cancel to ≈0. Helpers `roundsW_abs`,
  `abs_le_one_add`, `mul_one_add_sub`.

## [Unreleased] — 2026-06-25

### Added — ring-v3, the decompose-first toolkit, and a close-rate harness

- **`MachLib.MPolyRing` (ring-v3)** + the `mach_mpoly` tactic: a nested multivariate
  polynomial normal form. Reify once, normalise once, compare once — polynomial in
  the monomial count, not exponential in the variable count. Closes identities the
  recursive multivariate tactic could not: the 8-variable Euler four-square
  (quaternion-norm) identity goes from *not finishing in 50 minutes* to *seconds*,
  `sorryAx`-free.
- **`MachLib.Decompose`** — four reusable "decompose before nlinarith" lemmas
  (`abs_le_sqrt`, `mul_mem_symm_band`, `lerp_le_of_le`, `quad_denom_pos`) + the
  `mach_decompose` tactic, safe-by-construction (apply/exact + assumption; fails
  cleanly, never silent-`sorry`).
- **`foundations/scripts/closerate.sh`** — a reproducible close-rate harness for the
  Forge `@verify(lean)` corpus. Compiles each emitted obligation independently
  (recursively over all sub-corpora) and counts which `mach_positivity | rfl | sorry`
  cascades genuinely close vs fall through. Current figure: **387 / 581 = 66.6%**
  auto-close, 251 files, 0 build errors (up from 364 / 582 = 62.5%: a 2026-06-26
  refresh brought 16 Discovered obligations up to current `eml-compile`
  emission — the committed copies were stale bare-`sorry` output predating the
  `first | mach_positivity | rfl | sorry` cascade; +23 close, −1 theorem from a
  shadow_pcf re-emit). (The textual `sorry` fallback is in every
  emitted proof, so file-grep is NOT the close-rate — only compilation is.)

Full write-up: [`docs/verification_automation_2026_06_25.md`](docs/verification_automation_2026_06_25.md).

## [Unreleased] — 2026-06-14

### Calibration note — interim audit figures over-counted

In-flight prose around the Khovanskii closure on 2026-06-14 quoted an
audit summary of "210 Forge `@verify` obligations proven-in-place,
80%/19% gap-vs-discharged" and a related sorry count of "269 discovered
sorries (up from 222)". Both figures came from a local working tree
that contained, alongside the publicly-tracked files, ~62 ungated
Discovered/ stubs auto-emitted by the local `auto_prove.py` workflow
(blanket-ignored under `foundations/MachLib/Discovered/.gitignore`),
plus 32 duplicate `.eml` files in a forge `build/` artifact directory.
Neither was visible to a fresh public clone.

The CI-emitted `status.json` (`.github/workflows/status.yml`, lands on
the `status-data` branch on every master push) reports the
public-verifiable figures: 1088 `@verify` obligations total, 36
proven-in-place, 225 placeholder, 823 open, gap_pct 96.3%,
discharged_pct 3.7%, 198 discovered sorries. Those are the numbers a
stranger running `lake build` at the recorded SHA can reproduce.

The 4 strengthened Forge contracts shipped this cycle (Butler-Volmer,
plasma concentration, defibrillator discharge, critically-damped spring)
are publicly tracked and verified, and counted in both the local and
public audits. The over-count was concentrated in `proven_in_place`
(stubs the Forge backend auto-emitted with concrete-enough bodies that
the audit's heuristic classifier didn't flag them).

Follow-up: `forge_verify_audit.py` now defaults to `git ls-files`-aware
file enumeration so a local audit gives the same number as CI. The
`--include-untracked` flag preserves the full local view for callers
who want it. Until the 62 ungated stubs are reviewed and pushed, the
CI figure is the right one to quote.

### Added

- `MachLib.Applications.PlasmaConcentrationNonneg` — pharma kernel
  proof. Bi-exponential IV-bolus central-compartment concentration is
  non-negative under the Forge kernel preconditions. Domain: TCI
  anaesthesia pumps, ICU monitors. Safety class: IEC 62304 Class C, FDA
  510(k). Also closed the `sorry` for `plasma_concentration_nonneg`
  inline in `MachLib/Discovered/pk_two_compartment.lean`.
- `MachLib.Applications.DischargeVoltageSafety` — defibrillator kernel
  proof. Strengthens the Forge `True := by trivial` placeholder for
  `discharge_voltage_decays_exponentially` to sign preservation under
  non-negative initial voltage (no polarity inversion mid-phase). IEC
  62304 Class C. Pointer comment added to the Discovered stub.
- `MachLib.Applications.SpringCriticallyDamped` — game-animation kernel
  proof. Khovanskii-localised positivity of the critically-damped
  harmonic spring `A · (1 + ω·t) · exp(-ω·t)`. ExpPoly length 1, total
  degree 2; the lone zero at `t = -1/ω` is excluded by the animation
  window `t ≥ 0`. Sign-preserving + strictly-positive variants ship;
  the underdamped (cos-bearing) branch remains open pending
  trig-Khovanskii. From `eml-stdlib/gaming/animation/spring.eml`'s
  `spring_critical_signed` obligation.
- `MachLib.SingleExpKhovanskii` — constructive Khovanskii zero bound for
  polynomial-in-(x, eˣ), three resolution paths:
  - `expPoly_khovanskii_bound` (parametric capstone; user supplies an
    `IsKhovanskiiReducibleExp` witness).
  - `expPoly_auto_bound_with_propagation_aux` (strong-induction auto-bound
    over `length + Σ degreeUpper(polySimplify coeffs)`, parametric in a
    propagation hypothesis).
  - `expPoly_ode_no_zeros` (MVT-based ODE corner case: when
    `f' - c·f ≡ 0` on `(a, b)`, `f` is zero-free).
- `MachLib.KhovanskiiReduction` — `khovanskii_bound_full` for general
  triangular Pfaffian chains, parametric in a reduction witness
  (`IsKhovanskiiReducible` with `reduce` + `drop` constructors).
- `MachLib.MultiPolyToPoly` — `MultiPoly 0 → Poly` conversion + the
  chainLength-0 base-case zero bound.
- `MachLib.Applications.ButlerVolmerKhovanskii` — Forge kernel proof for
  the Butler-Volmer electrode-kinetics safety contract: current = 0 iff
  overpotential = 0. Strengthens the `True := by trivial` placeholder
  in `MachLib/Discovered/butler_volmer.lean` (pointer comment added).
  Domain: BMS, fuel cell controllers, corrosion engineering.
- `foundations/AxiomAudit.lean` — reproducible `#print axioms` over the
  headline theorems, run via `lake env lean AxiomAudit.lean`.
- `foundations/KhovanskiiExamples.lean` — three worked applications.

### Foundations note

Results are proven **modulo MachLib's axiomatized analytic base**: a Rolle
zero-counting corollary (`zero_count_bound_by_deriv`), the `HasDerivAt`
rules + `HasDerivAt_unique`, `exp_pos` / `exp_zero`, and `MachLib.Real`
arithmetic / order. In mathlib every one of these is a theorem, not an
axiom — grounding the base in mathlib is open work, not done here.

`zero_count_bound_by_deriv` does the core analytic work; the Khovanskii
layer added in this release is the reduction and the explicit-bound
bookkeeping on top of it. The audit (`AxiomAudit.lean`) makes the
dependency set fully visible.

The release added no assumptions beyond that documented base.

### Notes

- The textbook Khovanskii operator `f' - c·y_n'·f` does not drop degree
  in single-exp chains. The operator that works is `scaledReduction c f :=
  f' - c·f` (see the git history around the `4fe434a` commit for the
  discovery).
- `expPoly_ode_no_zeros` does not invoke `Classical.choice` in its Lean
  dependency closure. This is **not** a constructive-analysis claim — the
  MVT it rests on is classical in spirit and only escapes the dependency
  list because the MVT itself is axiomatized in MachLib.
- 3 `sorry`-warnings exist in 2 non-headline modules (`MachLib.ForgeTest`
  and `MachLib.HighDimensional`, work-in-progress queues unrelated to this
  release). Transitive-import closure of the headline theorems and the
  audit (25 modules) confirms neither is in the dependency chain.

### Verification

- `lake build` of the foundations target is green.
- Headline files have zero `sorry`.
- `lake env lean foundations/AxiomAudit.lean` reproduces the per-theorem
  axiom listing.

### Attribution

Formalization developed by an AI agent (Claude Code) driving MachLib
commits. Coordination on behalf of the Monogate research team.
