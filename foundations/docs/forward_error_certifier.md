# The forward-error certifier — one fold over the operator basis

A reader's front door to MachLib's **forward-error certifier**: a single proof that
bounds the floating-point forward error of *any* kernel built from the operator basis
`{leaf, +, ×, neg, abs, exp, sin, cos, tanh, sinh, cosh, atan, ÷, clamp, sqrt, ln, pow, if}`, and is bound to the real kernels Forge compiles.

Everything below is `sorryAx`-free; **0 custom axioms** beyond MachLib's existing base,
*except* `atan` (§3), which declares the `atan` primitive + its derivative — 3 axioms in
the same category as the `HasDerivAt_sin`/`cos` axioms. "`sorryAx`-free" means no `sorry`/`admit` — every step is a real proof.

---

## 1. What this is

EML's ~450 numeric kernels reduce to a small operator basis (the irreducible analytic
core is `{exp, ln, sin, cos}` — the Liouville generators — plus arithmetic and
division). The certifier proves, **once**, that the rounding error of evaluating any
expression over that basis is bounded by a quantity read off the expression's shape.
It is not a verified compiler and not a Mathlib replacement; it is a self-contained,
checkable forward-error guarantee for the kernels Forge emits.

The bound is a **magnitude+error certificate** `AErr M E v ve`: the exact value has
magnitude `|ve| ≤ M`, and the computed value is within `|v − ve| ≤ E`. Each operator
has a proven `AErr` propagation rule; one structural induction folds them.

## 2. Start here: the one result

**`MachLib.OperatorBasisComplete.gexpr_sound`** — for any per-node-rounded evaluation
of any `Valid` expression `t` over the full operator basis,

```
gexpr_sound : GRoundedEval w t v → t.Valid → AErr t.Mbound (t.Ebound w) v t.exact
gexpr_fwd_error :                              |v − t.exact| ≤ t.Ebound w
```

One fold, every kernel of the basis. `Valid` is trivially `True` away from division;
at a `÷` node it carries the denominator lower bound (`0 < m ≤ denom.exact`) — the one
data-dependent obligation division alone needs (`1/y` is unbounded near 0).

## 3. The per-operator rules it folds (the substance)

| operator | rule | error character |
|---|---|---|
| `+` | `aerr_add` | `Ex + Ey` + sum rounding |
| `×` | `aerr_mul` | bilinear `(|vx|Ey + |ye|Ex)` + product rounding |
| `neg` | `aerr_neg` | exact (`fl(−x) = −x`) |
| `abs` | `aerr_abs` | **exact + 1-Lipschitz** — preserves both magnitude `M` and error `E` |
| `exp`, `sinh`, `cosh` | `aerr_exp/sinh/cosh` | **amplifying** — magnitude `exp/sinh/cosh M`, error scaled by the growth at `M+E` (MVT-derived) |
| `sin`, `cos`, `tanh` | `aerr_sin/cos/tanh` | **bounded-Lipschitz** — `E + w`, magnitude `1` (`tanh`'s Lipschitz derived via MVT) |
| `÷` | `aerr_div` | rounding + propagation, every term scaled by `1/m` |
| `clamp` | `aerr_clamp` | **exact + 1-Lipschitz** — error *preserved* (`E`, no rounding), magnitude `max\|lo\|\|hi\|` |
| `atan` | `aerr_atan` | **1-Lipschitz, magnitude-preserving** (`\|atan x\| ≤ \|x\|`); 3 axioms (the `atan` primitive + its derivative, like `HasDerivAt_sin`) |
| `sqrt` | `aerr_sqrt` | **guarded** (`m ≤ arg`) — `1/(2√m)`-Lipschitz, magnitude `√M` |
| `ln` | `aerr_ln` | **guarded** (`m ≤ arg`) — `1/m`-Lipschitz, magnitude `max(\|ln m\|,\|ln M\|)` |
| `pow` | `aerr_pow` | native `x^y` (guarded base, `y ≥ 0`) — `rpow := exp(y·log x)`, amplifying via `exp_grow` |
| `if` | `aerr_ite` | **branch-robust conditional** — error `max(E_then, E_else)`, magnitude `max(M_then, M_else)`; the selected branch carries, no amplification. Sound when rounding does not flip the test (`if/else-if/else` → nested `iteO`) |

`exp` *amplifies* (absolute argument error → relative output factor); `sin`/`cos` stay
bounded (1-Lipschitz, `|f| ≤ 1`); `÷` needs the denominator bound. The same three
classes the literature names — each proved here, then folded.

These build incrementally and each is its own theorem:
- `OperatorBasisSound.renc_sound` — the tight *relative* `(1+w)^d` fold for nonneg `{+,×}`.
- `OperatorBasisTrans.texpr_sound` — the bounded-Lipschitz transcendentals (`sin`/`cos`/`e^{−S}`).
- `OperatorBasisGeneral.aexpr_sound` — every operator freely mixed (no division).
- `OperatorBasisComplete.gexpr_sound` — adds division: the complete fold.

The relative (`renc_sound`) and general (`aexpr_sound`) folds remain as the
sharper/simpler results where they apply; `gexpr_sound` is the one that covers everything.

## 4. It reaches across precisions and over iterations

- **Cross-target** (`gexpr_cross_target`): the same kernel at two unit-roundoffs `w₁, w₂`
  (an `f32` shader lane, an `f64` software lane) agrees to within `Ebound w₁ + Ebound w₂`
  — both enclose the single exact value. One proof for every kernel, division included.
- **Trajectory** (`TrajectoryCertified.iterated_kernel_trajectory`): a kernel iterated by
  an `L`-contraction has whole-run error `≤ ε·geom L n ≤ ε/(1−L)`, where `ε` is the
  certifier's per-evaluation `Ebound` made orbit-uniform. The per-evaluation guarantee
  lifts to the whole loop (controllers, filters, solvers).
- **Vectors / n-ary reductions** (`VectorError.aerr_sum`): the universal shapes — `Σ xᵢ`,
  dot product `Σ xᵢ·yᵢ`, squared norm `Σ xᵢ²` — are *variable-length* reductions, not one
  tree. `aerr_sum` certifies the accumulator loop `s := 0; for xᵢ: s := fl(s + xᵢ)` over
  any vector of certified components, one list induction folding `aerr_add`. And
  `VectorError.sum_const` turns the parametric error *shape* into an **explicit constant**:
  for exact inputs the n-fold sum's error is `≤ ((1+w)ⁿ − 1)·Σ|xᵢ|` — the classic
  summation bound `≈ n·u·Σ|xᵢ|`, closed-form in `n`. (`sum3_const_certified`,
  `dot2_certified` machine-check concrete instances.)

## 5. It is bound to real kernels (`tree_hash`)

A bound on a `GExpr` only certifies a *shipped kernel* if that `GExpr` is the expression
the kernel compiles. Forge computes a per-function `tree_hash` — a SHA-256 of the
canonical AST, target-independent, "tamper-evident against any meaningful math change."

`tools/machlib_bind/bind.py` (Forge repo) translates a kernel's canonical AST body into
the corresponding `GExpr` Lean term and records its `tree_hash`. The `GExpr` is the same
expression *by translation*; the `tree_hash` is what a drift gate watches (the same pin
the engine's binding-integrity gate uses). `MachLib.ForgeBindingDemo` certifies binder
output verbatim — `length_sq2` (`x²+y²`) and `sigmoid` (`1/(1+e^{−x})`, a division
kernel) — closing the AST → `GExpr` → bound chain, machine-checked.

**The binding is drift-gated, not a one-time snapshot.** `tools/machlib_bind/check.py`
re-runs the binder over the whole corpus and compares each certified kernel's `tree_hash`
to a committed baseline manifest, failing CI on **drift** (a certified kernel's expression
changed → re-verify), **regression** (a certified kernel fell off-basis), or a **coverage
drop**. The gate is proven to go red on an injected change (a one-line edit to a real
kernel's body flips it to a `DRIFT` failure naming the kernel and the old→new hash) — so a
kernel cannot silently diverge from the bound that certifies it.

The binder also **inlines immutable `let`-bindings** — substituting a `let`'s definition
at each use yields a single `GExpr`. Inlining duplicates a shared subtree, so the
certifier over-counts that subterm's rounding (the real kernel rounds it once): a *sound*
conservative upper bound, never an under-estimate. `forge_quad_inlined_let_certified`
machine-checks the sharing case (`let s = x+y; s*s`, both copies of `s` round to the
same value via one shared `RoundsW`). Loops/mutation (`let_mut`/`while`) stay off-basis.

**Measured reach** (the binder over the real eml-stdlib, not a heuristic): **456/517
functions (88.2%) are in the certified operator basis**, 199 of them guarded. The binder
**inlines user-function calls** (incl. `::`-qualified cross-module ones — same sound
inlining as `let`) and translates `if/else-if/else` expressions to nested `iteO` (11
piecewise kernels — easing curves, distance attenuation, IK reachability, AABB overlap —
now certified under branch-robustness). The off-basis remainder is named by exact count —
`floor` (×31, discontinuous — no Lipschitz bound), unresolved `call` (×10, into
`floor`/`tuple` kernels), `tuple` (×5, multi-return), `tan` (×5, guarded near `cos=0`),
`acos`/`asin` (×3, amplify near `±1`) — and a parser gap (×7, complex-number/matrix
kernels: quantum gates, DFT/FFT, simplex/voronoi noise). These remaining classes are
*structural* (discontinuity, non-scalar shape), not missing operators — `floor`/`tuple`/
complex cannot be a Lipschitz scalar tree.

## 6. Why *these* operators — the boundary is a theorem

The 88.2% is empirical; the *reason* the other ~12% are excluded is not. `OperatorAdmissibility`
makes the boundary a theorem. An operator is certifiable only if it is **Lipschitz** — a
bounded input error `E` must yield an output error `≤ L·E` that vanishes as `E → 0` (the `L`
*is* the local condition number). That is the abstract property the per-operator rules
deliver, named `ForwardBoundable`, with both directions proved:

- **Sufficiency** — the certified operators are instances: `fb_abs`, `fb_clamp`, `fb_sin`,
  `fb_cos`, `fb_tanh`, `fb_atan` (all 1-Lipschitz), and `fb_propagate` is the
  error-propagation consequence the fold threads through each node.
- **Necessity** — `heaviside_not_forwardBoundable`: the unit step (the local shape of `floor`
  at an integer) admits **no** Lipschitz constant. A unit jump over an interval of width
  `1/(L+1)` forces `1 ≤ L/(L+1) < 1` — a contradiction for every finite `L`. So `floor`
  isn't an unimplemented operator; it is *provably* uncertifiable in this framework.
- **The guard is necessary** — `recip_no_magnitude_bound`: unguarded `1/x` has no magnitude
  bound near `0` (for any `M` a positive `x` gives `M·x < 1`, i.e. `M < 1/x`). That is the
  structural reason `÷`/`√`/`ln`/`pow` carry a denominator guard `m ≤ |denom|`.
- **Airtight, including the amplifying operators** — global Lipschitz misses `exp`/`sinh`/`cosh`
  (their slope is unbounded), so the honest notion is `LocallyBoundable`: a finite local
  condition number on every bounded range `[−R, R]`. Under it the certified basis is captured
  *in full* — `lb_exp` (constant `exp R`), `lb_sinh`, `lb_cosh`, and the 1-Lipschitz ops as a
  special case — while `floor` still fails (`heaviside_not_locallyBoundable`: the jump lives
  in every range).

So "why these operators" has a precise, two-sided answer: **admissible ⇔ finite local
condition number**; the guards are exactly the poles where that number is infinite; the
discontinuities (`floor`) are excluded outright. The exclusions are a characterization, not a
to-do list.

## 7. What this does NOT claim

- Not a verified compiler — it certifies the *expression*, and binds it to the shipped
  kernel via `tree_hash`; it does not prove the backend lowering is correct.
- Not coverage of the whole stdlib — `tan`, `asin`/`acos` (amplify near `±1`), `floor`
  (discontinuous), `tuple`/complex (non-scalar), and loop/mutation kernels are off-basis
  (§5), named by exact count, not silently included. (`atan`, `sinh`, `cosh`, `tanh` *are*
  covered.)
- Conditionals are certified under **branch-robustness** — the bound holds when rounding
  does not flip which side of the test is taken; a kernel that straddles a threshold
  boundary is outside the guarantee (and a non-robust conditional is off-basis).
- The bounds are parametric in data-dependent inputs (condition numbers, denominator
  guards) supplied per call — the fold proves the *shape* is sound, not per-kernel constants.
- The relative-vs-absolute trade is real: `gexpr_sound` (absolute, magnitude-based) is
  more general but looser on pure arithmetic than `renc_sound`'s tight relative `(1+w)^d`.

**Measured tightness.** Instantiated at the per-op-class f64 budget — `u = 2⁻⁵³` for the
correctly-rounded ops (`+ × ÷ √` and constant representation), `2u` for the libm elementary
functions — the bound is **a median 8× the observed f64 error** across 349 stdlib kernels
(p10 3×, p90 124×; 89% within 100×). So the bounds are *useful*, not merely true. Two
honest caveats the measurement surfaced: (1) you must instantiate `w = 2u` for the libm
transcendentals (they're ~1 ulp, not correctly-rounded) or the bound undershoots — pure
arithmetic stays sound at `u`; (2) the exp/amplifying family (gaussian, softmax, …) is
sound but *loose* (10³⁺×) because the `exp(Mbound)` magnitude envelope is pessimistic — a
relative bound for that family is the natural tightening. Probe: `tools/machlib_bind/tightness.py`.

## 8. Check it yourself

```bash
# Build the whole certifier (part of the MachLib aggregate):
lake build MachLib

# Confirm a result is sorryAx-free + rests only on the documented axiom base:
lake env lean -e '#print axioms MachLib.Real.gexpr_sound'

# Measure the binder's reach over the real stdlib (needs the Forge repo):
PYTHONPATH=<forge> python3 tools/machlib_bind/bind.py --dir <eml-stdlib>

# Run the drift gate — fails if any certified kernel's tree_hash changed:
PYTHONPATH=<forge> python3 tools/machlib_bind/check.py --dir <eml-stdlib>
```

The certifier spans `OperatorBasisSound` / `OperatorBasisTrans` / `OperatorBasisGeneral`
/ `DivisionError` / `OperatorBasisComplete` / `TrajectoryCertified` / `ForgeBindingDemo`.

## 9. Status

Consolidated. 17-operator basis (arithmetic + `abs`/`clamp`, the transcendentals
`exp`/`sin`/`cos`/`tanh`/`sinh`/`cosh`/`atan`, guarded `÷`/`sqrt`/`ln`/`pow`, and `if`),
spanning straight-line **and** control-flow kernels, plus **n-ary reductions** (`Σ`, dot
product, norm) with an explicit `((1+w)ⁿ−1)` constant — so the basis now covers scalar
trees, branches, *and* variable-length vectors. Reaching **456/517** of the real
eml-stdlib, agreeing across precisions and over iterations, bound to `tree_hash`, and
**drift-gated** (a kernel cannot silently diverge from the bound that certifies it). All
`sorryAx`-free; 3 axioms (the `atan` primitive). The remaining scalar off-basis is
structural (discontinuity), not missing operators.
Each file's header states what it adds; this front door is the map.
