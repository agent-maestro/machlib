# The forward-error certifier — one fold over the operator basis

A reader's front door to MachLib's **forward-error certifier**: a single proof that
bounds the floating-point forward error of *any* kernel built from the operator basis
`{leaf, +, ×, neg, abs, exp, sin, cos, ÷, clamp, sqrt, ln, pow}`, and is bound to the real kernels Forge compiles.

Everything below is `sorryAx`-free with **0 custom axioms added** beyond MachLib's
existing base. "`sorryAx`-free" means no `sorry`/`admit` — every step is a real proof.

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
| `exp` | `aerr_exp` | **amplifying** — `exp(M)`·(condition number); reuses `exp_grow` |
| `sin`, `cos` | `aerr_sin/cos` | **bounded-Lipschitz** — `E + w`, magnitude `1` |
| `÷` | `aerr_div` | rounding + propagation, every term scaled by `1/m` |
| `clamp` | `aerr_clamp` | **exact + 1-Lipschitz** — error *preserved* (`E`, no rounding), magnitude `max\|lo\|\|hi\|` |
| `sqrt` | `aerr_sqrt` | **guarded** (`m ≤ arg`) — `1/(2√m)`-Lipschitz, magnitude `√M` |
| `ln` | `aerr_ln` | **guarded** (`m ≤ arg`) — `1/m`-Lipschitz, magnitude `max(\|ln m\|,\|ln M\|)` |
| `pow` | `aerr_pow` | native `x^y` (guarded base, `y ≥ 0`) — `rpow := exp(y·log x)`, amplifying via `exp_grow` |

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

The binder also **inlines immutable `let`-bindings** — substituting a `let`'s definition
at each use yields a single `GExpr`. Inlining duplicates a shared subtree, so the
certifier over-counts that subterm's rounding (the real kernel rounds it once): a *sound*
conservative upper bound, never an under-estimate. `forge_quad_inlined_let_certified`
machine-checks the sharing case (`let s = x+y; s*s`, both copies of `s` round to the
same value via one shared `RoundsW`). Loops/mutation (`let_mut`/`while`) stay off-basis.

**Measured reach** (the binder over the real eml-stdlib, not a heuristic): **410/483
functions (84.9%) are in the certified operator basis**, 173 of them guarded (`÷`, `sqrt`,
`ln`, or `pow`). The off-basis remainder is named by exact count — `call` (×10, user-fn
inlining), `tan`/`atan`/`asin` (×13), `floor` (×6), hyperbolic `sinh`/`cosh`/`tanh` (×6),
`tuple` (×5) — the operators not yet in the basis, and a parser gap (×33).

## 6. What this does NOT claim

- Not a verified compiler — it certifies the *expression*, and binds it to the shipped
  kernel via `tree_hash`; it does not prove the backend lowering is correct.
- Not coverage of the whole stdlib — `tan`/inverse-trig/hyperbolic/`floor` and loop/mutation kernels are
  off-basis (§5), named, not silently included.
- The bounds are parametric in data-dependent inputs (condition numbers, denominator
  guards) supplied per call — the fold proves the *shape* is sound, not per-kernel constants.
- The relative-vs-absolute trade is real: `gexpr_sound` (absolute, magnitude-based) is
  more general but looser on pure arithmetic than `renc_sound`'s tight relative `(1+w)^d`.

## 7. Check it yourself

```bash
# Build the whole certifier (part of the MachLib aggregate):
lake build MachLib

# Confirm a result is sorryAx-free + rests only on the documented axiom base:
lake env lean -e '#print axioms MachLib.Real.gexpr_sound'

# Measure the binder's reach over the real stdlib (needs the Forge repo):
PYTHONPATH=<forge> python3 tools/machlib_bind/bind.py --dir <eml-stdlib>
```

The certifier spans `OperatorBasisSound` / `OperatorBasisTrans` / `OperatorBasisGeneral`
/ `DivisionError` / `OperatorBasisComplete` / `TrajectoryCertified` / `ForgeBindingDemo`.
Each file's header states what it adds; this front door is the map.
