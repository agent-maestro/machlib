# MachSig Phase 0.5 — Feature Admissibility

**Question put by the directive:** are `source_exp_count` and `source_log_count` algebraically
redundant with the primitive node count, and if so over what domain?

**Answer: redundant in two grammars, independent in a third.** The census must therefore scope the
decision by `representation_kind` rather than drop the fields globally.

---

## Method

Established by reading each grammar's constructors and its evaluation function — not inferred from
the fact that `eml` "looks like" it carries one of each. Four grammars were checked because
reconnaissance found four; the answer is not uniform across them.

## The four grammars

### `EMLTree` — REDUNDANT

```
inductive EMLTree | const : Real → EMLTree | var | eml : EMLTree → EMLTree → EMLTree
def eval : | const c => c | var => x | eml t₁ t₂ => Real.exp (t₁.eval x) - Real.log (t₂.eval x)
```

`const` and `var` emit neither. `eml` emits exactly one `Real.exp` and one `Real.log`. By structural
recursion, for every `t`:

```
exp_applications(eval t) = log_applications(eval t) = eml_node_count(t)
```

Three columns, one quantity. **Retain `eml_node_count`; omit the other two.**

### `FTerm` — REDUNDANT, with a caveat that must survive into the schema

```
inductive FTerm | const | var | add | sub | mul | div | F : FTerm → FTerm
def FTerm.evalM (a b c) : | .F u, x => Fmix a b c (evalM a b c u x)
def Fmix (a b c x) : Real := a * exp x + b * log x + c
```

Each `F` emits exactly one `exp` and one `log` *application*, so
`exp_applications = log_applications = fOcc`, and `fOcc` already exists in the corpus.

**Caveat:** at `a = 0` the `exp` application is multiplied by zero. Syntactic presence and semantic
contribution diverge, and `Fmix` is parameterised, so a term's *effective* transcendental content
depends on `(a,b,c)` — which is data outside the term. Any count here is a **syntactic** count and
must be labelled as one. `Fmix 1 1 0 = Fbasis` is the instantiation most of the corpus uses.

### `EML` (Forge-facing) — NOT REDUNDANT

```
inductive EML | lit | var | bin : BinOp → … | neg | elet : String → EML → EML → EML
              | tr1 : Trans1 → EML → EML | tr2 : Trans2 → … | cond : EML → EML → EML → EML
inductive Trans1 | exp | ln | sin | cos | tan | sqrt | abs | asin | acos | atan | sinh | cosh | tanh | log10
```

`exp` and `ln` are **distinct `Trans1` constructors**. A term may carry three `exp`s and no `ln`s.
Here `exp_count` and `log_count` are genuinely independent features and both must be retained — as
must the other twelve `Trans1` heads, which the original roadmap's field list does not mention at
all.

Two further consequences specific to this grammar: `elet` introduces **sharing**, so tree/DAG size
diverge *within the source representation* rather than only after canonicalisation; and `cond`
introduces branching, which is the closest thing in the corpus to a real branch count — though it is
a syntactic branch, not a mathematical component.

### `ElementaryEMLErf` — SEPARATE, not yet assessed

`| pure : ElementaryEML → _ | erf | add | mul`. Delegates to `ElementaryEML.eval`. Its
transcendental content is `erf`-flavoured and does not reduce to exp/log counts. Left unassessed;
recorded as an open item rather than guessed at.

---

## Decision

| grammar | `exp_count` / `log_count` | keep? |
|---|---|---|
| `EMLTree` | `= eml_node_count` exactly | **omit**; keep `eml_node_count` |
| `FTerm` | `= fOcc` exactly (syntactic) | **omit**; keep `fOcc`, labelled syntactic |
| `EML` | independent; 14 `Trans1` heads | **keep**, and add per-head counts |
| `ElementaryEMLErf` | unassessed | defer |

Consistency invariant worth asserting in the extractor (cheap, and it fails loudly if a grammar
changes): for `EMLTree`-derived rows, `exp_count`, `log_count` and `eml_node_count` must agree if
all three are ever computed together.

## An epistemic note the schema must carry

The `EMLTree` equality is a property of the **source text of `eval`**, not a Lean theorem — `eval`
returns a `Real`, so there is no syntactic object inside Lean over which "number of `exp`
applications" could be stated, let alone proved. The claim is meta-level and rests on reading the
definition.

That is a weaker warrant than a proved relation, and MachSig should record it as such rather than
implying the redundancy was verified by the kernel. It is exactly the distinction the directive asks
the signature system to preserve: *counted*, *proved*, and *read off a definition* are three
different epistemic states, and only the first two are machine-checked.
