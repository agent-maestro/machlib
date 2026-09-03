# MachSig — Canonicalizer Bridge Inventory

Phase 1b question: *which extracted term representations can be passed through an existing
data-level canonicalizer?*

## The canonicalizers, type-verified

| canonicalizer | input → output | data-level? | total & deterministic? | source |
|---|---|---|---|---|
| `pnorm` | `List Real → List Real` | yes | yes (structural recursion, drops trailing zeros) | `PolyBasics` |
| `normalizeCoeff` | `CoeffPoly → CoeffPoly` | yes | yes | `NormalizedPolynomialRootCount:93` |
| `simplifyCoeffs` | `List Poly → List Poly` | yes | yes | `SingleExpKhovanskii:649` |
| `PfaffianFn.simplify` | `PfaffianFn → PfaffianFn` | yes | yes | `PfaffianChain:113` |

All four are genuine data-level functions with clean signatures. **The machinery is not the
blocker.**

## Why no canonical view can be populated anyway

The blocker is the *input side*, and it is structural:

1. **The dominant term population has no canonicalizer.** 993 of 1,084 records are `EMLTree`, and
   there is no `EMLTree → EMLTree` normaliser in the corpus. `pnorm` and friends act on
   coefficient lists and Pfaffian functions, not on EML trees.

2. **The representations that DO have canonicalizers appear as variables, not literals.** Polynomial
   coefficient lists occur throughout MachLib as `pev P x` where `P` is universally quantified. A
   canonicalizer needs a concrete `List Real`; the corpus supplies a bound variable. Applying
   `pnorm` to a free variable is not a canonical view, it is an unreduced application.

3. **Half of all extracted terms are structurally incomplete anyway** (54% carry opaque leaves), so
   even where a normaliser existed the input would frequently be partial.

## Verdict

**No representation can be given an honest canonical view at this commit, and none is implemented.**
The Phase 1b instruction was explicit that if none can be wired without inventing serialization
semantics, the correct action is to document that and stop. That is what this file does.

`canonical_views` therefore remains `[]` with availability `unsupported_representation` in both the
declaration and term censuses.

## Consequence for Phase 6, stated plainly

Phase 6's canonicalisation-drift gate — described in the roadmap as the phase that alone makes
MachSig operationally useful — **has nothing to watch, and this is now a measured finding rather
than an inference**. It is blocked on one of:

* an `EMLTree` normaliser existing in MachLib (none does), or
* a corpus containing concrete polynomial/Pfaffian literals (it does not), or
* MachSig defining its own canonical form — which would mean inventing normalization semantics that
  MachLib does not have, and would make the gate a test of MachSig against itself rather than a test
  of MachLib.

The third option is available and cheap, and it is the one that should **not** be taken silently.
