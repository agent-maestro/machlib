# Self-assessment — the axiom-witness mechanism

**Status: NOT a solicitation.** This was drafted as an external review request and is deliberately
not being sent. A cold review is a favour that can be asked once, and spending it on a mechanism
before there is a product is the wrong trade; the natural audience arrives later, without a favour
owed. It is kept because its value does not depend on a reader: **§5 is an honest inventory of
where we think this is weakest.**

If a reviewer does appear, this is the packet to hand them — one mechanism, not the corpus, not the
compiler, self-contained enough that nobody need read 252 435 lines of Lean.

**The question we would ask, stated so it can be answered "no":**

> Given a Mathlib-free Lean 4 corpus with an explicitly pinned set of trusted axioms, does
> mechanically checking that each axiom's *interpreted type* is inhabited by a Mathlib term buy a
> meaningfully stronger soundness story than not doing it — or is it relative consistency with extra
> steps, in which case what exactly is the extra step worth?

Answers that would be useful, including the dismissive ones:

- this is legitimate and standard, here is its name in the literature
- this is redundant given X
- your interpretation map is the weak point and here is how to break it
- this resembles prior work Y, which you should cite
- the witnesses do not buy what you think they buy, because Z

---

## 1. The 90-second context

**MachLib** is a Lean 4 corpus that does not depend on Mathlib. `MachLib.Real` is an *axiomatised*
ordered field with `exp`, `log`, `sin`, derivatives, and so on — declared, not constructed. The
corpus is ≈ 7 667 theorems outside its generated sub-corpus.

Why no Mathlib: the corpus ships proof certificates alongside generated engineering artifacts
(C, Verilog, VHDL…), and we wanted the trusted base to be small, enumerable and auditable rather
than "whatever Mathlib transitively contains." That is a design choice, not a claim that Mathlib is
untrustworthy.

The obvious objection to an axiomatised base is the obvious one: **you can axiomatise `False`.**
A corpus whose reals are axioms can prove anything if one of those axioms is wrong, and
`#print axioms` will look perfectly clean while it does so.

The live figures, all of which this document's own build gate pins to the corpus:

| class | n | meaning |
|---|---|---|
| trusted footprint | 156 | axioms any shipped theorem is allowed to touch |
| witnessed | 119 | a Mathlib term inhabits the interpreted type, kernel-checked |
| mapped | 12 | carrier/function symbols — interpreted, not propositions |
| standard | 3 | `propext`, `Classical.choice`, `Quot.sound` |
| float-bridge | 22 | about IEEE-754 floats — **unwitnessable in principle**, see §5 |
| unmodeled | 0 | a gate fails if this is ever nonzero |

## 2. The mechanism

A sibling repo (`monogate-lean`, also public) imports **both** Mathlib and MachLib. For each
registered MachLib axiom it:

1. takes the axiom's actual `Expr` **type**;
2. rewrites it through an **interpretation map** — `MachLib.Real ↦ ℝ`, its `Add`/`Mul`/`LT`
   instances ↦ ℝ's, `MachLib.Real.exp ↦ Real.exp`, MachLib's `HasDerivAt ↦` Mathlib's, …;
3. elaborates a registered **witness term** at that interpreted type.

Building the file *is* the check: any registered axiom whose witness fails to inhabit its
interpreted type raises `logError`.

**The design point we think matters.** The check is on the **type**, not the name. A name table
(`rolle_ct ↦ rolle_witnessed`) would have marked an earlier, genuinely **unsound** open-interval
`rolle` as "witnessed" forever, because the name never changed when the statement did. It is
teeth-verified in the negative direction too: deliberately pairing `rolle_ct` with `Real.exp_pos`,
or `add_comm` with `mul_comm`, is rejected.

A cross-repo note, since you will hit it immediately: the registry holds **121** witnesses, the
audit reports **119**. Both are right — two witnesses cover axioms that are no longer in the trusted
footprint. The audit says so explicitly rather than silently taking the larger number.

## 3. Prior art, as we understand it — please correct this

We do **not** think the idea is new. Exhibiting a model of an axiomatic theory inside a richer
theory is **relative consistency via interpretation**, which is textbook mathematical logic. The
corpus separately carries a ℤ-model (`MachLib.Model.intModel`) that depends on no MachLib axiom —
a conventional relative-consistency witness for the algebraic fragment.

Adjacent work we are aware of and would expect a reviewer to raise: Isabelle's definitional
approach and the work on definitional/overloading soundness; realizability models in Coq;
`#print axioms` hygiene as ordinary Lean practice.

**So the question is not "is interpretation novel."** It is whether doing it *continuously,
mechanically, at type level, across two repos on independently pinned toolchains, as a build gate*
is worth anything beyond a one-time paper proof — and whether our particular execution is sound.

## 4. The incident that makes us think the *continuous* part matters

The bridge **went dark for 33 days and nothing said so.**

MachLib moved to Lean v4.32.2; `monogate-lean` stayed on v4.14.0. Because it requires MachLib *by
path*, it was compiling MachLib's current source under the old toolchain and could not build — while
the ledger went on reporting "trusted," because *trusted* meant **listed**, and the thing that
turned listing into evidence had stopped running.

Worse, its `trustedFootprint` was a **hand-pinned snapshot** — 78 names against a live 149 — whose
own cross-check passed *against the copy*.

When it was finally rebuilt it **rejected two witnesses immediately**: Mathlib v4.32 had *flipped*
`add_lt_add_left` to add on the right.

The gate now fails on toolchain skew between the two repos, on any trusted axiom with no witness and
no classification, and on a stale excuse entry. The footprint is never re-pinned by hand.

We think that incident is the actual argument for the mechanism, and we would like to know whether
an outside reader agrees or thinks it argues for something else entirely (e.g. "just use Mathlib").

## 5. Where we think this is weakest — please start here

1. **The interpretation map is trusted, unaudited code.** It is a hand-written list of
   `MachLib constant ↦ Mathlib term`. If an entry maps an axiom onto a *weaker* statement, the
   witness check passes and the axiom has been laundered. Nothing mechanically checks that the
   interpretation is faithful, and we do not know how it could. **This is the attack we most expect
   and least know how to answer.**
2. **`RealSetFinite` is not `Set.Finite`.** MachLib defines finiteness as a length bound on every
   `Nodup` list drawn from the set. Witnessing `analytic_finite_zeros_compact` therefore needs the
   analysis *and* a conversion. That conversion is proved; but it is an example of the interpreted
   statement and the original being related by more than renaming.
3. **22 float-bridge axioms cannot be witnessed even in principle.** They assert that a concrete
   IEEE-754 `exp`/`atan`/`sqrt` rounds within ε of the real function. Mathlib has no IEEE-754
   semantics, so these are validated by *measurement*, not by a model. We deliberately do not
   average them into the "witnessed" figure. Anyone shown a hardware certificate should be pointed
   at this row first.
4. **What does this buy over using Mathlib directly?** A fair question we cannot answer from the
   inside.

## 6. Check it yourself — the fifteen-minute version

Both repos are public.

```bash
git clone https://github.com/agent-maestro/machlib
git clone https://github.com/agent-maestro/monogate-lean

# the mechanism, one file — the registry, the interpretation map, the checker
$EDITOR monogate-lean/MonogateEML/AxiomWitnessBridge.lean

# the classification, live, from machlib/foundations:
python3 tools/soundness_witness_audit.py
#   trusted footprint (live ledger) : 156
#   witnessed against Mathlib       : 119
#   UNMODELED (no witness at all)   : 0
```

To see it bite: change a witness in `witnessRegistry` to a term of the wrong type and rebuild
`monogate-lean`. To see the classification bite: add an axiom to a shipped theorem's footprint
without registering it.

## 7. The claim we should actually make

One correction to our own framing, recorded because it is the thing most likely to be overstated in
public. This mechanism does **not** establish that the axioms are sound, and saying so would be
indefensible. What it does is narrower and more useful:

> For each trusted MachLib axiom intended to represent ordinary mathematics, we continuously check
> that its *interpreted* proposition is inhabited in an independently maintained formal environment.

That is **semantic-drift detection**, not a soundness proof. The 33-day incident in §4 is the whole
evidence for it: the axioms changed, the names did not, the documentation did not, and everyone
would have gone on believing the original argument still applied. The build fails instead.

Anywhere this mechanism is described — site, README, certificate appendix — it should be described
that way and not more strongly.
