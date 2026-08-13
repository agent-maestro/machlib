import MachLib.EMLDepthTameness
import MachLib.EMLNetlistDepth

/-!
# Certified EML synthesis — the acceptance side

**T4 of the research slate.** The premise is that the *search* is untrusted and the *checker* is
not. Gradient descent, evolutionary search, MCTS, an LLM, a human with a hunch — all of them merely
**propose** a tree `t`. Nothing about how `t` was found appears anywhere below, and nothing about it
is assumed. This is deliberate: it is why the programme needs **no convergence theorem**. Proving
that an optimiser recovers a closed form is a bad bet — architecture choice alone can move exact
recovery between 100% and 0% on the same target language, so expressiveness does not imply
findability. Proving *accepted* results correct is cheap, and it is already this corpus's shape.

## Where the trust boundary sits, and who drew it

The boundary is not a convention adopted here. **Lean's own computability marker already draws it**,
and the two sides behave differently under `#eval` and `rfl`:

* `EMLTree.depth` is a plain `def`. The kernel decides it — `invX4.depth = 4` is closed `by rfl`
  even though `invX4` contains the opaque real `log (log (1 + exp 1))`, because `depth` never
  inspects the constant it carries. **Cost is decidable.**
* `EMLTree.eval` is `noncomputable`, because `MachLib.Real` is axiomatised. There is no code
  generator, and `#eval` on any tree fails. **Semantics is not decidable — it must be proved.**

So `Accepted` below has exactly two fields, one from each side, and the semantic one is an
*obligation the proposer must discharge*, never something the checker computes. A proposal cannot be
accepted with the obligation missing: it is a field of the structure.

Note what this actually buys, which is **not** "axioms are trustworthy" — axiomatising the reals
*enlarges* the trusted mathematical base. The useful property is narrower and structural:

> **Within this formal layer**, semantic EML obligations cannot be discharged by executable
> evaluation. Syntactic costs compute; semantic claims must pass through kernel-checked
> propositions.

The scope matters. Numerical checks of an EML expression certainly can exist elsewhere in the
project — in Python, in a simulator, on hardware — and they are useful. The virtue is narrower: such
a computation **cannot inhabit `Meets`**. There is no `#eval` path by which a spot-check could be
mistaken for a discharged obligation, because there is no `#eval` path at all.

## What is actually new here

Not the acceptance bookkeeping — that is a two-field structure and is honestly trivial. The content
is `DepthOptimal`: a certificate that pairs a witness with a **lower-bound theorem**, and so
certifies not merely *a* solution but a **minimum-depth** one. That second half is mathematics and
cannot be checked, only consumed; the checker's job is to insist it is present.

The pipeline then transfers optimality to hardware without any further reasoning about the target:
`depth_optimal_netDepth_floor` and `depth_optimal_schedule_floor` hold for **every** specification
with a certificate, and the previously bespoke theorems `inv_x_netlist_depth_ge_four` /
`inv_x_schedule_ge_four_L` are re-derived as consequences — they were the generic pipeline all
along, specialised by hand.

**Four targets are certified, forming a calibration ladder.** The point of the ladder is that the
*same* generic pipeline consumes lower bounds of four different kinds:

| target | `d` | where its lower bound comes from |
| --- | --- | --- |
| `exp x` | 1 | two-point evaluation on depth-0 trees |
| `exp (exp x)` | 2 | depth-≤1 growth envelope (**T2-native**) |
| `exp (exp x) − x` | 2 | same envelope, both children loaded |
| `1/x` | 4 | full structural case analysis (the reciprocal arm) |

**Two of them are certified deliberately as controls.** Instantiating a pipeline only on the target it was
abstracted from proves close to nothing: a green build says the abstraction is *true*, not that it
is the one anyone needs. So `exp` (§5) is certified alongside `1/x` (§4), chosen to differ on the
two axes where a design flaw would hide — its lower bound shares no lemma with the reciprocal arm,
and its specification is **total** where `invSpec` is restricted to `0 < x`. Both certificates feed
the same §3 theorems unchanged.

## Scope — read before quoting anything here

* A certificate is **relative to its specification**. `DepthOptimal P t d` says nothing about any
  `P'`, including a slightly relaxed one; an ε-tolerant spec is a different `P` and needs its own
  lower bound. Nothing here approximates.
* Optimality is in **depth only**. Size is not certified, and by `netDepth_eq_depth`'s companion
  results size does not survive the lowering to a DAG anyway.
* The hardware floors are in **units of `L`**, the per-node latency. They are floors on schedule
  position, not on nanoseconds; converting needs a measured `L` and a lowering that actually spends
  `L` per node.

## Where the proved chain ends and measurement begins

The certified statement is: **EML tree depth survives DAG sharing exactly, and induces a serial
EML-block dependency floor on any valid schedule.** Tree size does not survive sharing. That is the
whole of what is proved, and it is a statement about the **straight-line EML datapath**, not about
silicon.

Everything past that boundary is measured, not derived, and the measurement says the source-level
path model stops being exact:

| stage | status |
| --- | --- |
| tree → DAG | **proved** — depth exact, size destroyed exponentially |
| DAG → schedule | **proved** — latency floor survives; **area is not a path invariant** |
| schedule → RTL → mapped gates | **measured** — synthesis optimises across block boundaries |

The measurement that fixes the boundary: a 4-deep chain of pipelined EML blocks has combinational
path ratio ×1.00, and the same arithmetic with the registers removed has ratio ×3.55 — not ×4.00,
because cross-boundary optimisation reclaims the difference. So a certificate here bounds
**EML-block dependency depth**; it does not bound nanoseconds, gate levels after mapping, or the
cost of any particular `exp`/`log` block's internals.
-/

namespace MachLib
namespace EMLTree

open Real

/-! ### 1. Specifications, proposals, acceptance -/

/-- A **semantic** specification: a predicate on the *function* a tree computes, never on its
syntax. Taking specs at this type is what makes the transfer to netlists free — a program and its
unfolding compute the same function, so they satisfy the same specs by construction, with no
side condition asserting that the spec respects extensional equality. -/
abbrev SemSpec := (Real → Real) → Prop

/-- The tree-level reading of a specification. -/
def Meets (P : SemSpec) (t : EMLTree) : Prop := P t.eval

/-- **An accepted proposal.** Two fields, one per side of the trust boundary.

`meets` is the proof obligation: the checker never computes it, and it cannot be omitted, because
acceptance *is* this structure. `cost` is decided by the kernel — every instance below closes it
`by rfl`. -/
structure Accepted (P : SemSpec) (t : EMLTree) (d : Nat) : Prop where
  /-- The semantic obligation. Supplied by the proposer; never decided here. -/
  meets : Meets P t
  /-- The cost fact. Decided by the kernel. -/
  cost : t.depth = d

theorem accepted_meets {P : SemSpec} {t : EMLTree} {d : Nat} (h : Accepted P t d) :
    P t.eval := h.meets

theorem accepted_cost {P : SemSpec} {t : EMLTree} {d : Nat} (h : Accepted P t d) :
    t.depth = d := h.cost

/-! ### 2. Optimality certificates

Acceptance alone says a proposal works. It says nothing about whether a better one exists — and a
search that returns a depth-9 solution to a depth-4 problem is *accepted* and *bad*. Upgrading
acceptance to optimality needs a second ingredient the checker cannot produce. -/

/-- **A depth-optimality certificate.** An accepted witness at depth `d`, together with a proof that
nothing shallower meets the spec.

The asymmetry is the point. `accepted` is cheap and mechanical. `minimal` is a lower-bound theorem —
it quantifies over *all* trees, so no amount of search can establish it and no checker can decide
it. The certificate's job is to make its absence impossible to overlook. -/
structure DepthOptimal (P : SemSpec) (t : EMLTree) (d : Nat) : Prop where
  /-- A witness that attains `d`. -/
  accepted : Accepted P t d
  /-- Nothing shallower works. Mathematics, not checking. -/
  minimal : ∀ u : EMLTree, u.depth < d → Meets P u → False

/-- The witness attains the certified depth. -/
theorem depth_optimal_attains {P : SemSpec} {t : EMLTree} {d : Nat} (h : DepthOptimal P t d) :
    Meets P t ∧ t.depth = d := ⟨h.accepted.meets, h.accepted.cost⟩

/-- **The certificate means what it says: `d` is a floor for every solution.** This is the form the
rest of the file consumes — the `False`-shaped `minimal` field turned into a usable inequality. -/
theorem depth_optimal_is_minimum {P : SemSpec} {t : EMLTree} {d : Nat} (h : DepthOptimal P t d) :
    ∀ u : EMLTree, Meets P u → d ≤ u.depth := by
  intro u hu
  -- No `by_contra` in this corpus (see `EMLReciprocalDepth2`); split on the decidable order.
  cases Nat.lt_or_ge u.depth d with
  | inl hlt => exact False.elim (h.minimal u hlt hu)
  | inr hge => exact hge

/-- Two certificates for the same specification agree on the value. So "the minimum depth of `P`"
is well defined, and independent of which witness a search happened to find. -/
theorem depth_optimal_value_unique {P : SemSpec} {t t' : EMLTree} {d d' : Nat}
    (h : DepthOptimal P t d) (h' : DepthOptimal P t' d') : d = d' := by
  have h1 : d ≤ d' := by
    have := depth_optimal_is_minimum h t' h'.accepted.meets
    rw [h'.accepted.cost] at this; exact this
  have h2 : d' ≤ d := by
    have := depth_optimal_is_minimum h' t h.accepted.meets
    rw [h.accepted.cost] at this; exact this
  omega

/-- A certified minimum-depth proposal cannot be beaten on depth, only tied. Stated for the case a search cares
about: any *strictly* shallower proposal is refuted outright, whatever produced it. -/
theorem depth_optimal_refutes_shallower {P : SemSpec} {t : EMLTree} {d : Nat}
    (h : DepthOptimal P t d) (u : EMLTree) (hu : u.depth < d) : ¬ Meets P u :=
  fun hm => h.minimal u hu hm

/-! ### 3. Transfer to hardware

The certificate is about trees. Silicon is not a tree — it is a shared DAG, then a schedule. Both
steps are handled generically here: nothing below mentions any particular specification. -/

/-- **Every netlist meeting a certified specification has at least the certified depth.**

The tree→DAG step. Sharing collapses a tree into a DAG and destroys size exponentially, but depth
survives exactly (`netDepthAt_eq_depth`), so the floor crosses the lowering intact. -/
theorem depth_optimal_netDepth_floor {P : SemSpec} {t : EMLTree} {d : Nat}
    (h : DepthOptimal P t d) (p : Nat → EMLInstr) (i : Nat) (hp : P (progEvalAt p i)) :
    d ≤ netDepthAt p i := by
  have hfun : progEvalAt p i = (unfoldAt p i).eval :=
    funext (fun x => progEvalAt_eq_unfoldAt_eval p i x)
  have hm : Meets P (unfoldAt p i) := by rw [hfun] at hp; exact hp
  rw [netDepthAt_eq_depth]
  exact depth_optimal_is_minimum h _ hm

/-- **Every valid schedule of such a netlist places the output no earlier than `L * d`.**

The DAG→schedule step. A schedule may reorder and share freely; what it may not do is start a node
before both its operands are done, and that alone forces the floor. Area is destroyed here; the
latency floor is not.

`L` is the per-node latency of the lowering. The conclusion is a position in a schedule, not a
time — see the scope note in the module header. -/
theorem depth_optimal_schedule_floor {P : SemSpec} {t : EMLTree} {d : Nat}
    (h : DepthOptimal P t d) (p : Nat → EMLInstr) (hwf : ProgWf p) (L : Nat) (s : Nat → Nat)
    (hs : SchedValid p L s) (i : Nat) (hp : P (progEvalAt p i)) :
    L * d ≤ s i := by
  have hw := schedule_ge_wdepth p hwf L s hs (i + 1) i (Nat.lt_succ_self i)
  rw [wdepth_scaled] at hw
  have hfun : progEvalAt p i = (unfoldAt p i).eval :=
    funext (fun x => progEvalAt_eq_unfoldAt_eval p i x)
  have hm : Meets P (unfoldAt p i) := by rw [hfun] at hp; exact hp
  have hd : d ≤ (unfoldAt p i).depth := depth_optimal_is_minimum h _ hm
  exact Nat.le_trans (Nat.mul_le_mul_left L hd) hw

/-! ### 4. The worked instance — `1/x`

This is the one specification for which both halves currently exist. The upper half is a witness
(`invX4`, found by hand); the lower half is `inv_x_not_in_eml_depth_le_3`, the closing theorem of
the reciprocal arm. Assembling them is the first certified minimum-depth EML synthesis result in the
corpus, and the assembly is three lines because the arm did the work. -/

/-- The reciprocal specification, on the positives. -/
def invSpec : SemSpec := fun f => ∀ x : Real, 0 < x → f x = 1 / x

/-- **`invX4` is certified depth-optimal for `1/x`.**

`accepted.cost` is closed `by rfl` — the kernel decides the depth of a tree carrying the opaque
constant `log (log (1 + exp 1))`, exactly as the module header claims. -/
theorem invX4_depth_optimal : DepthOptimal invSpec invX4 4 :=
  { accepted := { meets := invX4_eval, cost := by rfl }
    minimal := fun u hu hm => inv_x_not_in_eml_depth_le_3 u (by omega) hm }

/-- `d(1/x) = 4`, in the form the certificate exports: **no EML tree of any shape computes `1/x`
above the positives in fewer than four levels**, and four is attained. -/
theorem inv_x_min_depth (u : EMLTree) (hu : ∀ x : Real, 0 < x → u.eval x = 1 / x) :
    4 ≤ u.depth := depth_optimal_is_minimum invX4_depth_optimal u hu

/-! #### The bespoke hardware theorems, re-derived

`inv_x_netlist_depth_ge_four` and `inv_x_schedule_ge_four_L` were each proved directly against
`1/x`. They are instances of §3 applied to the certificate — the specialisation was doing no work
that the generic pipeline does not do. Both are re-derived here from the certificate alone, with no
reference to reciprocals in either proof. -/

/-- Re-derivation of `inv_x_netlist_depth_ge_four` from the certificate. -/
theorem inv_x_netDepth_floor_via_certificate (p : Nat → EMLInstr) (i : Nat)
    (hp : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    4 ≤ netDepthAt p i :=
  depth_optimal_netDepth_floor invX4_depth_optimal p i hp

/-- Re-derivation of `inv_x_schedule_ge_four_L` from the certificate. The `4 * L` of the original
and the `L * 4` produced by the generic theorem differ only by commutativity. -/
theorem inv_x_schedule_floor_via_certificate (p : Nat → EMLInstr) (hwf : ProgWf p) (L : Nat)
    (s : Nat → Nat) (hs : SchedValid p L s) (i : Nat)
    (hp : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    4 * L ≤ s i := by
  have h := depth_optimal_schedule_floor invX4_depth_optimal p hwf L s hs i hp
  omega

/-! ### 5. A second target, to test whether §3 is generic or merely true

§4 instantiates the pipeline on the target it was abstracted from, which proves very little: a green
build says the abstraction is *true*, not that it is the one anyone needs. So here is a second
certificate, chosen to differ from `1/x` on the two axes most likely to hide a design flaw.

* **Its lower bound comes from a different mechanism.** `1/x`'s came from the reciprocal arm's
  entire case analysis. This one is a two-point argument on depth-0 trees, proved from scratch
  below, sharing no lemma with §4.
* **Its specification is total.** `invSpec` is restricted to `0 < x`; `expSpec` is not. If the
  transfer theorems had quietly depended on a domain restriction, this is where it would show.

The certificate is *cheap*, and that is the point rather than a boast — `exp` is shallow, so the
lower bound is two evaluations. What is being tested is the pipeline, not the target. -/

/-- The exponential, specified on **all** of `Real`. -/
def expSpec : SemSpec := fun f => ∀ x : Real, f x = exp x

/-- The depth-1 witness: `exp x − log 1 = exp x`. Totalised `log` is not even needed here — the
argument is the genuine `1`. -/
noncomputable def expTree : EMLTree := EMLTree.eml EMLTree.var (EMLTree.const 1)

theorem expTree_depth : expTree.depth = 1 := by rfl

theorem expTree_eval : ∀ x : Real, expTree.eval x = exp x := by
  intro x
  show exp (EMLTree.var.eval x) - log ((EMLTree.const (1 : Real)).eval x) = exp x
  show exp x - log (1 : Real) = exp x
  rw [log_one]
  mach_ring

/-- **No depth-0 tree computes `exp`.** A depth-0 tree is a constant or the variable
(`depth_zero_cases`), and two evaluations kill each: a constant cannot separate `exp 0` from
`exp 1`, and `var` fails already at `0`, where `exp 0 = 1 ≠ 0`. -/
theorem exp_not_depth_zero (u : EMLTree) (hu : u.depth < 1) (h : Meets expSpec u) : False := by
  have h0 : u.depth = 0 := by omega
  rcases depth_zero_cases h0 with ⟨c, hc⟩ | hv
  · -- `u = const c`: then `c = exp 0` and `c = exp 1`, but `exp 0 < exp 1`.
    subst hc
    have e0 : c = exp 0 := h 0
    have e1 : c = exp 1 := h 1
    have hlt : exp 0 < exp 1 := exp_lt one_pos
    rw [← e0, ← e1] at hlt
    exact lt_irrefl_ax c hlt
  · -- `u = var`: then `0 = exp 0 = 1`, contradicting `0 < 1`.
    subst hv
    have e0 : (0 : Real) = exp 0 := h 0
    rw [exp_zero] at e0
    have hp : (0 : Real) < 1 := one_pos
    rw [← e0] at hp
    exact lt_irrefl_ax 0 hp

/-- **`exp` is certified depth-optimal at depth 1.** The second certificate, and the evidence that
§3 is genuinely generic: it shares no lemma with §4 and carries no domain restriction. -/
theorem expTree_depth_optimal : DepthOptimal expSpec expTree 1 :=
  { accepted := { meets := expTree_eval, cost := by rfl }
    minimal := exp_not_depth_zero }

/-- The hardware floor for `exp`, obtained from §3 with no new reasoning — the same theorem that
produced the `1/x` floor, applied to a certificate built from unrelated mathematics. -/
theorem exp_netDepth_floor (p : Nat → EMLInstr) (i : Nat)
    (hp : ∀ x : Real, progEvalAt p i x = exp x) :
    1 ≤ netDepthAt p i :=
  depth_optimal_netDepth_floor expTree_depth_optimal p i hp

/-! ### 6. Depth-2 certificates whose lower bounds are **T2-native**

§4 and §5 draw their lower bounds from opposite extremes: the reciprocal arm's full case analysis,
and a two-point evaluation. Neither uses the shallow-tameness kit as a *kit*. The two certificates
here do — both lower bounds are one application of `depth_le_one_le_exp_shift`, the depth-≤1 growth
envelope, and neither touches reciprocal machinery.

They also exercise the grammar in two different ways. `exp (exp x)` uses **totalised log** as a
construction tool rather than a hazard: `log 0 = 0`, so `eml t (const 0)` is exactly `exp ⟦t⟧` and
iterated exponentials cost one level each. `exp (exp x) − x` instead loads *both* children, using
`log (exp x) = x` to make the right child do real work.

The resulting calibration ladder is the point — the same pipeline now accepts lower bounds of four
different kinds, at depths 1, 2, 2 and 4. -/

/-- The arithmetic core of both depth-2 lower bounds, over **plain variables**.

Stated separately on purpose: with `E = exp D`, `F = exp (1 + exp D)` and `G = exp F` substituted
in, `mach_linarith` spends its whole heartbeat budget in `whnf` on the nested exponentials. Over
four opaque atoms it is immediate. Reading: the growth envelope gives `G ≤ F + D`, doubling gives
`F + F ≤ G`, hence `F ≤ D` — contradicted by `F ≥ 2 + E ≥ 3 + D`. -/
private theorem envelope_absurd {D E F G : Real}
    (hDD : 1 + D ≤ E) (hgr : 1 + (1 + E) ≤ F) (hdd : F + F ≤ G) (hb : G ≤ F + D) : False := by
  have s1 : 1 + (1 + D) ≤ 1 + E := add_le_add_left hDD 1
  have s2 : 1 + (1 + (1 + D)) ≤ 1 + (1 + E) := add_le_add_left s1 1
  have hFge : 1 + (1 + (1 + D)) ≤ F := le_trans s2 hgr
  have hFD : F + F ≤ F + D := le_trans hdd hb
  have s3 : F + (1 + (1 + (1 + D))) ≤ F + F := add_le_add_left hFge F
  have chain : F + (1 + (1 + (1 + D))) ≤ F + D := le_trans s3 hFD
  have e : F + (1 + (1 + (1 + D))) = (F + D) + (1 + (1 + 1)) := by mach_ring
  rw [e] at chain
  have hz : (0 : Real) < 1 + (1 + 1) := by mach_linarith
  have s4 : (F + D) + 0 < (F + D) + (1 + (1 + 1)) := add_lt_add_left hz (F + D)
  have e2 : (F + D) + 0 = F + D := by mach_ring
  rw [e2] at s4
  exact lt_irrefl_ax (F + D) (lt_of_lt_of_le s4 chain)

/-- Same shape one subtraction along: the envelope now bounds `G − x` where `x = 1 + E`. -/
private theorem envelope_absurd_sub {D E F G : Real}
    (hDD : 1 + D ≤ E) (hxx : (1 + E) + (1 + E) ≤ F) (hdd : F + F ≤ G)
    (hb : G - (1 + E) ≤ F + D) : False := by
  have hb' : G ≤ (F + D) + (1 + E) := by
    have t := add_le_add_left hb (1 + E)
    have e1 : (1 + E) + (G - (1 + E)) = G := by mach_ring
    have e2 : (1 + E) + (F + D) = (F + D) + (1 + E) := by mach_ring
    rw [e1, e2] at t; exact t
  have hFF : F + F ≤ (F + D) + (1 + E) := le_trans hdd hb'
  have s1 : 1 + (1 + D) ≤ 1 + E := add_le_add_left hDD 1
  have s2 : (1 + E) + (1 + (1 + D)) ≤ (1 + E) + (1 + E) := add_le_add_left s1 (1 + E)
  have s3 : F + ((1 + E) + (1 + (1 + D))) ≤ F + ((1 + E) + (1 + E)) := add_le_add_left s2 F
  have s4 : F + ((1 + E) + (1 + E)) ≤ F + F := add_le_add_left hxx F
  have chain : F + ((1 + E) + (1 + (1 + D))) ≤ (F + D) + (1 + E) :=
    le_trans s3 (le_trans s4 hFF)
  have e : F + ((1 + E) + (1 + (1 + D))) = ((F + D) + (1 + E)) + (1 + 1) := by mach_ring
  rw [e] at chain
  have hz : (0 : Real) < 1 + 1 := by mach_linarith
  have s5 : ((F + D) + (1 + E)) + 0 < ((F + D) + (1 + E)) + (1 + 1) :=
    add_lt_add_left hz ((F + D) + (1 + E))
  have e2 : ((F + D) + (1 + E)) + 0 = (F + D) + (1 + E) := by mach_ring
  rw [e2] at s5
  exact lt_irrefl_ax ((F + D) + (1 + E)) (lt_of_lt_of_le s5 chain)

/-- Iterated exponential, specified on all of `Real`. -/
def expExpSpec : SemSpec := fun f => ∀ x : Real, f x = exp (exp x)

/-- Depth-2 witness. `log 0 = 0` by totalisation, so this is `exp (exp x)` exactly. -/
noncomputable def expExpTree : EMLTree := EMLTree.eml expTree (EMLTree.const 0)

theorem expExpTree_depth : expExpTree.depth = 2 := by rfl

theorem expExpTree_eval : ∀ x : Real, expExpTree.eval x = exp (exp x) := by
  intro x
  show exp (expTree.eval x) - log ((EMLTree.const (0 : Real)).eval x) = exp (exp x)
  rw [expTree_eval]
  show exp (exp x) - log (0 : Real) = exp (exp x)
  rw [log_nonpos (le_refl (0 : Real))]
  mach_ring

/-- **No depth-≤1 tree reaches the double-exponential scale.** One application of the depth-≤1
growth envelope: `A x ≤ exp x + D` on `[1,∞)`, while `exp (exp x) ≥ exp x + exp x`, so the
envelope forces `exp x ≤ D` — refuted at `x = 1 + exp D`. -/
theorem expExp_not_depth_le_one (u : EMLTree) (hu : u.depth < 2) (h : Meets expExpSpec u) :
    False := by
  have h1 : u.depth ≤ 1 := by omega
  obtain ⟨D, hD⟩ := depth_le_one_le_exp_shift u h1
  -- NB: `mach_linarith` is not linarith — its `apply le_trans` branch diverges on a `≤` goal
  -- carrying an opaque atom like `exp D`. Explicit steps instead.
  have hx1 : (1 : Real) ≤ 1 + exp D := by
    have t := add_le_add_left (le_of_lt (exp_pos D)) 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at t; exact t
  have hb := hD (1 + exp D) hx1
  rw [h (1 + exp D)] at hb
  exact envelope_absurd (one_add_le_exp D) (one_add_le_exp (1 + exp D))
    (two_mul_le_exp (le_of_lt (exp_pos (1 + exp D)))) hb

theorem expExpTree_depth_optimal : DepthOptimal expExpSpec expExpTree 2 :=
  { accepted := { meets := expExpTree_eval, cost := by rfl }
    minimal := expExp_not_depth_le_one }

/-- The second depth-2 target, loading **both** children: `log (exp x) = x`, so the right child
contributes genuinely rather than being neutralised. -/
def expExpSubSpec : SemSpec := fun f => ∀ x : Real, f x = exp (exp x) - x

noncomputable def expExpSubTree : EMLTree := EMLTree.eml expTree expTree

theorem expExpSubTree_depth : expExpSubTree.depth = 2 := by rfl

theorem expExpSubTree_eval : ∀ x : Real, expExpSubTree.eval x = exp (exp x) - x := by
  intro x
  show exp (expTree.eval x) - log (expTree.eval x) = exp (exp x) - x
  rw [expTree_eval, log_exp]

/-- Same envelope, one subtraction further along: the envelope now forces `exp x − x ≤ D`, and
`two_mul_le_exp` gives `exp x − x ≥ x`, refuted at `x = 1 + exp D`. -/
theorem expExpSub_not_depth_le_one (u : EMLTree) (hu : u.depth < 2) (h : Meets expExpSubSpec u) :
    False := by
  have h1 : u.depth ≤ 1 := by omega
  obtain ⟨D, hD⟩ := depth_le_one_le_exp_shift u h1
  have hx1 : (1 : Real) ≤ 1 + exp D := by
    have t := add_le_add_left (le_of_lt (exp_pos D)) 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at t; exact t
  have hxnn : (0 : Real) ≤ 1 + exp D :=
    add_nonneg (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos D))
  have hb := hD (1 + exp D) hx1
  rw [h (1 + exp D)] at hb
  exact envelope_absurd_sub (one_add_le_exp D) (two_mul_le_exp hxnn)
    (two_mul_le_exp (le_of_lt (exp_pos (1 + exp D)))) hb

theorem expExpSubTree_depth_optimal : DepthOptimal expExpSubSpec expExpSubTree 2 :=
  { accepted := { meets := expExpSubTree_eval, cost := by rfl }
    minimal := expExpSub_not_depth_le_one }

/-! ### 7. The iterated-exponential tower — an infinite family, and what it costs

`T₀ x = x`, `T_{n+1} x = exp (T_n x)`. The two depth-2 certificates of §6 were not isolated
examples: **they are `T₁` and `T₂`**, and seeing that is what makes the family the right object.

The **upper** half is free and holds for every `n`: totalised `log 0 = 0` makes `eml t (const 0)`
exactly `exp ⟦t⟧`, so one `eml` node buys one exponential and `towerTree n` has depth exactly `n`.

The **lower** half is the open problem, and this section's job is to state precisely what it would
buy. `tower_depth_optimal_of_lower_bound` shows the entire infinite certified family is a *function*
of one lower-bound family — so T4's supply of targets is bounded below by T2's supply of theorems,
not by any amount of engineering here. That is the "T4 consumes T2" reading, made formal rather
than asserted. -/

/-- `T₀ x = x`, `T_{n+1} x = exp (T_n x)`. -/
noncomputable def towerFn : Nat → Real → Real
  | 0, x => x
  | n + 1, x => exp (towerFn n x)

/-- One `eml` node per level; the right child is neutralised by totalised `log 0 = 0`. -/
noncomputable def towerTree : Nat → EMLTree
  | 0 => EMLTree.var
  | n + 1 => EMLTree.eml (towerTree n) (EMLTree.const 0)

/-- **One node buys exactly one exponential.** Depth is `n` on the nose, not `≤ n`. -/
theorem towerTree_depth : ∀ n : Nat, (towerTree n).depth = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show 1 + max (towerTree k).depth 0 = k + 1
      rw [ih]
      simp
      omega

theorem towerTree_eval : ∀ (n : Nat) (x : Real), (towerTree n).eval x = towerFn n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      show exp ((towerTree k).eval x) - log ((EMLTree.const (0 : Real)).eval x) = _
      rw [ih x]
      show exp (towerFn k x) - log (0 : Real) = _
      rw [log_nonpos (le_refl (0 : Real))]
      show exp (towerFn k x) - 0 = exp (towerFn k x)
      mach_ring

/-- The specification of the `n`-th tower level. -/
def towerSpec (n : Nat) : SemSpec := fun f => ∀ x : Real, f x = towerFn n x

/-- The upper half, for **every** `n`: `d(Tₙ) ≤ n`, witnessed and accepted. -/
theorem towerTree_accepted (n : Nat) : Accepted (towerSpec n) (towerTree n) n :=
  { meets := towerTree_eval n, cost := towerTree_depth n }

/-- **The missing ingredient, named.** No tree shallower than `n` computes `Tₙ`.

This is a statement about *all* trees at *all* depths, so no search can establish it and no checker
can decide it. It is the single input that would turn the tower into an unbounded supply of
certified targets. -/
def TowerLowerBound : Prop :=
  ∀ n : Nat, ∀ u : EMLTree, u.depth < n → Meets (towerSpec n) u → False

/-- The bounded form, which is what is actually proved so far. -/
def TowerLowerBoundUpTo (N : Nat) : Prop :=
  ∀ n : Nat, n ≤ N → ∀ u : EMLTree, u.depth < n → Meets (towerSpec n) u → False

/-- **The reduction.** One lower-bound family ⟹ an infinite certified family. Everything else —
witness, depth computation, acceptance, and the §3 hardware transfer — is already in place for every
`n`, so this is the whole of what is missing. -/
theorem tower_depth_optimal_of_lower_bound (h : TowerLowerBound) (n : Nat) :
    DepthOptimal (towerSpec n) (towerTree n) n :=
  { accepted := towerTree_accepted n, minimal := h n }

/-- The same reduction in bounded form. -/
theorem tower_depth_optimal_upto {N : Nat} (h : TowerLowerBoundUpTo N) (n : Nat) (hn : n ≤ N) :
    DepthOptimal (towerSpec n) (towerTree n) n :=
  { accepted := towerTree_accepted n, minimal := h n hn }

/-- **`d(Tₙ) = n` for `n ≤ 2`**, assembled from §5 and §6 — `T₀ = x` is depth 0 vacuously, `T₁`
is `exp`, and `T₂` is `exp (exp x)`. The tower's first three levels are exactly the certificates
already proved, which is the evidence that the family is the natural object rather than a
generalisation invented after the fact. -/
theorem tower_lower_bound_upto_two : TowerLowerBoundUpTo 2 := by
  intro n hn u hu hm
  match n, hn with
  | 0, _ => exact absurd hu (Nat.not_lt_zero _)
  | 1, _ => exact exp_not_depth_zero u hu hm
  | 2, _ => exact expExp_not_depth_le_one u hu hm

theorem tower_certified_upto_two (n : Nat) (hn : n ≤ 2) :
    DepthOptimal (towerSpec n) (towerTree n) n :=
  tower_depth_optimal_upto tower_lower_bound_upto_two n hn

/-! ### 7b. `d(T₃) = 3` — the growth/decay pair earns its first new theorem

`T₃` is the first tower level beyond what the shallow classifications already gave. Its lower bound
is the first consumer of `depth_le_two_growth_envelope`, which is in turn the first place the
**growth** and **decay** halves are used together — the left child bounded above by
`depth_le_one_le_exp_shift`, the right child bounded *below* by
`depth_le_one_log_lower_at_infinity`.

The argument is short once the envelope exists, and its shape is the reason the pair was needed:
a depth-≤2 tree is capped at `exp (exp x + K) + M`, one exponential above `exp x`. `T₃` is
`exp (exp (exp x))`, two exponentials above. The gap is closed by noting that
`exp (exp x) ≥ exp x + exp x`, so once `exp x ≥ K + 1` the tower's outer exponent clears the
envelope's by a full unit — and one unit of exponent is a factor of `e ≥ 2`, which the additive
slack `M` cannot absorb. -/

/-- The arithmetic core: a quantity that both doubles and is capped by itself plus a constant. -/
private theorem tower3_absurd {P M : Real} (hPP : P + P ≤ P + M) (hMP : M < P) : False :=
  lt_irrefl_ax (P + P) (lt_of_le_of_lt hPP (add_lt_add_left hMP P))

private theorem le_add_nonneg {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have t := add_le_add_left hb a
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at t; exact t

/-- The core of the argument, over a **free** evaluation point — this corpus has no `set` tactic,
and stating it this way keeps the elaborator away from a large repeated term. -/
private theorem tower3_core {K M x : Real}
    (hx_ge_expK : exp K ≤ x) (hx_ge_expMK : exp (M - K) ≤ x)
    (hcap : exp (exp (exp x)) ≤ exp (exp x + K) + M) : False := by
  have hex : 1 + x ≤ exp x := one_add_le_exp x
  have hxle : x ≤ exp x := by
    have t : x ≤ 1 + x := by
      have u : x ≤ x + 1 := le_add_nonneg (le_of_lt zero_lt_one_ax)
      have e : x + (1 : Real) = 1 + x := by mach_ring
      rw [e] at u; exact u
    exact le_trans t hex
  have hP : (0 : Real) ≤ exp (exp x + K) := le_of_lt (exp_pos _)
  -- (i) `exp x ≥ K + 1`, via `exp K ≥ 1 + K`.
  have hi : K + 1 ≤ exp x := by
    have s1 : 1 + exp K ≤ 1 + x := add_le_add_left hx_ge_expK 1
    have s2 : 1 + (1 + K) ≤ 1 + exp K := add_le_add_left (one_add_le_exp K) 1
    have e : (1 : Real) + (1 + K) = K + 1 + 1 := by mach_ring
    rw [e] at s2
    have s3 : K + 1 ≤ K + 1 + 1 := le_add_nonneg (le_of_lt zero_lt_one_ax)
    exact le_trans s3 (le_trans s2 (le_trans s1 hex))
  -- (ii) `M < exp (exp x + K)`, via `exp t ≥ 1 + t` twice.
  have hMlt : M < exp (exp x + K) := by
    have a1 : 1 + (exp x + K) ≤ exp (exp x + K) := one_add_le_exp (exp x + K)
    have a5 : 1 + (1 + (M - K)) ≤ 1 + exp (M - K) := add_le_add_left (one_add_le_exp (M - K)) 1
    have a4 : 1 + exp (M - K) ≤ 1 + x := add_le_add_left hx_ge_expMK 1
    have a7 : 1 + (1 + (M - K)) + K ≤ 1 + x + K := add_le_add_wit (le_trans a5 a4) (le_refl K)
    have a8 : 1 + x + K ≤ exp x + K := add_le_add_wit hex (le_refl K)
    have a9 : 1 + x + K ≤ 1 + (exp x + K) := by
      have e : (1 : Real) + (exp x + K) = 1 + exp x + K := by mach_ring
      rw [e]
      exact add_le_add_wit (add_le_add_left hxle 1) (le_refl K)
    have a6 : M + 1 < 1 + (1 + (M - K)) + K := by
      have t1 : M + 1 + 0 < M + 1 + 1 := add_lt_add_left zero_lt_one_ax (M + 1)
      have e1 : M + 1 + (0 : Real) = M + 1 := by mach_ring
      have e2 : M + 1 + (1 : Real) = 1 + (1 + (M - K)) + K := by mach_mpoly [M, K]
      rw [e1, e2] at t1; exact t1
    have a10 : M + 1 ≤ exp (exp x + K) :=
      le_of_lt (lt_of_lt_of_le a6 (le_trans a7 (le_trans a9 a1)))
    have a11 : M < M + 1 := by
      have t1 : M + 0 < M + 1 := add_lt_add_left zero_lt_one_ax M
      have e1 : M + (0 : Real) = M := by mach_ring
      rw [e1] at t1; exact t1
    exact lt_of_lt_of_le a11 a10
  -- The tower's outer exponent clears the envelope's by a full unit.
  have hgap : exp x + K + 1 ≤ exp (exp x) := by
    have d1 : exp x + exp x ≤ exp (exp x) := two_mul_le_exp (le_of_lt (exp_pos x))
    have d2 : exp x + (K + 1) ≤ exp x + exp x := add_le_add_left hi (exp x)
    have e : exp x + (K + 1) = exp x + K + 1 := by mach_ring
    rw [e] at d2
    exact le_trans d2 d1
  -- One unit of exponent is a factor of `e ≥ 2`, which the additive slack `M` cannot absorb.
  have hbig : exp (exp x + K) + exp (exp x + K) ≤ exp (exp (exp x)) := by
    have m1 : exp (exp x + K + 1) ≤ exp (exp (exp x)) := exp_monotone hgap
    have m2 : exp (exp x + K + 1) = exp (exp x + K) * exp 1 := by
      have e : exp x + K + 1 = (exp x + K) + 1 := by mach_ring
      rw [e]; exact exp_add _ _
    have m4 : exp (exp x + K) * (1 + 1) ≤ exp (exp x + K) * exp 1 :=
      mul_le_mul_of_nonneg_left (one_add_le_exp 1) hP
    have m5 : exp (exp x + K) * ((1 : Real) + 1) = exp (exp x + K) + exp (exp x + K) := by
      mach_ring
    rw [m5] at m4
    rw [m2] at m1
    exact le_trans m4 m1
  exact tower3_absurd (le_trans hbig hcap) hMlt

/-- **No depth-≤2 tree computes `exp (exp (exp x))`.** -/
theorem tower3_not_depth_le_two (u : EMLTree) (hu : u.depth < 3) (h : Meets (towerSpec 3) u) :
    False := by
  have h2 : u.depth ≤ 2 := by omega
  obtain ⟨K, M, X₀, hX1, hEnv⟩ := depth_le_two_growth_envelope u h2
  have hKp : (0 : Real) < exp K := exp_pos K
  have hMKp : (0 : Real) < exp (M - K) := exp_pos (M - K)
  have hX0 : (0 : Real) < X₀ := lt_of_lt_of_le zero_lt_one_ax hX1
  have hxX : X₀ ≤ X₀ + (exp (M - K) + exp K) :=
    le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hMKp) hKp))
  have hb := hEnv (X₀ + (exp (M - K) + exp K)) hxX
  rw [h (X₀ + (exp (M - K) + exp K))] at hb
  have hcap : exp (exp (exp (X₀ + (exp (M - K) + exp K))))
      ≤ exp (exp (X₀ + (exp (M - K) + exp K)) + K) + M := hb
  refine tower3_core ?_ ?_ hcap
  · have e : X₀ + (exp (M - K) + exp K) = exp K + (X₀ + exp (M - K)) := by mach_ring
    rw [e]
    exact le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hX0) hMKp))
  · have e : X₀ + (exp (M - K) + exp K) = exp (M - K) + (X₀ + exp K) := by mach_ring
    rw [e]
    exact le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hX0) hKp))

theorem tower_lower_bound_upto_three : TowerLowerBoundUpTo 3 := by
  intro n hn u hu hm
  match n, hn with
  | 0, _ => exact absurd hu (Nat.not_lt_zero _)
  | 1, _ => exact exp_not_depth_zero u hu hm
  | 2, _ => exact expExp_not_depth_le_one u hu hm
  | 3, _ => exact tower3_not_depth_le_two u hu hm

/-- **`d(Tₙ) = n` for `n ≤ 3`.** The first level proved by the growth/decay pair rather than by a
bespoke classification. -/
theorem tower_certified_upto_three (n : Nat) (hn : n ≤ 3) :
    DepthOptimal (towerSpec n) (towerTree n) n :=
  tower_depth_optimal_upto tower_lower_bound_upto_three n hn

/-! ### 7c. `d(T₄) = 4` — instantiating `U₃`

`depth_le_three_growth_envelope` was built but never used. A green build says an abstraction is
*true*, not that it is the one anyone needs, so this section spends it. If `U₃`'s shape were subtly
unusable — wrong constant placement, a ray that cannot be met — this is where it would show.

The argument is the `d(T₃)` one with the tower shifted up a level, and it is now packaged: the tail
that was inlined in `tower3_core` is extracted as `exp_gap_absurd`, since a quantity that doubles
cannot also be capped by itself plus a constant. -/

/-- **The generic gap step.** If the inner exponent clears the envelope's by a full unit, the node
is at least double the envelope, which the additive slack cannot absorb. Extracted from
`tower3_core`, which used it inline. -/
private theorem exp_gap_absurd {inner bound N : Real}
    (hgap : bound + 1 ≤ inner) (hN : N < exp bound) (hcap : exp inner ≤ exp bound + N) : False := by
  have h1 : exp (bound + 1) ≤ exp inner := exp_monotone hgap
  have h2 : exp bound + exp bound ≤ exp (bound + 1) := exp_add_one_doubles bound
  have h3 : exp bound + exp bound ≤ exp bound + N := le_trans (le_trans h2 h1) hcap
  have h4 : exp bound + N < exp bound + exp bound := add_lt_add_left hN (exp bound)
  exact lt_irrefl_ax _ (lt_of_le_of_lt h3 h4)

/-- Core of `d(T₄) = 4`, over a free evaluation point (this corpus has no `set`). -/
private theorem tower4_core {K M N x : Real}
    (hK : exp (K + 1) ≤ x) (hMK : exp (M - K) ≤ x) (hN : exp (N - K - M) ≤ x)
    (hcap : exp (exp (exp (exp x))) ≤ exp (exp (exp x + K) + M) + N) : False := by
  have hxe : x ≤ exp x := self_le_exp x
  have hu0 : (0 : Real) ≤ exp x := le_of_lt (exp_pos x)
  have huK : K + 1 ≤ exp x := le_trans (self_le_exp (K + 1)) (le_trans hK hxe)
  have huMK : M - K ≤ exp x := le_trans (self_le_exp (M - K)) (le_trans hMK hxe)
  have huN : N - K - M ≤ exp x := le_trans (self_le_exp (N - K - M)) (le_trans hN hxe)
  -- (i) the inner exponent clears the envelope's by a unit
  have hstepA : exp x + K + 1 ≤ exp (exp x) := by
    have d1 : exp x + exp x ≤ exp (exp x) := two_mul_le_exp hu0
    have d2 : exp x + (K + 1) ≤ exp x + exp x := add_le_add_left huK (exp x)
    have e : exp x + (K + 1) = exp x + K + 1 := by mach_ring
    rw [e] at d2; exact le_trans d2 d1
  have hbig : exp (exp x + K) + exp (exp x + K) ≤ exp (exp (exp x)) :=
    le_trans (exp_add_one_doubles _) (exp_monotone hstepA)
  have hM1 : M + 1 ≤ exp (exp x + K) := by
    have a1 : 1 + (exp x + K) ≤ exp (exp x + K) := one_add_le_exp _
    have a2 : M + 1 ≤ 1 + (exp x + K) := by
      have v := add_le_add_wit huMK (le_refl K)
      have e1 : M - K + K = M := by mach_mpoly [M, K]
      rw [e1] at v
      have u := add_le_add_wit (le_refl (1 : Real)) v
      have e2 : (1 : Real) + M = M + 1 := by mach_ring
      rw [e2] at u; exact u
    exact le_trans a2 a1
  have hgap : exp (exp x + K) + M + 1 ≤ exp (exp (exp x)) := by
    have v : exp (exp x + K) + (M + 1) ≤ exp (exp x + K) + exp (exp x + K) :=
      add_le_add_left hM1 _
    have e : exp (exp x + K) + (M + 1) = exp (exp x + K) + M + 1 := by mach_ring
    rw [e] at v; exact le_trans v hbig
  -- (ii) the additive slack is beaten
  have hNlt : N < exp (exp (exp x + K) + M) := by
    have a1 : 1 + (exp (exp x + K) + M) ≤ exp (exp (exp x + K) + M) := one_add_le_exp _
    have a2 : 1 + (exp x + K) ≤ exp (exp x + K) := one_add_le_exp _
    have a3 : N < 1 + (1 + (exp x + K) + M) := by
      have v := add_le_add_wit (add_le_add_wit huN (le_refl K)) (le_refl M)
      have e1 : N - K - M + K + M = N := by mach_mpoly [N, K, M]
      rw [e1] at v
      -- `N ≤ exp x + K + M < 1 + (1 + (exp x + K) + M)`
      have hlt : exp x + K + M < 1 + (1 + (exp x + K) + M) := by
        have t1 : exp x + K + M + 0 < exp x + K + M + (1 + 1) :=
          add_lt_add_left (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax) _
        have e2 : exp x + K + M + (0 : Real) = exp x + K + M := by mach_ring
        have e3 : exp x + K + M + ((1 : Real) + 1) = 1 + (1 + (exp x + K) + M) := by mach_ring
        rw [e2, e3] at t1; exact t1
      exact lt_of_le_of_lt v hlt
    have a4 : 1 + (1 + (exp x + K) + M) ≤ 1 + (exp (exp x + K) + M) :=
      add_le_add_wit (le_refl (1 : Real)) (add_le_add_wit a2 (le_refl M))
    exact lt_of_lt_of_le a3 (le_trans a4 a1)
  exact exp_gap_absurd hgap hNlt hcap

/-- **No depth-≤3 tree computes `T₄`.** The first consumer of `U₃`. -/
theorem tower4_not_depth_le_three (u : EMLTree) (hu : u.depth < 4) (h : Meets (towerSpec 4) u) :
    False := by
  have h3 : u.depth ≤ 3 := by omega
  obtain ⟨K, M, N, X₀, hX1, hEnv⟩ := depth_le_three_growth_envelope u h3
  have p1 : (0 : Real) < exp (K + 1) := exp_pos _
  have p2 : (0 : Real) < exp (M - K) := exp_pos _
  have p3 : (0 : Real) < exp (N - K - M) := exp_pos _
  have hX0 : (0 : Real) < X₀ := lt_of_lt_of_le zero_lt_one_ax hX1
  have hxX : X₀ ≤ X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M)) :=
    le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos
      (le_of_lt (add_pos_of_nonneg_pos (le_of_lt p1) p2)) p3))
  have hb := hEnv (X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))) hxX
  rw [h (X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M)))] at hb
  have hcap : exp (exp (exp (exp (X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))))))
      ≤ exp (exp (exp (X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))) + K) + M) + N := hb
  refine tower4_core ?_ ?_ ?_ hcap
  · have e : X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))
        = exp (K + 1) + (X₀ + exp (M - K) + exp (N - K - M)) := by mach_ring
    rw [e]
    exact le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos
      (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hX0) p2)) p3))
  · have e : X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))
        = exp (M - K) + (X₀ + exp (K + 1) + exp (N - K - M)) := by mach_ring
    rw [e]
    exact le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos
      (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hX0) p1)) p3))
  · have e : X₀ + (exp (K + 1) + exp (M - K) + exp (N - K - M))
        = exp (N - K - M) + (X₀ + exp (K + 1) + exp (M - K)) := by mach_ring
    rw [e]
    exact le_add_nonneg (le_of_lt (add_pos_of_nonneg_pos
      (le_of_lt (add_pos_of_nonneg_pos (le_of_lt hX0) p1)) p2))

theorem tower_lower_bound_upto_four : TowerLowerBoundUpTo 4 := by
  intro n hn u hu hm
  match n, hn with
  | 0, _ => exact absurd hu (Nat.not_lt_zero _)
  | 1, _ => exact exp_not_depth_zero u hu hm
  | 2, _ => exact expExp_not_depth_le_one u hu hm
  | 3, _ => exact tower3_not_depth_le_two u hu hm
  | 4, _ => exact tower4_not_depth_le_three u hu hm

/-- **`d(Tₙ) = n` for `n ≤ 4`.** -/
theorem tower_certified_upto_four (n : Nat) (hn : n ≤ 4) :
    DepthOptimal (towerSpec n) (towerTree n) n :=
  tower_depth_optimal_upto tower_lower_bound_upto_four n hn

/-! ### 8. What this checker does **not** decide

Recorded here rather than in a report, so it travels with the code.

* **It does not find anything.** There is no search in this file, and adding one would not change a
  single theorem. That is the design, not an omission.
* **It does not decide `meets`.** `eval` is noncomputable; the obligation is discharged by a proof
  term or acceptance does not happen. A numerical spot-check is not a proof of `Meets`, and there is
  deliberately no path in this file that would let one masquerade as one.
* **It does not certify optimality on its own.** `DepthOptimal` requires a lower-bound theorem as
  input. For `1/x` that theorem cost the reciprocal arm its entire run. For a fresh target there is
  no reason to expect one to be cheap, and **no certificate can be produced without it** — the
  structure will not typecheck.
* **It does not extend to approximation.** `invSpec` is exact equality. An ε-tolerant spec is a
  different `SemSpec` and inherits none of the lower bounds proved here.
* **It says nothing about size.** Only depth. -/

end EMLTree
end MachLib
