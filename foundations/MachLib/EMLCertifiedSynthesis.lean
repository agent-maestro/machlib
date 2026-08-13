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

> Axiomatised reals prevent semantic evaluation from masquerading as proof. Syntactic costs
> compute; semantic claims must pass through kernel-checked propositions.

There is no `#eval` path by which a numerical spot-check could be mistaken for `Meets`, because
there is no `#eval` path at all.

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
| DAG → schedule | **proved** — latency floor survives, area destroyed |
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

/-! ### 7. What this checker does **not** decide

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
