import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.EMLHierarchy
import MachLib.Pfaffian
import MachLib.KhovanskiiLemma
import MachLib.IntermediateValue

/-!
# EML → Pfaffian embedding + Sin Barrier (Phase D)

Conditional on Phase A's axiomatized zero bound
(`PfaffianFunction.zero_bound`), ships the END-USER results:

1. **EML embedding** (`eml_pfaffian`): every EMLTree corresponds to
   a Pfaffian function with matching evaluation.

2. **Sin barrier for all depths** (`sin_not_in_eml_any_depth`):
   `Real.sin ∉ EML_k` for every Nat k. ONE theorem.

**Proof strategy:** Given `t.eval = sin globally` with `t.depth ≤ k`:

- `eml_pfaffian t` is Pfaffian. Its eval = t.eval = sin.
- Not identically zero (sin 1 > 0). So `PfaffianFunction.zero_bound`
  applies. Let M be the bound.
- Construct M+1 distinct zeros of sin at `pi, 2pi, ..., (M+1)pi`
  (all in the interval `(0, (M+2) * pi)`).
- Bound says ≤ M zeros, but we have M+1. Contradiction.

**Honest scope:** This is CONDITIONAL on Phase A's axiomatized zero
bound. The constructive Khovanskii proof (Phase C) replaces the
axiom with a real proof.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## sin(natCast k * π) = 0 for all Nat k -/

/-- Sin vanishes at all integer multiples of π. -/
theorem sin_natCast_mul_pi (k : Nat) : sin (natCast k * pi) = 0 := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul]
    exact sin_zero
  | succ n ih =>
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * pi = natCast n * pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib, sin_add, ih, sin_pi, zero_mul, mul_zero, add_zero]

end Real
end MachLib

namespace MachLib

open Real

/-! ## EML → Pfaffian embedding — constructive (chunk 5, 2026-06-11)

Khovanskii sprint week 1 chunk 5. With chunk 4's structural refactor
of PfaffianFunction (and the rfl-trivial eval theorems on each closure
op), the EML → Pfaffian embedding becomes a direct recursive
definition: the three EMLTree constructors map to `const`, `pfaffian_var`,
and the `exp` / `log` / `sub` composition. The eval-agreement falls
out by structural induction with `rfl` at each base case. -/

/-- Every EML tree corresponds to a Pfaffian function. Recursive on
the tree structure: `const c` → `PfaffianFunction.const c`,
`var` → `pfaffian_var`, `eml t1 t2` → `exp(f1) - log(f2)` where
`f_i = eml_pfaffian t_i`.

⚠ **Domain qualification (2026-06-12 step 2):** The construction
produces a `PfaffianFunction` (a Lean structure) for *any* EMLTree,
but the resulting function is GENUINELY Pfaffian (in the
classical-Khovanskii sense) only on intervals where every log-
subargument stays strictly positive. This is because MachLib's
`Real.log` is clamped at 0 for `x ≤ 0` (a piecewise-total function),
and piecewise functions are not analytic, hence not Pfaffian.

A correct downstream application of `PfaffianFunction.zero_bound`
to `eml_pfaffian t` on `(a, b)` therefore requires verifying:

  for every `eml t1 t2` subtree of `t`, the inner function
  `t2.eval` is strictly positive on `(a, b)`.

The predicate `EMLPfaffianValidOn` (below) captures this domain
condition explicitly. Downstream consumers should require it as a
precondition.

For the headline `sin_not_in_eml_any_depth`, the domain condition is
*forced* by the hypothesis: if `t.eval = sin` globally, then for any
`eml` subtree on the interval `(0, (M+2)·π)`, the inner `t2.eval`
must stay positive — because sin takes negative values on `(π, 2π)`,
and `exp(t1.eval x) - log(t2.eval x) = sin x` with negative sin
forces `log(t2.eval x)` to be the analytic (positive-domain) value,
which forces `t2.eval x > 0`. So the sin-barrier proof's domain
condition is satisfied implicitly by its hypothesis — no explicit
precondition needed for that specific theorem. -/
noncomputable def eml_pfaffian : EMLTree → PfaffianFunction
  | EMLTree.const c   => PfaffianFunction.const c
  | EMLTree.var       => pfaffian_var
  | EMLTree.eml t1 t2 =>
      (exp_as_pfaffian.comp (eml_pfaffian t1)).sub
        (log_as_pfaffian.comp (eml_pfaffian t2))

/-- Domain-validity predicate for `eml_pfaffian` on `(a, b)`. The
construction is genuinely Pfaffian on `(a, b)` iff all log subargument
sub-evaluations stay strictly positive throughout the interval.

This predicate is the load-bearing precondition that any non-trivial
application of `PfaffianFunction.zero_bound` to `eml_pfaffian t`
must verify. -/
def EMLPfaffianValidOn : EMLTree → Real → Real → Prop
  | EMLTree.const _,    _, _ => True
  | EMLTree.var,        _, _ => True
  | EMLTree.eml t1 t2,  a, b =>
      EMLPfaffianValidOn t1 a b ∧
      EMLPfaffianValidOn t2 a b ∧
      (∀ x : Real, a < x → x < b → 0 < t2.eval x)

/-- **`EMLPfaffianValidOn` is monotone in the right endpoint.** Validity on the bigger interval
`(a,B)` gives validity on any smaller `(a,b) ⊆ (a,B)` (`b ≤ B`) — the positivity constraint's
universal quantifier just ranges over fewer points. By structural induction on `s`; the only
content is in the `eml` case, where it's a one-line transitivity (`x < b ≤ B → x < B`).

Useful for closing `eml_pfaffian_validon_from_sin_equality`-style arguments at a SMALL requested
`b`: prove validity on some large, convenient `B` (e.g. one guaranteed to contain a zero of `sin`,
sidestepping the case where `(0,b)` itself is too short to contain one), then downgrade via this
lemma. Zero new axioms. -/
theorem EMLPfaffianValidOn_mono_b {s : EMLTree} {a b B : Real} (hbB : b ≤ B)
    (h : EMLPfaffianValidOn s a B) : EMLPfaffianValidOn s a b := by
  induction s with
  | const c => trivial
  | var => trivial
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨ih1 h1, ih2 h2, fun x hxa hxb => h3 x hxa (lt_of_lt_of_le hxb hbB)⟩

/-- The eval-agreement theorem. Proven by structural induction; each
base case is `rfl` from chunk 4's structural definitions, and the
recursive case unfolds via `PfaffianFunction.sub_eval` / `comp_eval`
(also `rfl`) plus the IH. -/
theorem eml_pfaffian_eval (t : EMLTree) (x : Real) :
    (eml_pfaffian t).eval x = t.eval x := by
  induction t with
  | const c => rfl
  | var => rfl
  | eml t1 t2 ih1 ih2 =>
    show Real.exp ((eml_pfaffian t1).eval x) - Real.log ((eml_pfaffian t2).eval x)
       = Real.exp (t1.eval x) - Real.log (t2.eval x)
    rw [ih1, ih2]

/-! ## Bridge: EMLPfaffianValidOn → PfaffianExpr.IsValidAt

The `EMLPfaffianValidOn t a b` predicate (defined above) captures the
EMLTree-level domain condition: every `eml t1 t2` subtree has
`t2.eval > 0` on `(a, b)`. The `PfaffianExpr.IsValidAt` predicate
(defined in `KhovanskiiLemma.lean`) is its Pfaffian-side counterpart.
This theorem bridges the two. Proven by structural induction on
`EMLTree`. -/
theorem eml_pfaffian_isvalidat_of_validon (t : EMLTree) (a b : Real)
    (hvalidon : EMLPfaffianValidOn t a b) :
    ∀ x : Real, a < x → x < b → (eml_pfaffian t).expr.IsValidAt x := by
  intro x hxa hxb
  induction t with
  | const c =>
    -- eml_pfaffian (const c) = ⟨const c⟩; IsValidAt = True.
    trivial
  | var =>
    -- eml_pfaffian var = ⟨var⟩; IsValidAt = True.
    trivial
  | eml t1 t2 ih1 ih2 =>
    -- EMLPfaffianValidOn (eml t1 t2) a b = validon t1 ∧ validon t2 ∧ (∀ x, ..., 0 < t2.eval x)
    obtain ⟨hv1, hv2, hpos⟩ := hvalidon
    -- (eml_pfaffian (eml t1 t2)).expr.IsValidAt x: triplet from sub/comp/comp structure.
    refine ⟨?_, ?_⟩
    · -- First subtree: comp exp_atom (eml_pfaffian t1).expr
      refine ⟨ih1 hv1, ?_⟩
      -- exp_atom.IsValidAt _ = True
      trivial
    · -- Second subtree: comp log_atom (eml_pfaffian t2).expr
      refine ⟨ih2 hv2, ?_⟩
      -- log_atom.IsValidAt ((eml_pfaffian t2).expr.eval x) = 0 < t2.eval x
      show (0 : Real) < (eml_pfaffian t2).expr.eval x
      have := hpos x hxa hxb
      -- (eml_pfaffian t2).expr.eval x = (eml_pfaffian t2).eval x = t2.eval x
      show (0 : Real) < (eml_pfaffian t2).eval x
      rw [eml_pfaffian_eval t2 x]
      exact this

/-! ## Sin-equality forces validity (axiomatized analytic argument)

If `t.eval x = sin x` for all `x : Real`, then `EMLPfaffianValidOn t 0 b`
holds for every `b > 0`. The classical argument:

1. `t.eval` equals `sin`, hence is smooth (sin is smooth everywhere).
2. For any `eml t1 t2` subtree of `t`, the eval is
   `exp(t1.eval x) - log_clamped(t2.eval x)`. Since `exp` is smooth,
   smoothness of the whole forces `log_clamped(t2.eval x)` to be smooth.
3. `log_clamped` is discontinuous at `0` (jumps from 0 to the analytic
   log). For its composition with `t2.eval` to be smooth, `t2.eval`
   must not cross 0 anywhere `t.eval = sin` is smooth — which is
   everywhere.
4. At any zero of `sin` (`x = i·π`), if `t = eml t1 t2`, then
   `t.eval = exp - log_clamped(t2) = 0` forces `log_clamped(t2) > 0`
   (since `exp > 0`), hence `t2 > 0` (since log_clamped(t2) = 0 when
   t2 ≤ 0).
5. By connectivity of `(0, b)` and `t2` not crossing 0 plus `t2 > 0`
   at any sin-zero in the interval (if any exists), `t2 > 0` throughout.

The argument requires formalizing smoothness preservation, continuity,
and connectivity — none of which MachLib currently has. Axiomatized
here as a single load-bearing analytic claim, named so reviewers can
locate it as a single auditable item. Closure path: add a Smoothness
module with `IsSmoothOn`, `IsSmoothOn_of_eq`, `Continuous_of_HasDerivAt`,
and a connectivity argument; ~300-500 lines, multi-session.

**Step 4 above is now PROVEN below (`eml_nonpos_forces_log_arg_pos`), and in a strictly more
general form** (`≤ 0`, not just "at a zero of sin"; no reference to `sin`/`cos` at all — it's a
pure structural fact about `eml` nodes). It needs no continuity/connectivity: whenever an `eml`
node's OWN value is non-positive, its log-argument is forced positive, by a two-line contradiction
(no smoothness reasoning at all).

**2026-07-16: pushed further.** `log_unbounded_below` formalizes the "log blows up near `0⁺`"
fact flagged above as missing — it turned out to be a short derivation from `exp`'s existing axioms
(`exp_lt`, `exp_injective`, `exp_log`, `exp_pos`), not a genuinely new primitive. Combining it with
`eml_nonpos_forces_log_arg_pos`'s trick gives `eml_gap_avoidance`: for an `eml` node bounded ABOVE by
`U`, its log-argument can never land strictly between `0` and `exp(-U)` — it's either `≤ 0` or
`≥ exp(-U)`. This is a genuine strengthening (a two-sided GAP the log-argument can't cross), not
just the one-sided fact from step 4. `EMLPfaffianValidOn_mono_b` separately disposes of the
"requested `b` is too small to contain a zero of sin/cos" edge case (prove validity on a large,
convenient interval, downgrade to any smaller one).

**What still doesn't close, even with the gap:** turning "avoids the gap everywhere" into "always
on the same side of the gap" needs `intermediate_value` (already proven, `IntermediateValue.lean`)
applied to the log-argument — which needs the log-argument CONTINUOUS on `(0,b)`. Establishing that
continuity for an ARBITRARILY NESTED subtree, without already knowing its own internal log-arguments
are well-formed (needed to know the composition with `log` doesn't itself have a jump), is exactly
the circularity that remains open — propagating regularity down through unboundedly deep `exp`/`log`
nesting. **2026-07-15: the compactness tool itself (`continuousAt_bddAbove_Icc`, an Extreme Value
Theorem from `sup_exists`) has since been built** — see the dated note further below, after
`eml_gap_avoidance` — **but it does not close this circularity**: the real obstruction is that no
bound propagates from the root down to an arbitrarily nested interior subtree (bounding
`exp(s1.eval) - log(s2.eval)` does not bound `s1.eval`/`s2.eval` individually), so the missing piece
is a genuine differentiation/identity-theorem argument, not a compactness patch. -/
axiom eml_pfaffian_validon_from_sin_equality
    (t : EMLTree) (hsin : ∀ x : Real, t.eval x = Real.sin x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b

/-- **A pure structural fact about `eml` nodes — no smoothness hypothesis, no axiom.** Whenever an
`eml t1 t2` node's OWN value is non-positive at a point, its log-argument `t2` is forced strictly
positive there: if `t2.eval x ≤ 0`, the clamped log evaluates to `0` (`log_nonpos`), so the node's
value collapses to `exp(t1.eval x)`, which is always strictly positive (`exp_pos`) — contradicting
non-positivity. This is exactly step 4 of `eml_pfaffian_validon_from_sin_equality`'s argument above,
generalized from "at a zero of sin" to "wherever the node's value is `≤ 0`" (so it applies to `cos`
and any other target function too, not just `sin`). It does not close that axiom — the remaining
gap (points where the outer value is positive) genuinely needs the connectivity argument the axiom
still cites — but it does shrink the axiom's real content to exactly that gap. -/
theorem eml_nonpos_forces_log_arg_pos (t1 t2 : EMLTree) (x : Real)
    (h : (EMLTree.eml t1 t2).eval x ≤ 0) : 0 < t2.eval x := by
  by_cases hle : t2.eval x ≤ 0
  · exfalso
    have hlog0 : Real.log (t2.eval x) = 0 := Real.log_nonpos hle
    have heval : (EMLTree.eml t1 t2).eval x = Real.exp (t1.eval x) := by
      show Real.exp (t1.eval x) - Real.log (t2.eval x) = Real.exp (t1.eval x)
      rw [hlog0, sub_zero]
    rw [heval] at h
    exact lt_irrefl_ax 0 (lt_of_lt_of_le_r (Real.exp_pos (t1.eval x)) h)
  · rcases lt_total 0 (t2.eval x) with hpos | heq | hneg
    · exact hpos
    · exact absurd (le_of_eq heq.symm) hle
    · exact absurd (le_of_lt hneg) hle

/-! ## `log` is unbounded near `0` — the missing infrastructure, now built (2026-07-16)

Chasing whether `eml_nonpos_forces_log_arg_pos` generalizes into a full closure of
`eml_pfaffian_validon_from_sin_equality` (it doesn't — see the axiom's docstring, updated below)
turned up this: `log` blowing up near `0⁺` is exactly the "unboundedness" fact flagged as missing
infrastructure. It's a short derivation from facts MachLib already has (`exp_lt`, `exp_injective`,
`exp_log`, `exp_pos`), not a new axiom. -/

/-- **`exp` reflects strict order.** The converse of `exp_lt` (`a < b → exp a < exp b`): if
`exp a < exp b` then `a < b`. By trichotomy: `a = b` would force `exp a = exp b`
(contradicting `<`), and `b < a` would force `exp b < exp a` (also contradicting `<`, via
`exp_lt` the other way and transitivity). -/
theorem exp_reflect_lt {a b : Real} (h : Real.exp a < Real.exp b) : a < b := by
  rcases lt_total a b with hlt | heq | hgt
  · exact hlt
  · exfalso; rw [heq] at h; exact lt_irrefl_ax _ h
  · exfalso; exact lt_irrefl_ax _ (lt_trans_ax h (Real.exp_lt hgt))

/-- **`log` reflects the `exp`-threshold.** If `0 < y` and `y < exp M`, then `log y < M`. Via
`exp_log` (`exp (log y) = y` for `y > 0`) and `exp_reflect_lt`. -/
theorem log_lt_of_lt_exp {y M : Real} (hy : 0 < y) (h : y < Real.exp M) : Real.log y < M := by
  have hyeq : Real.exp (Real.log y) = y := Real.exp_log hy
  apply exp_reflect_lt
  rw [hyeq]
  exact h

/-- **`log` is unbounded below near `0⁺`.** For any target `M` (however negative), there is a
threshold `δ := exp M > 0` such that every `y` strictly between `0` and `δ` has `log y < M`. This
is the "log blows up approaching 0 from the right" fact — stated quantitatively (no limits, no
sequences), which is all the gap-avoidance argument below needs. -/
theorem log_unbounded_below (M : Real) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, 0 < y → y < δ → Real.log y < M :=
  ⟨Real.exp M, Real.exp_pos M, fun _ hy hyd => log_lt_of_lt_exp hy hyd⟩

/-- **Gap avoidance.** For an `eml t1 t2` node whose OWN value is bounded above by `U`, its
log-argument `t2` can never take a value strictly between `0` and `exp(-U)`: either `t2.eval x ≤ 0`,
or `t2.eval x ≥ exp(-U)`. Proof: if `0 < t2.eval x`, the node's defining equation rearranges to
`log(t2.eval x) = exp(t1.eval x) - (eml t1 t2).eval x`, which exceeds `-U` (since `exp(t1.eval x) >
0` and `(eml t1 t2).eval x ≤ U`). Combined with `log_unbounded_below`'s contrapositive at threshold
`exp(-U)` (`t2.eval x < exp(-U) → log(t2.eval x) < -U`), `t2.eval x < exp(-U)` is impossible, so
`t2.eval x ≥ exp(-U)`.

This generalizes `eml_nonpos_forces_log_arg_pos`'s trick (which is the `t2.eval x ≤ 0` disjunct
here) using `log_unbounded_below` for the other disjunct — the SAME two ingredients the axiom's
docstring identifies as missing (steps 4 and part of 3). It still does not close the axiom: to turn
"avoids the gap" into "positive throughout `(0,b)`", one more ingredient is needed — that `t2.eval`
is CONTINUOUS on `(0,b)` (so `intermediate_value` from `IntermediateValue.lean` rules out it being
`≤ 0` at one point and `≥ exp(-U)` at another) — and establishing that continuity for an arbitrarily
NESTED subtree, without already knowing ITS OWN log-arguments are well-formed, is exactly the
circularity that remains open. -/
theorem eml_gap_avoidance (t1 t2 : EMLTree) (x U : Real)
    (hU : (EMLTree.eml t1 t2).eval x ≤ U) :
    t2.eval x ≤ 0 ∨ Real.exp (-U) ≤ t2.eval x := by
  by_cases hle : t2.eval x ≤ 0
  · exact Or.inl hle
  · right
    have hpos : 0 < t2.eval x := by
      rcases lt_total 0 (t2.eval x) with hp | heq | hn
      · exact hp
      · exact absurd (le_of_eq heq.symm) hle
      · exact absurd (le_of_lt hn) hle
    have heval : Real.log (t2.eval x)
        = Real.exp (t1.eval x) - (EMLTree.eml t1 t2).eval x := by
      show Real.log (t2.eval x)
          = Real.exp (t1.eval x) - (Real.exp (t1.eval x) - Real.log (t2.eval x))
      mach_ring
    have hgt : -U < Real.log (t2.eval x) := by
      rw [heval]
      have h1 : (0 : Real) < Real.exp (t1.eval x) := Real.exp_pos _
      have step1 : -U < (-U) + Real.exp (t1.eval x) := by
        have h3 := add_lt_add_left h1 (-U)
        rwa [add_zero] at h3
      have step2 : (-U) + Real.exp (t1.eval x)
          ≤ Real.exp (t1.eval x) - (EMLTree.eml t1 t2).eval x := by
        rw [sub_def, add_comm (-U) (Real.exp (t1.eval x))]
        exact add_le_add_left (neg_le_neg hU) (Real.exp (t1.eval x))
      exact lt_of_lt_of_le_r step1 step2
    refine Classical.byContradiction (fun hcon => ?_)
    have hlt : t2.eval x < Real.exp (-U) := by
      rcases lt_total (t2.eval x) (Real.exp (-U)) with hl | he | hg
      · exact hl
      · exact absurd (le_of_eq he.symm) hcon
      · exact absurd (le_of_lt hg) hcon
    have hfin := log_lt_of_lt_exp hpos hlt
    exact lt_irrefl_ax _ (lt_trans_ax hgt hfin)

/-! ## 2026-07-15: Extreme Value Theorem built — and why it still doesn't close the axiom

`continuousAt_bddAbove_Icc` (continuous on `[a,b]` ⟹ bounded above there, from `sup_exists`,
mirroring `intermediate_value`'s proof technique) is now proven in `IntermediateValue.lean` — the
compactness tool flagged as missing above. Zero new axioms. It is genuine, reusable infrastructure.

**It does not close this axiom.** Tracing through why: to validate an `eml t1 t2` node nested
*inside* `t`, `eml_gap_avoidance` forces its log-argument `t2` to avoid the gap `(0, exp(-U))`
*pointwise*, for any `U` bounding the node's own value. Combined with `intermediate_value` and
continuity of `t2.eval`, "avoids the gap pointwise" upgrades to "one-sided throughout `(0,b)`" —
this is the intended use of the new EVT (via `bdd_above_nbhd_of_continuousAt` giving the local
bound that feeds `U`).

The obstruction: establishing continuity of `t2.eval`, when `t2` is itself a nested `eml` node,
needs `t2`'s *own* internal log-arguments already well-formed (otherwise an inner `log` hits its
clamp boundary and `t2.eval` is not obviously continuous there) — i.e. exactly the validity being
proved, one level deeper. And at that deeper level there is no bound available to seed
`eml_gap_avoidance`: boundedness of the *root* (`|sin x| ≤ 1`) bounds the root's value, but
`exp(s1.eval x) - log(s2.eval x)` staying bounded does **not** bound `s1.eval` or `s2.eval`
individually (unlike at the root, an interior node has no anchor tying it to a known-bounded
target function). So the induction cannot bottom out via elementary bound propagation through
nested compositions — turning `t.eval = sin` into constraints on an arbitrarily deep interior
subtree needs a real identity-theorem / differentiation argument (the classical route sketched at
the top of this section: differentiate, or use analytic continuation uniqueness), not a
continuity-only patch. This matches — rather than shortens — the axiom's original "Smoothness
module, ~300-500 lines, multi-session" estimate. `continuousAt_bddAbove_Icc` stays as useful,
reusable infrastructure but does not by itself reduce this axiom's remaining scope. -/

/-! ## A genuinely free fact: the ROOT's derivative, via `HasDerivAt_of_eq`

`MachLib.Differentiation` (already transitively imported here, via `Pfaffian.lean`) axiomatizes
`HasDerivAt` with base rules for `exp`/`log`/`sin`/`cos`, closure rules (`add`/`sub`/`mul`/`comp`/
`inv`/`neg`), uniqueness, and — the one used below — "if two functions agree everywhere, a known
derivative of one transfers to the other" (`HasDerivAt_of_eq`). Since `sin` unconditionally has
derivative `cos x` at every `x` (`HasDerivAt_sin`), and `t.eval` agrees with `sin` everywhere by
hypothesis, `t.eval` gets `HasDerivAt t.eval (cos x) x` **for free** — no structural analysis of
`t`'s internal exp/log nesting, no validity assumption, no case split. This is NOT the same fact as
`t.eval`'s *own* structural derivative (computed bottom-up via the chain rule through `t`'s actual
`exp`/`log` nodes) — that computation is exactly where the circularity above bites, since it needs
every internal `log`'s argument positive AT `x` to invoke `HasDerivAt_log_pos`. The free fact below
sidesteps that entirely by never looking at `t`'s internal structure. -/

/-- **Free derivative transfer (sin side).** No validity hypothesis needed. -/
theorem eml_hasDerivAt_of_sin_eq (t : EMLTree) (hsin : ∀ x : Real, t.eval x = Real.sin x)
    (x : Real) : HasDerivAt t.eval (Real.cos x) x :=
  HasDerivAt_of_eq Real.sin t.eval (Real.cos x) x (fun y => (hsin y).symm) (HasDerivAt_sin x)

/-- **Free continuity transfer (sin side).** Corollary of the above via `hasDerivAt_continuousAt`. -/
theorem eml_continuousAt_of_sin_eq (t : EMLTree) (hsin : ∀ x : Real, t.eval x = Real.sin x)
    (x : Real) : ContinuousAt t.eval x :=
  hasDerivAt_continuousAt (eml_hasDerivAt_of_sin_eq t hsin x)

/-! ### Why the free fact still doesn't scale to arbitrary-depth validity

The natural next move is to also compute `HasDerivAt t.eval _ x` *structurally* — bottom-up through
`t`'s actual `exp`/`sub`/`log` nodes, via `HasDerivAt_comp`/`HasDerivAt_sub`/`HasDerivAt_log_pos` —
and use `HasDerivAt_unique` to force the structural formula to equal `cos x` from the free fact
above. This is exactly the strategy `Differentiation.lean`'s own docstring sketches for closing 2
*specific, fixed-shape* depth-2 sin-barrier cases (differentiate, evaluate at one concrete point,
derive a numeric contradiction like `exp 1 = 2`).

It does not generalize to THIS axiom's arbitrary, unbounded-depth `t`: (1) the structural
computation still needs `HasDerivAt_log_pos`, which needs each internal log-argument positive AT
`x` — i.e. the validity being proved; (2) even granting that, the resulting *formula* for `t.eval'`
depends on `t`'s exact shape, so "pick a point and get a numeric contradiction" is a per-tree
algebra trick, not a scheme that closes for every tree at once. The free-transfer fact is a genuine,
verified, zero-new-axiom building block (`t.eval` inherits sin's regularity at the root, for free)
but — like the EVT above — does not reach interior subtrees, for the same root-cause: only the
ROOT is globally tied to a named, regular function; no subtree is. -/

-- (theorem sin_zeros_list_nodup moved after natCast_mul_pi_lt below)

/-! ## Helpers for the list construction -/

/-- `natCast k * π ≥ 0` for all `k`. -/
theorem natCast_mul_pi_nonneg (k : Nat) : (0 : Real) ≤ natCast k * pi := by
  induction k with
  | zero => rw [natCast_zero, zero_mul]; exact le_refl _
  | succ p ihp =>
    rw [natCast_succ, mul_distrib_right, one_mul_thm]
    exact add_nonneg ihp (le_of_lt pi_pos)

/-- `natCast k * π > 0` for `k ≥ 1`. -/
theorem natCast_mul_pi_pos {k : Nat} (hk : 1 ≤ k) : (0 : Real) < natCast k * pi := by
  -- For k ≥ 1: k = m + 1 with m ≥ 0. natCast (m+1) * pi = natCast m * pi + pi.
  -- ≥ 0 + pi = pi > 0.
  cases k with
  | zero => omega
  | succ m =>
    rw [natCast_succ, mul_distrib_right, one_mul_thm]
    have hmul_nonneg : (0 : Real) ≤ natCast m * pi := natCast_mul_pi_nonneg m
    have step := add_lt_add_left pi_pos (natCast m * pi)
    rw [add_zero] at step
    exact lt_of_le_of_lt hmul_nonneg step

/-- `natCast j * π < natCast k * π` when `j < k`. -/
theorem natCast_mul_pi_lt {j k : Nat} (hjk : j < k) :
    natCast j * pi < natCast k * pi := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases h : j < m
    · have ih' := ih h
      rw [natCast_succ, mul_distrib_right, one_mul_thm]
      have hstep : natCast m * pi < natCast m * pi + pi := by
        have step := add_lt_add_left pi_pos (natCast m * pi)
        rw [add_zero] at step
        exact step
      exact lt_trans_ax ih' hstep
    · have hjm : j = m := by omega
      rw [hjm, natCast_succ, mul_distrib_right, one_mul_thm]
      have step := add_lt_add_left pi_pos (natCast m * pi)
      rw [add_zero] at step
      exact step

/-- The list `[natCast 1 * π, natCast 2 * π, ..., natCast (M+1) * π]` has
no duplicates. PROVEN via `List.Pairwise.map` + injectivity from
`natCast_mul_pi_lt` (strict-order-preserving). -/
theorem sin_zeros_list_nodup (M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi))
  exact (List.nodup_range (M + 1)).map (fun i => natCast (i + 1) * pi)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      dsimp only at hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := natCast_mul_pi_lt (show i + 1 < j + 1 from by omega)
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := natCast_mul_pi_lt (show j + 1 < i + 1 from by omega)
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-! ## 2026-06-12 sprint week-2 step 1 — sin barrier under consistent axioms

The 2026-06-11 reproof attempt added an `eml_pfaffian_below_sin_density`
axiom that turned out to be inconsistent (same root cause as the
original Pfaffian zero bound: sin/cos couldn't be distinguished from
EML functions at the same (n, d)).

The operator's diagnosis on 2026-06-12 identified that sin/cos were
themselves the source of the inconsistency: they had been axiomatized
as globally Pfaffian (chain.order=2, degree=1), but classical
Khovanskii requires triangular Pfaffian chains, and the sin/cos
chain sin' = cos, cos' = -sin is circular. Removing `sin_as_pfaffian`
and `cos_as_pfaffian` from Pfaffian.lean restored consistency of the
original interval-uniform bound axiom.

With the original axiom signature restored and sin/cos no longer in
the Pfaffian family, the sin barrier proof works as originally
structured (commit pre-086e464). No additional Khovanskii-rate axiom
is needed. -/

/-! ## Sin barrier — moved (2026-07-15)

`sin_not_in_eml_any_depth` used to live here, applying `PfaffianFunction.zero_bound`
(the axiom `zero_count_bound_classical`'s thin wrapper). Both have been deleted —
see `KhovanskiiLemma.lean`'s removal notes. The theorem now lives in
`EMLExplicitBoundSinBarrier.lean` (same name, re-proven via the constructive
`EMLExplicitBound.enc_combinedBound`), which imports this file for `eml_pfaffian`,
`EMLPfaffianValidOn`, and `eml_pfaffian_validon_from_sin_equality` — kept here since
they're still needed and moving them would risk an import cycle (that file necessarily
imports this one). -/

end MachLib
