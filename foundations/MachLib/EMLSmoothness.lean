import MachLib.EMLPfaffian
import MachLib.MultiVarTwoExpSum
import MachLib.WronskianProportional

/-!
# Differentiability away from log-clamp crossings

Toward closing `eml_pfaffian_validon_from_sin_equality`/`_from_cos_equality` (see the dated notes
in `EMLPfaffian.lean` after `eml_gap_avoidance` and `eml_continuousAt_of_sin_eq`). Rounds 3
(compactness/IVT) and 4 (free derivative transfer at the root) both found the same obstruction:
nothing ties an INTERIOR subtree back to a known-bounded/regular target function the way the ROOT
is tied to `sin`/`cos`.

This file attacks the problem from a different angle: instead of needing FULL validity (strict
positivity of a log-argument throughout an interval) to get continuity of an `eml` node, it's
enough to avoid landing EXACTLY on the clamp boundary (`t2.eval x ≠ 0`) at the point in question —
`MachLib.Real.log` is differentiable on EITHER side of `0` (`HasDerivAt_log_pos` for `>0`, the newly
derived `HasDerivAt_log_neg` for `<0`), just via different rules. This is a strictly WEAKER, purely
LOCAL, structural condition (`EMLNoCrossingAt`) than `EMLPfaffianValidOn`, provable by ordinary
structural induction with NO circularity (a subtree's own `EMLNoCrossingAt` never needs its
sibling's or parent's validity).

**Honest scope:** this does not, by itself, close either axiom — see the dated note at the bottom.
It sharpens exactly where the remaining difficulty lives: not "is `t2.eval` continuous" (answered
here, for free, away from crossings) but "does `t2.eval` ever actually reach `≤ 0` at all" (the
`EMLNoCrossingAt`-violating case), which still needs a global argument.
-/

namespace MachLib

open Real
open MachLib.MultiVarMod.TwoExp (neg_lt_neg)

/-- No internal `eml` node's log-argument is EXACTLY `0` at `x`. Strictly WEAKER than
`EMLPfaffianValidOn s a b` (which needs strict POSITIVITY of every log-argument throughout an
*interval*): this only rules out landing on log's clamp boundary at *this one point*, and never
mentions siblings/ancestors — a genuinely local, non-circular structural condition. -/
def EMLNoCrossingAt : EMLTree → Real → Prop
  | .const _,   _ => True
  | .var,       _ => True
  | .eml t1 t2, x => EMLNoCrossingAt t1 x ∧ EMLNoCrossingAt t2 x ∧ t2.eval x ≠ 0

/-- An `eml t1 t2` node is differentiable at `x`, given its children are and its own log-argument
isn't exactly `0` there — via `HasDerivAt_log_pos` (argument `> 0`) or `HasDerivAt_log_neg`
(argument `< 0`), whichever side of the clamp boundary applies. -/
theorem eml_hasDerivAt_away_from_crossing {t1 t2 : EMLTree} {x a b : Real}
    (h1 : HasDerivAt t1.eval a x) (h2 : HasDerivAt t2.eval b x) (hne : t2.eval x ≠ 0) :
    ∃ c : Real, HasDerivAt (EMLTree.eml t1 t2).eval c x := by
  have hexp : HasDerivAt (fun y => Real.exp (t1.eval y)) (Real.exp (t1.eval x) * a) x :=
    HasDerivAt_comp Real.exp t1.eval a (Real.exp (t1.eval x)) x h1 (HasDerivAt_exp _)
  rcases lt_total (t2.eval x) 0 with hlt | heq | hgt
  · have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (0 * b) x :=
      HasDerivAt_comp Real.log t2.eval b 0 x h2 (HasDerivAt_log_neg hlt)
    exact ⟨_, HasDerivAt_sub _ _ _ _ x hexp hlog⟩
  · exact absurd heq hne
  · have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (1 / t2.eval x * b) x :=
      HasDerivAt_comp Real.log t2.eval b (1 / t2.eval x) x h2 (HasDerivAt_log_pos _ hgt)
    exact ⟨_, HasDerivAt_sub _ _ _ _ x hexp hlog⟩

/-- **Differentiability away from crossings.** Any `EMLTree` is differentiable at `x` provided no
internal log-argument lands exactly on `0` there — by ordinary structural induction, no circularity
(the base cases `const`/`var` are unconditionally differentiable; the `eml` step only needs its
immediate children's differentiability, from the induction hypothesis, plus the local
`t2.eval x ≠ 0` side condition). -/
theorem eml_hasDerivAt_of_no_crossing (s : EMLTree) (x : Real) (h : EMLNoCrossingAt s x) :
    ∃ c : Real, HasDerivAt s.eval c x := by
  induction s with
  | const c => exact ⟨0, HasDerivAt_const c x⟩
  | var => exact ⟨1, HasDerivAt_id x⟩
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨h1, h2, hne⟩ := h
    obtain ⟨a, ha⟩ := ih1 h1
    obtain ⟨b, hb⟩ := ih2 h2
    exact eml_hasDerivAt_away_from_crossing ha hb hne

/-- Corollary: continuity away from crossings, via `hasDerivAt_continuousAt`. -/
theorem eml_continuousAt_of_no_crossing (s : EMLTree) (x : Real) (h : EMLNoCrossingAt s x) :
    ContinuousAt s.eval x :=
  (eml_hasDerivAt_of_no_crossing s x h).elim (fun _ hc => hasDerivAt_continuousAt hc)

/-! ## `log` is unbounded ABOVE too — the mirror of `log_unbounded_below`

`log_unbounded_below` (`EMLPfaffian.lean`) says `log` blows up to `-∞` as its argument `→ 0⁺`. The
blow-up-propagation argument below also needs the mirror fact: `log` blows up to `+∞` as its
argument `→ +∞`. Same derivation shape as `log_lt_of_lt_exp`/`log_unbounded_below`, just with the
inequality reversed. -/

/-- **`log` is unbounded above.** For any target `M`, there is a threshold `δ := exp M > 0` such
that every `y > δ` has `log y > M`. -/
theorem log_unbounded_above (M : Real) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, δ < y → M < Real.log y := by
  refine ⟨Real.exp M, Real.exp_pos M, fun y hy => ?_⟩
  have hypos : (0 : Real) < y := lt_trans_ax (Real.exp_pos M) hy
  have heq : Real.exp (Real.log y) = y := Real.exp_log hypos
  apply exp_reflect_lt
  rw [heq]
  exact hy

/-! ## Depth-2 blow-up: a crossing forces the composition arbitrarily low

The mechanism `eml_gap_avoidance` already uses (an `eml` node's own value bounded above forces its
log-argument away from a small gap, via `exp ≥ 0` absorbing the OTHER child) composes: if `s3`
(two levels down) takes a small enough positive value at `y`, `eml s2 s3` is forced arbitrarily
LARGE at `y` (again via `exp(s2.eval y) ≥ 0`, regardless of `s2`), and THEN `log` of that large
value is forced arbitrarily large too, forcing `eml t1 (eml s2 s3)` arbitrarily NEGATIVE at `y` —
regardless of `t1`'s value there, chosen pointwise. Two nested applications of `log`'s
unboundedness. -/

/-- **Depth-2 blow-up.** For any target `L`, there is a threshold `δ > 0` (depending on `y`'s
already-fixed `t1.eval y`/`s2.eval y`, chosen internally) such that `s3.eval y` landing in
`(0, δ)` forces `eml t1 (eml s2 s3)` below `L` at `y` — regardless of `t1` or `s2`'s actual
values there. -/
theorem eml_depth2_blowup (t1 s2 s3 : EMLTree) (y L : Real) :
    ∃ δ : Real, 0 < δ ∧ (0 < s3.eval y → s3.eval y < δ →
      (EMLTree.eml t1 (EMLTree.eml s2 s3)).eval y < L) := by
  obtain ⟨δ2, hδ2pos, hM2⟩ := log_unbounded_above (Real.exp (t1.eval y) - L + 1)
  obtain ⟨δ1, hδ1pos, hM1⟩ := log_unbounded_below (-δ2)
  refine ⟨δ1, hδ1pos, fun hpos hlt => ?_⟩
  have hlog3 : Real.log (s3.eval y) < -δ2 := hM1 (s3.eval y) hpos hlt
  have hexp_pos : (0 : Real) < Real.exp (s2.eval y) := Real.exp_pos _
  have hstep1 : δ2 < -Real.log (s3.eval y) := by
    have h2 := neg_lt_neg hlog3
    rwa [show -(-δ2) = δ2 from by mach_ring] at h2
  have hstep2 : -Real.log (s3.eval y) < Real.exp (s2.eval y) - Real.log (s3.eval y) := by
    have h2 := add_lt_add_left hexp_pos (-Real.log (s3.eval y))
    rwa [add_zero,
      show -Real.log (s3.eval y) + Real.exp (s2.eval y)
        = Real.exp (s2.eval y) - Real.log (s3.eval y)
        from by mach_mpoly [Real.log (s3.eval y), Real.exp (s2.eval y)]] at h2
  have ht2gap : δ2 < (EMLTree.eml s2 s3).eval y := by
    show δ2 < Real.exp (s2.eval y) - Real.log (s3.eval y)
    exact lt_trans_ax hstep1 hstep2
  have hlog2 : Real.exp (t1.eval y) - L + 1 < Real.log ((EMLTree.eml s2 s3).eval y) :=
    hM2 ((EMLTree.eml s2 s3).eval y) ht2gap
  show Real.exp (t1.eval y) - Real.log ((EMLTree.eml s2 s3).eval y) < L
  have h2 := neg_lt_neg hlog2
  have h3 := add_lt_add_left h2 (Real.exp (t1.eval y))
  rw [show Real.exp (t1.eval y) + -(Real.log ((EMLTree.eml s2 s3).eval y))
        = Real.exp (t1.eval y) - Real.log ((EMLTree.eml s2 s3).eval y)
        from by mach_mpoly [Real.exp (t1.eval y), Real.log ((EMLTree.eml s2 s3).eval y)],
      show Real.exp (t1.eval y) + -(Real.exp (t1.eval y) - L + 1) = L - 1
        from by mach_mpoly [Real.exp (t1.eval y), L]] at h3
  have hlt1 : L - 1 < L := by
    have h4 := add_lt_add_left (neg_neg_of_pos zero_lt_one_ax) L
    rwa [add_zero, show L + -1 = L - 1 from by mach_ring] at h4
  exact lt_trans_ax h3 hlt1

/-! ## Why this does NOT generalize to arbitrary depth (a precise correction)

The natural next step is to chase this mechanism up an ARBITRARY root-to-offender path (a sequence
of "the offender's ancestor is the LEFT child" vs "... is the RIGHT child" steps) and hope it
propagates all the way to the root, where `|sin| ≤ 1` gives the final contradiction. Tracing the
two step types against the two "controllable" states shows it does **not**, in general.

Track a hole value `v` that is *controllable* (for any target, some threshold on `v` achieves it)
in one of two states: `A` (`v` can be forced arbitrarily LARGE) or `B` (`v` can be forced
arbitrarily NEGATIVE — this is where `eml_depth2_blowup`'s intermediate `t2 = eml s2 s3` value
ends up). Composing one more ancestor step:

- State `A` through a LEFT step (`exp v − log sib`): `exp v → +∞` too — **stays `A`**.
- State `A` through a RIGHT step (`exp sib − log v`): `log v → +∞` — **flips to `B`**.
- State `B` through a LEFT step (`exp v − log sib`): `exp v → 0` (bounded, `exp` never blows up
  downward) — the composition CONVERGES to the fixed value `−log sib`. **Dies** (no longer
  unbounded).
- State `B` through a RIGHT step (`exp sib − log v`): once `v` is negative enough, `log v` is
  CLAMPED to exactly `0` regardless of magnitude, so the composition is the fixed constant
  `exp sib`. **Dies** too.

So `B` always dies after exactly one more step, whichever kind. The mandatory first step
(offender → immediate parent) is always a RIGHT step (an offender is by definition someone's
log-argument) and lands in state `A`. From there the signal survives any number of further LEFT
steps, survives a first subsequent RIGHT step (flipping to `B`), and then dies on the very next
step after that — REGARDLESS of whether that step lands on the root or not. Concretely: a
"right-right-right" chain (an offender three log-slots below the root, nothing else) does **not**
close, because the third step lands on a fixed constant, not a contradiction — confirmed by hand
above and consistent with `eml_depth2_blowup` being exactly the "right, right, stop — the second
right IS the root" case, the longest chain this mechanism can certify.

**Consequence:** this is not "more elementary work will eventually get there" — it's a structural
reach limit. Elementary bound/blow-up chasing genuinely cannot certify validity for an offender
whose root-to-offender path has two or more RIGHT turns separated by anything (or more than two
RIGHT turns at all) without the LAST one landing exactly on the root. Since the axiom quantifies
over an arbitrary `t` (any left/right shape is possible), full closure needs a different technique
— most plausibly the differentiate-and-compare-derivatives route `Differentiation.lean` already
sketches for fixed small cases, generalized via genuine calculus (not value-bound chasing), or a
repurposing of the existing Khovanskii/Wronskian rigidity machinery built for the (different)
zero-counting problem. Not attempted here. -/

/-! ## A genuinely different mechanism: linear ODE / integrating factor (not blow-up)

Differentiating `t.eval = sin` against the structural chain-rule derivative of an `eml t1 t2` node
gives a genuine LINEAR ODE for the log-argument: `t2' = t2 · Q` with `Q := exp(t1)·t1' − cos`. `Q`
has an EXPLICIT antiderivative built from existing primitives — `A := exp(t1) − sin` satisfies
`A' = Q` exactly — giving an EXPLICIT, always-positive integrating factor `E := exp(A)`. Wherever
the ODE holds, `t2/E` is a CONSTANT (via the same Wronskian-vanishing + MVT-constancy technique
`WronskianProportional.lean` already uses for a different purpose), i.e. `t2 = k · E` exactly.

Unlike the value-blow-up (`eml_depth2_blowup`) and derivative-blow-up attempts above, this does NOT
hit a reach limit or an indeterminate form when pushed to a deeper offender: the SAME technique
applies one level further using the now-EXPLICIT `t2 = k·E`, since `E`'s own derivative is
computable exactly (no asymptotics), yielding a second linear ODE for the next level down with its
own explicit integrating factor (still always positive, since it's `exp` of *something* at every
level) — recursing cleanly to arbitrary depth. See the round-8 note in memory
(`machlib-khovanskii-axiom-frontier.md`) for the full argument, including how the constant-ratio
fact combines with a minimal-violation point (via completeness) to force a contradiction. This
section builds the one genuinely reusable piece: the general "shared linear ODE ⟹ constant ratio"
lemma, not yet specialized to EML trees. -/

/-- **Constant ratio from a shared linear ODE.** If `f` and `E` both satisfy the SAME linear ODE
`y' = y · Q` throughout `[p,q]`, and `E` never vanishes there, `f/E` is a CONSTANT throughout —
i.e. `f = k · E` exactly, for a single `k`. Specializes `WronskianProportional.phi_deriv_zero` (the
Wronskian `f'·E − f·E' = f·Q·E − f·E·Q` vanishes identically, since both sides use the literal same
`Q`) combined with `eq_endpoints_of_deriv_zero` (MVT-constancy). No analyticity needed. -/
theorem const_ratio_of_shared_ode (f E Q : Real → Real) (p q : Real) (hpq : p < q)
    (hfderiv : ∀ x, p ≤ x → x ≤ q → HasDerivAt f (f x * Q x) x)
    (hEderiv : ∀ x, p ≤ x → x ≤ q → HasDerivAt E (E x * Q x) x)
    (hEne : ∀ x, p ≤ x → x ≤ q → E x ≠ 0) :
    ∃ k : Real, ∀ x, p ≤ x → x ≤ q → f x = k * E x := by
  have hφ0 : ∀ c, p ≤ c → c ≤ q → HasDerivAt (fun y => f y * (1 / E y)) 0 c := by
    intro c hc1 hc2
    exact phi_deriv_zero f E (f c * Q c) (E c * Q c) c (hEne c hc1 hc2)
      (hfderiv c hc1 hc2) (hEderiv c hc1 hc2) (by mach_mpoly [f c, E c, Q c])
  refine ⟨f p * (1 / E p), fun x hx1 hx2 => ?_⟩
  rcases lt_total p x with hlt | heq | hgt
  · have heqends : f p * (1 / E p) = f x * (1 / E x) :=
      eq_endpoints_of_deriv_zero (fun y => f y * (1 / E y)) p x hlt
        (fun c hc1 hc2 => hφ0 c hc1 (le_trans hc2 hx2))
    have hEx_ne : E x ≠ 0 := hEne x hx1 hx2
    have h2 : f p * (1 / E p) * E x = f x * (1 / E x) * E x := by rw [heqends]
    rw [mul_assoc (f x) (1 / E x) (E x), mul_comm (1 / E x) (E x),
        mul_inv (E x) hEx_ne, mul_one_ax] at h2
    exact h2.symm
  · rw [← heq]
    have hEp_ne : E p ≠ 0 := hEne p (le_refl p) (le_of_lt hpq)
    rw [mul_assoc (f p) (1 / E p) (E p), mul_comm (1 / E p) (E p),
        mul_inv (E p) hEp_ne, mul_one_ax]
  · exact absurd (lt_of_lt_of_le hgt hx1) (lt_irrefl_ax x)

/-! ## Depth-1 instantiation: the explicit integrating factor and the ODE for `t2`

For `t = eml t1 t2` with `t.eval = sin`, the log-argument `t2` satisfies (wherever `t2 > 0`, so the
structural chain rule applies to the `log` branch) the linear ODE `t2' = t2 · Q₁` with
`Q₁ := exp(t1)·t1' − cos`. `Q₁`'s explicit antiderivative `A₁ := exp(t1) − sin` gives the explicit,
always-positive integrating factor `E₁ := exp(A₁)`. -/

/-- The explicit depth-1 integrating factor's own derivative, matching the `E' = E·Q` shape
`const_ratio_of_shared_ode` needs — built purely from `t1`'s derivative, no `t2` involved at all. -/
theorem eml_depth1_E_deriv {t1 : EMLTree} {x a : Real} (h1 : HasDerivAt t1.eval a x) :
    HasDerivAt (fun y => Real.exp (Real.exp (t1.eval y) - Real.sin y))
      (Real.exp (Real.exp (t1.eval x) - Real.sin x) *
        (Real.exp (t1.eval x) * a - Real.cos x)) x := by
  have hexp : HasDerivAt (fun y => Real.exp (t1.eval y)) (Real.exp (t1.eval x) * a) x :=
    HasDerivAt_comp Real.exp t1.eval a (Real.exp (t1.eval x)) x h1 (HasDerivAt_exp _)
  have hA : HasDerivAt (fun y => Real.exp (t1.eval y) - Real.sin y)
      (Real.exp (t1.eval x) * a - Real.cos x) x :=
    HasDerivAt_sub _ _ _ _ x hexp (HasDerivAt_sin x)
  exact HasDerivAt_comp Real.exp (fun y => Real.exp (t1.eval y) - Real.sin y)
    (Real.exp (t1.eval x) * a - Real.cos x) (Real.exp (Real.exp (t1.eval x) - Real.sin x))
    x hA (HasDerivAt_exp _)

/-- The structural derivative of `eml t1 t2` on the branch where `t2.eval x > 0`, EXPLICIT (not
existential) — the exact formula needed to combine with the free `cos x` fact via
`HasDerivAt_unique`. -/
theorem eml_hasDerivAt_pos_branch {t1 t2 : EMLTree} {x a b : Real}
    (h1 : HasDerivAt t1.eval a x) (h2 : HasDerivAt t2.eval b x) (hpos : 0 < t2.eval x) :
    HasDerivAt (EMLTree.eml t1 t2).eval
      (Real.exp (t1.eval x) * a - 1 / t2.eval x * b) x := by
  have hexp : HasDerivAt (fun y => Real.exp (t1.eval y)) (Real.exp (t1.eval x) * a) x :=
    HasDerivAt_comp Real.exp t1.eval a (Real.exp (t1.eval x)) x h1 (HasDerivAt_exp _)
  have hlog : HasDerivAt (fun y => Real.log (t2.eval y)) (1 / t2.eval x * b) x :=
    HasDerivAt_comp Real.log t2.eval b (1 / t2.eval x) x h2 (HasDerivAt_log_pos _ hpos)
  exact HasDerivAt_sub _ _ _ _ x hexp hlog

/-- **The depth-1 ODE.** If `t = eml t1 t2` agrees with `sin` everywhere and `t2.eval x > 0`,
`t2`'s derivative at `x` is FORCED to be `t2.eval x * Q₁ x` — combining the free root derivative
(`eml_hasDerivAt_of_sin_eq`, unconditional) with the structural positive-branch derivative
(`eml_hasDerivAt_pos_branch`) via `HasDerivAt_unique`. -/
theorem eml_depth1_t2_ode {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x)
    {x a b : Real} (h1 : HasDerivAt t1.eval a x) (h2 : HasDerivAt t2.eval b x)
    (hpos : 0 < t2.eval x) :
    HasDerivAt t2.eval (t2.eval x * (Real.exp (t1.eval x) * a - Real.cos x)) x := by
  have hfree : HasDerivAt (EMLTree.eml t1 t2).eval (Real.cos x) x :=
    eml_hasDerivAt_of_sin_eq (EMLTree.eml t1 t2) hsin x
  have hstruct : HasDerivAt (EMLTree.eml t1 t2).eval
      (Real.exp (t1.eval x) * a - 1 / t2.eval x * b) x :=
    eml_hasDerivAt_pos_branch h1 h2 hpos
  have heq : Real.exp (t1.eval x) * a - 1 / t2.eval x * b = Real.cos x :=
    HasDerivAt_unique (EMLTree.eml t1 t2).eval _ _ x hstruct hfree
  have ht2ne : t2.eval x ≠ 0 := ne_of_lt hpos |>.symm
  have hb : b = t2.eval x * (Real.exp (t1.eval x) * a - Real.cos x) := by
    have hY : 1 / t2.eval x * b = Real.exp (t1.eval x) * a - Real.cos x := by
      rw [← heq]
      mach_mpoly [Real.exp (t1.eval x) * a, 1 / t2.eval x * b]
    rw [← hY, ← mul_assoc, mul_inv (t2.eval x) ht2ne, one_mul_thm]
  rwa [hb] at h2

/-- **The depth-1 constant-ratio fact.** Assembling `eml_depth1_t2_ode` + `eml_depth1_E_deriv` via
`const_ratio_of_shared_ode`: throughout any interval `[p,q]` where `t2` stays strictly positive
(and both `t1`, `t2` are differentiable, via explicit derivative-functions `t1'`/`t2'`), `t2` is
EXACTLY a constant multiple of the explicit integrating factor `exp(exp(t1) − sin)`. -/
theorem eml_depth1_t2_const_ratio {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x)
    (p q : Real) (hpq : p < q)
    (t1' : Real → Real) (ht1'd : ∀ x, p ≤ x → x ≤ q → HasDerivAt t1.eval (t1' x) x)
    (t2' : Real → Real) (ht2'd : ∀ x, p ≤ x → x ≤ q → HasDerivAt t2.eval (t2' x) x)
    (hpos : ∀ x, p ≤ x → x ≤ q → 0 < t2.eval x) :
    ∃ k : Real, ∀ x, p ≤ x → x ≤ q →
      t2.eval x = k * Real.exp (Real.exp (t1.eval x) - Real.sin x) :=
  const_ratio_of_shared_ode t2.eval
    (fun x => Real.exp (Real.exp (t1.eval x) - Real.sin x))
    (fun x => Real.exp (t1.eval x) * t1' x - Real.cos x)
    p q hpq
    (fun x hx1 hx2 => eml_depth1_t2_ode hsin (ht1'd x hx1 hx2) (ht2'd x hx1 hx2) (hpos x hx1 hx2))
    (fun x hx1 hx2 => eml_depth1_E_deriv (ht1'd x hx1 hx2))
    (fun x _ _ => (ne_of_lt (Real.exp_pos _)).symm)

/-! ## The minimal-violation-point contradiction, assembled for depth-1

The last pieces: (i) a value that is `0` throughout `[x0, xs)` and continuous AT `xs` is also `0`
AT `xs` (sign-preservation, mirroring `intermediate_value`'s own proof style); (ii) combine with
`eml_depth1_t2_const_ratio` and `inf_exists` to show a positivity witness at `x0` propagates to
the WHOLE of `[x0, b)`. -/

/-- If `g` vanishes throughout `[x0, xs)` and is continuous AT `xs` (with `x0 < xs`), `g` also
vanishes AT `xs` — by sign-preservation: `g xs ≠ 0` would give a neighborhood where `g` keeps that
sign, but arbitrarily close to `xs` from below `g` is `0`, a contradiction. -/
theorem eq_zero_at_of_eq_zero_below {g : Real → Real} {x0 xs : Real} (hx0xs : x0 < xs)
    (hcont : ContinuousAt g xs) (hzero : ∀ y, x0 ≤ y → y < xs → g y = 0) :
    g xs = 0 := by
  rcases lt_total (g xs) 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨δ, hδ, hnbhd⟩ := neg_nbhd_of_continuousAt hcont hlt
    obtain ⟨y, hy1, hy2⟩ := exists_between (max x0 (xs - δ)) xs
      (iv_ltmax hx0xs (iv_subself xs hδ))
    have hyx0 : x0 ≤ y := le_of_lt_r (lt_of_le_of_lt (le_max_left x0 (xs - δ)) hy1)
    have hyxsδ : xs - δ < y := lt_of_le_of_lt (le_max_right x0 (xs - δ)) hy1
    have habs : abs (y - xs) < δ := by
      rw [iv_absub (le_of_lt_r hy2)]
      have h2 := add_lt_add_left hyxsδ δ
      rw [show δ + (xs - δ) = xs from by mach_ring,
          show δ + y = y + δ from by mach_ring] at h2
      have h3 := add_lt_add_left h2 (-y)
      rw [show -y + xs = xs - y from by mach_mpoly [xs, y],
          show -y + (y + δ) = δ from by mach_mpoly [y, δ]] at h3
      exact h3
    have hgy0 : g y = 0 := hzero y hyx0 hy2
    have hcontra := hnbhd y habs
    rw [hgy0] at hcontra
    exact lt_irrefl_ax 0 hcontra
  · exact heq
  · exfalso
    obtain ⟨δ, hδ, hnbhd⟩ := pos_nbhd_of_continuousAt hcont hgt
    obtain ⟨y, hy1, hy2⟩ := exists_between (max x0 (xs - δ)) xs
      (iv_ltmax hx0xs (iv_subself xs hδ))
    have hyx0 : x0 ≤ y := le_of_lt_r (lt_of_le_of_lt (le_max_left x0 (xs - δ)) hy1)
    have hyxsδ : xs - δ < y := lt_of_le_of_lt (le_max_right x0 (xs - δ)) hy1
    have habs : abs (y - xs) < δ := by
      rw [iv_absub (le_of_lt_r hy2)]
      have h2 := add_lt_add_left hyxsδ δ
      rw [show δ + (xs - δ) = xs from by mach_ring,
          show δ + y = y + δ from by mach_ring] at h2
      have h3 := add_lt_add_left h2 (-y)
      rw [show -y + xs = xs - y from by mach_mpoly [xs, y],
          show -y + (y + δ) = δ from by mach_mpoly [y, δ]] at h3
      exact h3
    have hgy0 : g y = 0 := hzero y hyx0 hy2
    have hcontra := hnbhd y habs
    rw [hgy0] at hcontra
    exact lt_irrefl_ax 0 hcontra

/-- **Depth-1 positivity propagation — the full contradiction.** If `t = eml t1 t2` agrees with
`sin` on `[x0,b)`, `t2` is positive at `x0`, and both `t1`/`t2` are differentiable throughout
`[x0,b)`, `t2` stays positive on the WHOLE of `[x0,b)`.

Proof: suppose not; let `xs` be the infimum of the failure set (`inf_exists`). `t2` stays positive
on `[x0,xs)` (else `xs` wouldn't be the infimum), so it is forced to be `k * E1` there exactly
(`eml_depth1_t2_const_ratio`, `k := t2.eval x0 / E1 x0`, `E1 := exp(exp(t1) − sin)`). By continuity
this extends to `xs` itself (`eq_zero_at_of_eq_zero_below`, applied to `t2 − k·E1`), giving
`t2.eval xs = k · E1 xs > 0` (since `k > 0` and `E1 > 0`) — contradicting `xs` being a failure
point (`t2.eval xs ≤ 0`, forced by continuity from `xs = inf` of the `≤ 0` set). -/
theorem eml_depth1_pos_of_pos_witness {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x)
    (x0 b : Real) (hx0b : x0 < b)
    (t1' : Real → Real) (ht1'd : ∀ x, x0 ≤ x → x < b → HasDerivAt t1.eval (t1' x) x)
    (t2' : Real → Real) (ht2'd : ∀ x, x0 ≤ x → x < b → HasDerivAt t2.eval (t2' x) x)
    (hx0pos : 0 < t2.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < t2.eval x := by
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : t2.eval x ≤ 0 := by
    rcases lt_total 0 (t2.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => x0 ≤ y ∧ y < b ∧ t2.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedBelow (fun y => x0 ≤ y ∧ y < b ∧ t2.eval y ≤ 0) := ⟨x0, fun y hy => hy.1⟩
  obtain ⟨xs, hlb, hglb⟩ := inf_exists _ hSne hSbd
  have hx0xs : x0 ≤ xs := hglb x0 (fun y hy => hy.1)
  have hxsb : xs < b := lt_of_le_of_lt (hlb x ⟨hx1, hx2, hxle⟩) hx2
  have hposbelow : ∀ y, x0 ≤ y → y < xs → 0 < t2.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : t2.eval y ≤ 0 := by
      rcases lt_total 0 (t2.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hyb : y < b := lt_trans_ax hy2 hxsb
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlb y ⟨hy1, hyb, hyle⟩) hy2)
  have hxsle : t2.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < t2.eval xs := by
      rcases lt_total (t2.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ :=
      pos_nbhd_of_continuousAt (hasDerivAt_continuousAt (ht2'd xs hx0xs hxsb)) hxsgt
    have hbound2 : ∀ y, (x0 ≤ y ∧ y < b ∧ t2.eval y ≤ 0) → xs + δ ≤ y := by
      intro y hy
      rcases lt_total y (xs + δ) with h | h | h
      · exfalso
        have hyxs : xs ≤ y := hlb y hy
        have habs : abs (y - xs) < δ := by
          rcases (le_iff_lt_or_eq xs y).mp hyxs with hlt | heq
          · rw [abs_of_nonneg (le_of_lt_r (sub_pos_of_lt hlt))]
            have h2 := add_lt_add_left h (-xs)
            rwa [show -xs + y = y - xs from by mach_mpoly [xs, y],
                show -xs + (xs + δ) = δ from by mach_mpoly [xs, δ]] at h2
          · rw [← heq, show xs - xs = 0 from by mach_ring,
                abs_of_nonneg (le_refl (0 : Real))]
            exact hδ
        exact lt_irrefl_ax 0 (lt_of_lt_of_le (hnbhd y habs) hy.2.2)
      · exact le_of_eq h.symm
      · exact le_of_lt h
    exact lt_irrefl_ax xs (lt_of_lt_of_le (iv_ltadd xs hδ) (hglb (xs + δ) hbound2))
  -- t2 = k * E1 exactly throughout [x0, xs), extending by continuity to xs itself
  let E1 : Real → Real := fun z => Real.exp (Real.exp (t1.eval z) - Real.sin z)
  have hE1pos : ∀ z, 0 < E1 z := fun z => Real.exp_pos _
  let k : Real := t2.eval x0 * (1 / E1 x0)
  have hkE1x0 : k * E1 x0 = t2.eval x0 := by
    show t2.eval x0 * (1 / E1 x0) * E1 x0 = t2.eval x0
    rw [mul_assoc, mul_comm (1 / E1 x0) (E1 x0), mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
        mul_one_ax]
  have hkpos : 0 < k := mul_pos hx0pos (one_div_pos_of_pos (hE1pos x0))
  have hzero : ∀ y, x0 ≤ y → y < xs → t2.eval y - k * E1 y = 0 := by
    intro y hy1 hy2
    rcases (le_iff_lt_or_eq x0 y).mp hy1 with hlt | heq
    · obtain ⟨k', hk'⟩ := eml_depth1_t2_const_ratio hsin x0 y hlt t1'
        (fun z hz1 hz2 => ht1'd z hz1 (lt_of_le_of_lt hz2 (lt_trans_ax hy2 hxsb)))
        t2' (fun z hz1 hz2 => ht2'd z hz1 (lt_of_le_of_lt hz2 (lt_trans_ax hy2 hxsb)))
        (fun z hz1 hz2 => hposbelow z hz1 (lt_of_le_of_lt hz2 hy2))
      have hkx0 : t2.eval x0 = k' * E1 x0 := hk' x0 (le_refl x0) (le_of_lt hlt)
      have hkeq : k' = k := by
        have h2 : k' * E1 x0 = k * E1 x0 := by rw [← hkx0, hkE1x0]
        have h3 : k' * E1 x0 * (1 / E1 x0) = k * E1 x0 * (1 / E1 x0) := by rw [h2]
        rwa [mul_assoc, mul_assoc, mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
            mul_one_ax, mul_one_ax] at h3
      have hky : t2.eval y = k' * E1 y := hk' y hy1 (le_refl y)
      rw [hky, hkeq, sub_def, add_neg]
    · rw [← heq, hkE1x0, sub_def, add_neg]
  have hxsE1pos : 0 < k * E1 xs := mul_pos hkpos (hE1pos xs)
  have hxseq2 : t2.eval xs = k * E1 xs := by
    rcases (le_iff_lt_or_eq x0 xs).mp hx0xs with hx0xslt | hx0xseq
    · have hcontdiff : HasDerivAt (fun z => t2.eval z - k * E1 z)
          (t2' xs - (0 * E1 xs + k * (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs)))) xs :=
        HasDerivAt_sub t2.eval (fun z => k * E1 z) (t2' xs)
          (0 * E1 xs + k * (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs))) xs
          (ht2'd xs hx0xs hxsb)
          (HasDerivAt_mul (fun _ => k) E1 0 (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs)) xs
            (HasDerivAt_const k xs) (eml_depth1_E_deriv (ht1'd xs hx0xs hxsb)))
      have hxseq : t2.eval xs - k * E1 xs = 0 :=
        @eq_zero_at_of_eq_zero_below (fun z => t2.eval z - k * E1 z) x0 xs hx0xslt
          (hasDerivAt_continuousAt hcontdiff) hzero
      have h2 : t2.eval xs - k * E1 xs + k * E1 xs = 0 + k * E1 xs := by rw [hxseq]
      rwa [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
    · rw [← hx0xseq, hkE1x0]
  have hfinal : k * E1 xs ≤ 0 := hxseq2 ▸ hxsle
  exact lt_irrefl_ax 0 (lt_of_lt_of_le hxsE1pos hfinal)

/-- **A concrete witness, for free.** `sin(π) = 0 ≤ 0`, so `eml_nonpos_forces_log_arg_pos`
(a pure structural fact, no smoothness needed) already forces `t2.eval π > 0` — no ODE machinery
required for the witness itself, only for propagating it outward. -/
theorem eml_depth1_t2_witness_at_pi {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x) :
    0 < t2.eval Real.pi :=
  eml_nonpos_forces_log_arg_pos t1 t2 Real.pi (by rw [hsin]; exact le_of_eq sin_pi)

/-! ## The backward (mirror) direction — needed to reach small `b`

`eml_depth1_pos_of_pos_witness` only propagates FORWARD from a witness `x0`, giving positivity on
`[x0, b)` for `b > x0`. Since `EMLPfaffianValidOn t 0 b` is needed for ARBITRARY `b > 0` (including
`b` smaller than any witness `sin` provides, e.g. `b < π`), the mirror direction — propagating
BACKWARD from a witness `x1` down to positivity on `(a, x1]` — is also needed. Same mechanism,
`sup_exists` in place of `inf_exists`, approaching the violation point from ABOVE instead of
below. -/

/-- Mirror of `iv_ltmax`/`iv_ltmin`-style helpers used implicitly below via `min`. -/
theorem eq_zero_at_of_eq_zero_above {g : Real → Real} {xs x1 : Real} (hxsx1 : xs < x1)
    (hcont : ContinuousAt g xs) (hzero : ∀ y, xs < y → y ≤ x1 → g y = 0) :
    g xs = 0 := by
  rcases lt_total (g xs) 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨δ, hδ, hnbhd⟩ := neg_nbhd_of_continuousAt hcont hlt
    obtain ⟨y, hy1, hy2⟩ := exists_between xs (min (xs + δ) x1) (iv_ltmin (iv_ltadd xs hδ) hxsx1)
    have hyx1 : y ≤ x1 := le_of_lt (lt_of_lt_of_le hy2 (min_le_right (xs + δ) x1))
    have hyxsδ : y < xs + δ := lt_of_lt_of_le hy2 (min_le_left (xs + δ) x1)
    have habs : abs (y - xs) < δ := by
      rw [abs_of_nonneg (le_of_lt_r (sub_pos_of_lt hy1))]
      have h2 := add_lt_add_left hyxsδ (-xs)
      rw [show -xs + y = y - xs from by mach_mpoly [xs, y],
          show -xs + (xs + δ) = δ from by mach_mpoly [xs, δ]] at h2
      exact h2
    have hcontra := hnbhd y habs
    rw [hzero y hy1 hyx1] at hcontra
    exact lt_irrefl_ax 0 hcontra
  · exact heq
  · exfalso
    obtain ⟨δ, hδ, hnbhd⟩ := pos_nbhd_of_continuousAt hcont hgt
    obtain ⟨y, hy1, hy2⟩ := exists_between xs (min (xs + δ) x1) (iv_ltmin (iv_ltadd xs hδ) hxsx1)
    have hyx1 : y ≤ x1 := le_of_lt (lt_of_lt_of_le hy2 (min_le_right (xs + δ) x1))
    have hyxsδ : y < xs + δ := lt_of_lt_of_le hy2 (min_le_left (xs + δ) x1)
    have habs : abs (y - xs) < δ := by
      rw [abs_of_nonneg (le_of_lt_r (sub_pos_of_lt hy1))]
      have h2 := add_lt_add_left hyxsδ (-xs)
      rw [show -xs + y = y - xs from by mach_mpoly [xs, y],
          show -xs + (xs + δ) = δ from by mach_mpoly [xs, δ]] at h2
      exact h2
    have hcontra := hnbhd y habs
    rw [hzero y hy1 hyx1] at hcontra
    exact lt_irrefl_ax 0 hcontra

/-- **Depth-1 positivity propagation, BACKWARD.** If `t = eml t1 t2` agrees with `sin` on
`(a, x1]`, `t2` is positive at the witness `x1`, and both `t1`/`t2` are differentiable throughout
`(a, x1]`, then `t2` stays strictly positive on the WHOLE of `(a, x1]`. Mirror of
`eml_depth1_pos_of_pos_witness`: `sup_exists` finds the LAST failure point `xs` (closest to `x1`
from below); above `xs`, `t2` is forced to `k · E1` exactly; continuity extends this DOWN to `xs`,
giving a contradiction with `xs` being a failure. -/
theorem eml_depth1_pos_of_pos_witness_backward {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x)
    (a x1 : Real) (hax1 : a < x1)
    (t1' : Real → Real) (ht1'd : ∀ x, a < x → x ≤ x1 → HasDerivAt t1.eval (t1' x) x)
    (t2' : Real → Real) (ht2'd : ∀ x, a < x → x ≤ x1 → HasDerivAt t2.eval (t2' x) x)
    (hx1pos : 0 < t2.eval x1) :
    ∀ x, a < x → x ≤ x1 → 0 < t2.eval x := by
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : t2.eval x ≤ 0 := by
    rcases lt_total 0 (t2.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => a < y ∧ y ≤ x1 ∧ t2.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedAbove (fun y => a < y ∧ y ≤ x1 ∧ t2.eval y ≤ 0) := ⟨x1, fun y hy => hy.2.1⟩
  obtain ⟨xs, hub, hlub⟩ := sup_exists _ hSne hSbd
  have hxsx1 : xs ≤ x1 := hlub x1 (fun y hy => hy.2.1)
  have hax : a < xs := lt_of_lt_of_le hx1 (hub x ⟨hx1, hx2, hxle⟩)
  have hposabove : ∀ y, xs < y → y ≤ x1 → 0 < t2.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : t2.eval y ≤ 0 := by
      rcases lt_total 0 (t2.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hya : a < y := lt_trans_ax hax hy1
    exact lt_irrefl_ax xs (lt_of_lt_of_le hy1 (hub y ⟨hya, hy2, hyle⟩))
  have hxsle : t2.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < t2.eval xs := by
      rcases lt_total (t2.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ :=
      pos_nbhd_of_continuousAt (hasDerivAt_continuousAt (ht2'd xs hax hxsx1)) hxsgt
    have hbound2 : ∀ y, (a < y ∧ y ≤ x1 ∧ t2.eval y ≤ 0) → y ≤ xs - δ := by
      intro y hy
      rcases lt_total y (xs - δ) with h | h | h
      · exact le_of_lt h
      · exact le_of_eq h
      · exfalso
        have hyxs : y ≤ xs := hub y hy
        have habs : abs (y - xs) < δ := by
          rw [iv_absub hyxs]
          have h2 := add_lt_add_left h δ
          rw [show δ + (xs - δ) = xs from by mach_ring,
              show δ + y = y + δ from by mach_ring] at h2
          have h3 := add_lt_add_left h2 (-y)
          rw [show -y + xs = xs - y from by mach_mpoly [xs, y],
              show -y + (y + δ) = δ from by mach_mpoly [y, δ]] at h3
          exact h3
        exact lt_irrefl_ax 0 (lt_of_lt_of_le (hnbhd y habs) hy.2.2)
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlub (xs - δ) hbound2) (iv_subself xs hδ))
  let E1 : Real → Real := fun z => Real.exp (Real.exp (t1.eval z) - Real.sin z)
  have hE1pos : ∀ z, 0 < E1 z := fun z => Real.exp_pos _
  let k : Real := t2.eval x1 * (1 / E1 x1)
  have hkE1x1 : k * E1 x1 = t2.eval x1 := by
    show t2.eval x1 * (1 / E1 x1) * E1 x1 = t2.eval x1
    rw [mul_assoc, mul_comm (1 / E1 x1) (E1 x1), mul_inv (E1 x1) (ne_of_lt (hE1pos x1)).symm,
        mul_one_ax]
  have hkpos : 0 < k := mul_pos hx1pos (one_div_pos_of_pos (hE1pos x1))
  have hzero : ∀ y, xs < y → y ≤ x1 → t2.eval y - k * E1 y = 0 := by
    intro y hy1 hy2
    rcases (le_iff_lt_or_eq y x1).mp hy2 with hlt | heq
    · obtain ⟨k', hk'⟩ := eml_depth1_t2_const_ratio hsin y x1 hlt t1'
        (fun z hz1 hz2 => ht1'd z (lt_of_lt_of_le (lt_trans_ax hax hy1) hz1) hz2)
        t2' (fun z hz1 hz2 => ht2'd z (lt_of_lt_of_le (lt_trans_ax hax hy1) hz1) hz2)
        (fun z hz1 hz2 => hposabove z (lt_of_lt_of_le hy1 hz1) hz2)
      have hkx1 : t2.eval x1 = k' * E1 x1 := hk' x1 (le_of_lt hlt) (le_refl x1)
      have hkeq : k' = k := by
        have h2 : k' * E1 x1 = k * E1 x1 := by rw [← hkx1, hkE1x1]
        have h3 : k' * E1 x1 * (1 / E1 x1) = k * E1 x1 * (1 / E1 x1) := by rw [h2]
        rwa [mul_assoc, mul_assoc, mul_inv (E1 x1) (ne_of_lt (hE1pos x1)).symm,
            mul_one_ax, mul_one_ax] at h3
      have hky : t2.eval y = k' * E1 y := hk' y (le_refl y) (le_of_lt hlt)
      rw [hky, hkeq, sub_def, add_neg]
    · rw [heq, hkE1x1, sub_def, add_neg]
  have hxsE1pos : 0 < k * E1 xs := mul_pos hkpos (hE1pos xs)
  have hxseq2 : t2.eval xs = k * E1 xs := by
    rcases (le_iff_lt_or_eq xs x1).mp hxsx1 with hxsx1lt | hxsx1eq
    · have hcontdiff : HasDerivAt (fun z => t2.eval z - k * E1 z)
          (t2' xs - (0 * E1 xs + k * (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs)))) xs :=
        HasDerivAt_sub t2.eval (fun z => k * E1 z) (t2' xs)
          (0 * E1 xs + k * (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs))) xs
          (ht2'd xs hax hxsx1)
          (HasDerivAt_mul (fun _ => k) E1 0 (E1 xs * (Real.exp (t1.eval xs) * t1' xs - Real.cos xs)) xs
            (HasDerivAt_const k xs) (eml_depth1_E_deriv (ht1'd xs hax hxsx1)))
      have hxseq : t2.eval xs - k * E1 xs = 0 :=
        @eq_zero_at_of_eq_zero_above (fun z => t2.eval z - k * E1 z) xs x1 hxsx1lt
          (hasDerivAt_continuousAt hcontdiff) hzero
      have h2 : t2.eval xs - k * E1 xs + k * E1 xs = 0 + k * E1 xs := by rw [hxseq]
      rwa [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
    · rw [hxsx1eq, hkE1x1]
  have hfinal : k * E1 xs ≤ 0 := hxseq2 ▸ hxsle
  exact lt_irrefl_ax 0 (lt_of_lt_of_le hxsE1pos hfinal)

/-! ## Capstone: full depth-1 closure, any `b > 0`

Combining the `π` witness with BOTH directions covers the whole of `(0,b)` for any `b > 0` — the
backward direction reaches `(0,π]` (covering small `b`), the forward direction reaches `[π,b)`
(covering large `b`). This is a genuine, complete instance of `EMLPfaffianValidOn (eml t1 t2) 0 b`
reduced to just its `t2`-positivity clause (since, for `t1`/`t2` with no crossing, the other two
conjuncts of `EMLPfaffianValidOn` are handled by `eml_hasDerivAt_of_no_crossing` itself needing no
further validity). -/

/-- **Depth-1 closure, any `b`.** Given no crossing anywhere in `t1`/`t2` on `(0, max(b,π)]` (so
both are everywhere differentiable there — trivially true if `t1`/`t2` are leaves), `t = eml t1 t2`
agreeing with `sin` forces `t2` positive throughout `(0,b)`, for ANY `b > 0`. -/
theorem eml_depth1_validon_of_sin_eq {t1 t2 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x)
    (b : Real) (hb : 0 < b)
    (hnc1 : ∀ x : Real, 0 < x → EMLNoCrossingAt t1 x)
    (hnc2 : ∀ x : Real, 0 < x → EMLNoCrossingAt t2 x) :
    ∀ x, 0 < x → x < b → 0 < t2.eval x := by
  let t1' : Real → Real := fun x =>
    if h : 0 < x then (eml_hasDerivAt_of_no_crossing t1 x (hnc1 x h)).choose else 0
  have ht1'd : ∀ x, 0 < x → HasDerivAt t1.eval (t1' x) x := by
    intro x hx
    show HasDerivAt t1.eval (if h : 0 < x then (eml_hasDerivAt_of_no_crossing t1 x (hnc1 x h)).choose else 0) x
    rw [dif_pos hx]
    exact (eml_hasDerivAt_of_no_crossing t1 x (hnc1 x hx)).choose_spec
  let t2' : Real → Real := fun x =>
    if h : 0 < x then (eml_hasDerivAt_of_no_crossing t2 x (hnc2 x h)).choose else 0
  have ht2'd : ∀ x, 0 < x → HasDerivAt t2.eval (t2' x) x := by
    intro x hx
    show HasDerivAt t2.eval (if h : 0 < x then (eml_hasDerivAt_of_no_crossing t2 x (hnc2 x h)).choose else 0) x
    rw [dif_pos hx]
    exact (eml_hasDerivAt_of_no_crossing t2 x (hnc2 x hx)).choose_spec
  have hwitness : 0 < t2.eval Real.pi := eml_depth1_t2_witness_at_pi hsin
  intro x hx1 hx2
  rcases lt_total x Real.pi with hlt | heq | hgt
  · exact eml_depth1_pos_of_pos_witness_backward hsin 0 Real.pi pi_pos t1'
      (fun y hy1 hy2 => ht1'd y hy1) t2' (fun y hy1 hy2 => ht2'd y hy1) hwitness x hx1 (le_of_lt hlt)
  · rw [heq]; exact hwitness
  · exact eml_depth1_pos_of_pos_witness hsin Real.pi b (lt_trans_ax hgt hx2) t1'
      (fun y hy1 hy2 => ht1'd y (lt_of_lt_of_le pi_pos hy1)) t2'
      (fun y hy1 hy2 => ht2'd y (lt_of_lt_of_le pi_pos hy1)) hwitness x (le_of_lt hgt) hx2

/-! ## Toward arbitrary depth: the recursive step, generalized

`eml_depth1_t2_ode`/`eml_depth1_E_deriv` are special cases of a DEPTH-INDEPENDENT pattern: given
ONLY that the node `eml A B`'s derivative is SOME known explicit value `D` (not necessarily
`cos x` — at depth ≥ 2, `D` comes from the PREVIOUS level's own derived ODE, not from `sin`
directly), `B`'s derivative is forced into the same "linear ODE" shape, with an integrating
factor built from `A` and the node's OWN value (not needing an externally-named function like
`sin` at all). Instantiating with `eml A B := t` and `D := cos x` (the free root fact) recovers
depth-1; instantiating with `eml A B := t2` and `D` from depth-1's OWN derived ODE reaches
depth-2; and so on — the SAME two lemmas apply at every depth. -/

/-- **General ODE step.** Generalizes `eml_depth1_t2_ode`: the node's derivative being SOME known
`D` (of any origin) forces `B`'s derivative into the same shape. -/
theorem eml_ode_step_general {A B : EMLTree} {x a b D : Real}
    (hNderiv : HasDerivAt (EMLTree.eml A B).eval D x)
    (hA : HasDerivAt A.eval a x) (hB : HasDerivAt B.eval b x) (hBpos : 0 < B.eval x) :
    b = B.eval x * (Real.exp (A.eval x) * a - D) := by
  have hstruct : HasDerivAt (EMLTree.eml A B).eval
      (Real.exp (A.eval x) * a - 1 / B.eval x * b) x :=
    eml_hasDerivAt_pos_branch hA hB hBpos
  have heq : Real.exp (A.eval x) * a - 1 / B.eval x * b = D :=
    HasDerivAt_unique (EMLTree.eml A B).eval _ _ x hstruct hNderiv
  have hBne : B.eval x ≠ 0 := (ne_of_lt hBpos).symm
  have hY : 1 / B.eval x * b = Real.exp (A.eval x) * a - D := by
    rw [← heq]
    mach_mpoly [Real.exp (A.eval x) * a, 1 / B.eval x * b]
  rw [← hY, ← mul_assoc, mul_inv (B.eval x) hBne, one_mul_thm]

/-- **General integrating-factor step.** Generalizes `eml_depth1_E_deriv`: the next-level
integrating factor `exp(exp(A) − N.eval)` — built from `A` and the node's OWN value, needing no
externally-named function — satisfies the matching ODE. -/
theorem eml_E_step_general {A B : EMLTree} {x a D : Real}
    (hA : HasDerivAt A.eval a x) (hNderiv : HasDerivAt (EMLTree.eml A B).eval D x) :
    HasDerivAt (fun z => Real.exp (Real.exp (A.eval z) - (EMLTree.eml A B).eval z))
      (Real.exp (Real.exp (A.eval x) - (EMLTree.eml A B).eval x) *
        (Real.exp (A.eval x) * a - D)) x := by
  have hexp : HasDerivAt (fun z => Real.exp (A.eval z)) (Real.exp (A.eval x) * a) x :=
    HasDerivAt_comp Real.exp A.eval a (Real.exp (A.eval x)) x hA (HasDerivAt_exp _)
  have hAnew : HasDerivAt (fun z => Real.exp (A.eval z) - (EMLTree.eml A B).eval z)
      (Real.exp (A.eval x) * a - D) x :=
    HasDerivAt_sub _ _ _ _ x hexp hNderiv
  exact HasDerivAt_comp Real.exp (fun z => Real.exp (A.eval z) - (EMLTree.eml A B).eval z)
    (Real.exp (A.eval x) * a - D) (Real.exp (Real.exp (A.eval x) - (EMLTree.eml A B).eval x))
    x hAnew (HasDerivAt_exp _)

/-! ## Toward left-descent: a node-local consistent-sign fact

The witness problem (round 9.5) is specifically about pinning `B`'s SIGN, not its exact value.
`eml_gap_avoidance` (pointwise, no continuity needed) plus the EVT (`continuousAt_bddAbove_Icc`,
giving a LOCAL bound with no connection to `sin`/`cos` required) plus `intermediate_value`
combine to show: ANY `eml A B` node's log-argument `B` has a CONSISTENT sign throughout any
closed sub-interval where nothing crosses — it just doesn't (yet) say WHICH sign, for nodes with
no external anchor. Still real progress: it turns "does B change sign" into a settled question,
leaving only "which sign" open. -/

/-- **Consistent sign.** Given no crossing anywhere in `[p,q]` (so `eml A B` and `B` are both
continuous there), `B` is either `≤ 0` throughout `[p,q]` or `> 0` throughout — it cannot switch,
because `eml_gap_avoidance` (using a LOCAL bound on `eml A B` from the Extreme Value Theorem)
forbids `B` from ever landing in the gap `(0, exp(-U))`, and `intermediate_value` would force it
through that gap if it ever switched sides. -/
theorem eml_log_arg_consistent_sign {A B : EMLTree} {p q : Real} (hpq : p < q)
    (hnc : ∀ x, p ≤ x → x ≤ q → EMLNoCrossingAt (EMLTree.eml A B) x) :
    (∀ x, p ≤ x → x ≤ q → B.eval x ≤ 0) ∨ (∀ x, p ≤ x → x ≤ q → 0 < B.eval x) := by
  have hcontN : ∀ x, p ≤ x → x ≤ q → ContinuousAt (EMLTree.eml A B).eval x :=
    fun x hx1 hx2 => eml_continuousAt_of_no_crossing _ x (hnc x hx1 hx2)
  obtain ⟨U, hU⟩ := continuousAt_bddAbove_Icc (EMLTree.eml A B).eval p q (le_of_lt hpq) hcontN
  have hdichot : ∀ x, p ≤ x → x ≤ q → B.eval x ≤ 0 ∨ Real.exp (-U) ≤ B.eval x :=
    fun x hx1 hx2 => eml_gap_avoidance A B x U (hU x hx1 hx2)
  -- `c := exp(-U-1)` is a concrete point strictly inside the gap `(0, exp(-U))`.
  have hcpos : (0 : Real) < Real.exp (-U - 1) := Real.exp_pos _
  have hclt : Real.exp (-U - 1) < Real.exp (-U) := by
    apply Real.exp_lt
    have h2 := add_lt_add_left (neg_neg_of_pos zero_lt_one_ax) (-U)
    rwa [show -U + -1 = -U - 1 from by mach_ring, add_zero] at h2
  have hcontshift : ∀ x, p ≤ x → x ≤ q →
      ContinuousAt (fun z => B.eval z - Real.exp (-U - 1)) x := by
    intro x hx1 hx2
    obtain ⟨b, hb⟩ := eml_hasDerivAt_of_no_crossing B x (hnc x hx1 hx2).2.1
    exact hasDerivAt_continuousAt
      (HasDerivAt_sub B.eval (fun _ => Real.exp (-U - 1)) b 0 x hb (HasDerivAt_const _ x))
  have hgap_contra : ∀ c, p ≤ c → c ≤ q → B.eval c ≠ Real.exp (-U - 1) := by
    intro c hcp hcq hBc
    rcases hdichot c hcp hcq with h | h
    · rw [hBc] at h; exact lt_irrefl_ax 0 (lt_of_lt_of_le hcpos h)
    · rw [hBc] at h; exact lt_irrefl_ax _ (lt_of_le_of_lt h hclt)
  by_cases hexle : ∃ x, p ≤ x ∧ x ≤ q ∧ B.eval x ≤ 0
  · left
    obtain ⟨x1, hx1a, hx1b, hx1le⟩ := hexle
    intro x hxa hxb
    refine Classical.byContradiction (fun hxcon => ?_)
    have hxge : Real.exp (-U) ≤ B.eval x := by
      rcases hdichot x hxa hxb with h | h
      · exact absurd h hxcon
      · exact h
    rcases lt_total x1 x with hlt | heq | hgt
    · obtain ⟨c, hc1, hc2, hc3⟩ :=
        intermediate_value (fun z => B.eval z - Real.exp (-U - 1)) x1 x hlt
          (fun z hz1 hz2 => hcontshift z (le_trans hx1a hz1) (le_trans hz2 hxb))
          (by
            show B.eval x1 - Real.exp (-U - 1) < 0
            have hlt1 : B.eval x1 < Real.exp (-U - 1) := lt_of_le_of_lt hx1le hcpos
            have h2 := add_lt_add_left hlt1 (-Real.exp (-U - 1))
            rwa [neg_add_self, add_comm (-Real.exp (-U - 1)) (B.eval x1), ← sub_def] at h2)
          (by
            show 0 < B.eval x - Real.exp (-U - 1)
            exact sub_pos_of_lt (lt_of_lt_of_le hclt hxge))
      have hBc : B.eval c = Real.exp (-U - 1) := by
        have h2 : B.eval c - Real.exp (-U - 1) + Real.exp (-U - 1) = 0 + Real.exp (-U - 1) := by
          rw [hc3]
        rwa [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
      exact hgap_contra c (le_trans hx1a (le_of_lt hc1)) (le_trans (le_of_lt hc2) hxb) hBc
    · rw [← heq] at hxge
      exact lt_irrefl_ax (B.eval x1)
        (lt_of_lt_of_le (lt_of_le_of_lt hx1le (Real.exp_pos (-U))) hxge)
    · obtain ⟨c, hc1, hc2, hc3⟩ :=
        intermediate_value (fun z => Real.exp (-U - 1) - B.eval z) x x1 hgt
          (fun z hz1 hz2 => by
            obtain ⟨b, hb⟩ := eml_hasDerivAt_of_no_crossing B z (hnc z (le_trans hxa hz1)
              (le_trans hz2 hx1b)).2.1
            exact hasDerivAt_continuousAt
              (HasDerivAt_sub (fun _ => Real.exp (-U - 1)) B.eval 0 b z
                (HasDerivAt_const _ z) hb))
          (by
            show Real.exp (-U - 1) - B.eval x < 0
            have hlt2 : Real.exp (-U - 1) < B.eval x := lt_of_lt_of_le hclt hxge
            have h2 := add_lt_add_left hlt2 (-B.eval x)
            rwa [neg_add_self, add_comm (-B.eval x) (Real.exp (-U - 1)), ← sub_def] at h2)
          (by
            show 0 < Real.exp (-U - 1) - B.eval x1
            exact sub_pos_of_lt (lt_of_le_of_lt hx1le hcpos))
      have hBc : B.eval c = Real.exp (-U - 1) := by
        have h2 : Real.exp (-U - 1) - B.eval c + B.eval c = 0 + B.eval c := by rw [hc3]
        rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
        exact h2.symm
      exact hgap_contra c (le_trans hxa (le_of_lt hc1)) (le_trans (le_of_lt hc2) hx1b) hBc
  · right
    intro x hxa hxb
    rcases hdichot x hxa hxb with h | h
    · exact absurd ⟨x, hxa, hxb, h⟩ hexle
    · exact lt_of_lt_of_le (Real.exp_pos (-U)) h

end MachLib
