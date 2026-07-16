import MachLib.EMLPfaffian
import MachLib.MultiVarTwoExpSum
import MachLib.WronskianProportional
import MachLib.SinNotInEML

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
open MachLib.MultiVarMod.TwoExp (neg_lt_neg add_lt_add)

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

/-! ## Toward full generality: the "right-then-left" blow-up

Round 5's value-blow-up mechanism (`eml_depth2_blowup`, "right-right") turned out to have a reach
limit. Round 10 found a node-local sign fact that reaches left-descent but only pins WHICH sign
for anchored nodes. Here: a DIFFERENT class of trees closes via blow-up after all — offenders
whose ancestor path, after the mandatory first "right" step, consists ENTIRELY of "left" steps —
because (round 8.5's state-machine finding) a value forceable arbitrarily LARGE survives any run
of left steps (composing with a further `exp`, which is unbounded above, unlike `log`'s clamp
which discards magnitude). This needs the sibling encountered at each left step to be BOUNDED
(via EVT + no-crossing), not anchored to anything named. -/

/-- **A node's value exceeds any target, given its log-argument is small enough.** Isolates the
first-step mechanism inside `eml_depth2_blowup` as its own reusable fact (for ANY target `M1`, not
just the specific one that proof needed). -/
theorem eml_rightstep_exceeds (W1 W2 : EMLTree) (y M1 : Real) :
    ∃ δ : Real, 0 < δ ∧ (0 < W2.eval y → W2.eval y < δ →
      M1 < (EMLTree.eml W1 W2).eval y) := by
  obtain ⟨δ, hδpos, hM⟩ := log_unbounded_below (Real.exp (W1.eval y) - M1)
  refine ⟨δ, hδpos, fun hpos hlt => ?_⟩
  have hlog : Real.log (W2.eval y) < Real.exp (W1.eval y) - M1 := hM (W2.eval y) hpos hlt
  show M1 < Real.exp (W1.eval y) - Real.log (W2.eval y)
  have h2 := neg_lt_neg hlog
  have h3 := add_lt_add_left h2 (Real.exp (W1.eval y))
  rwa [show Real.exp (W1.eval y) + -(Real.exp (W1.eval y) - M1) = M1
        from by mach_mpoly [Real.exp (W1.eval y), M1],
      show Real.exp (W1.eval y) + -(Real.log (W2.eval y))
        = Real.exp (W1.eval y) - Real.log (W2.eval y)
        from by mach_mpoly [Real.exp (W1.eval y), Real.log (W2.eval y)]] at h3

/-- **A single left-step preserves "forceable arbitrarily large."** Given a node `eml W1 W2`
whose value can be forced above any target (via `W2` landing small positive), wrapping it as the
FIRST child of a further `eml` node — `eml (eml W1 W2) C` — is ALSO forceable arbitrarily large,
GIVEN an upper bound `M_C` on `log(C.eval y)` (e.g. from `C` being bounded via the EVT and
no-crossing, whether or not `C` is itself positive — a bound suffices either way). No dependence
on `C` being anchored to anything named. -/
theorem eml_leftstep_blowup (W1 W2 C : EMLTree) (y L M_C : Real)
    (hC : Real.log (C.eval y) ≤ M_C) :
    ∃ δ : Real, 0 < δ ∧ (0 < W2.eval y → W2.eval y < δ →
      L < (EMLTree.eml (EMLTree.eml W1 W2) C).eval y) := by
  obtain ⟨δ, hδpos, hM1⟩ := eml_rightstep_exceeds W1 W2 y (L + M_C)
  refine ⟨δ, hδpos, fun hpos hlt => ?_⟩
  have hWbig : L + M_C < (EMLTree.eml W1 W2).eval y := hM1 hpos hlt
  show L < Real.exp ((EMLTree.eml W1 W2).eval y) - Real.log (C.eval y)
  have hexp_gt : (EMLTree.eml W1 W2).eval y < Real.exp ((EMLTree.eml W1 W2).eval y) :=
    exp_grows_strictly_thm _
  have h1 : L + M_C < Real.exp ((EMLTree.eml W1 W2).eval y) := lt_trans_ax hWbig hexp_gt
  have h2 : L < Real.exp ((EMLTree.eml W1 W2).eval y) - M_C := by
    have h3 := add_lt_add_left h1 (-M_C)
    rwa [show -M_C + (L + M_C) = L from by mach_mpoly [L, M_C],
        show -M_C + Real.exp ((EMLTree.eml W1 W2).eval y)
          = Real.exp ((EMLTree.eml W1 W2).eval y) - M_C
          from by mach_mpoly [M_C, Real.exp ((EMLTree.eml W1 W2).eval y)]] at h3
  have h4 : Real.exp ((EMLTree.eml W1 W2).eval y) - M_C
      ≤ Real.exp ((EMLTree.eml W1 W2).eval y) - Real.log (C.eval y) := by
    have h5 := add_le_add_left (neg_le_neg hC) (Real.exp ((EMLTree.eml W1 W2).eval y))
    rwa [← sub_def, ← sub_def] at h5
  exact lt_of_lt_of_le h2 h4

/-! ## Generalizing to an arbitrary-length left-chain -/

/-- The offender `W2`'s node is forceable above ANY target `L`, as `W2.eval y` lands small enough
positive. A named predicate purely to make the chain induction below readable. -/
def ForceableLarge (T W2 : EMLTree) (y : Real) : Prop :=
  ∀ L : Real, ∃ δ : Real, 0 < δ ∧ (0 < W2.eval y → W2.eval y < δ → L < T.eval y)

/-- Repackages `eml_rightstep_exceeds` as the base case of the chain induction. -/
theorem forceableLarge_base (W1 W2 : EMLTree) (y : Real) : ForceableLarge (EMLTree.eml W1 W2) W2 y :=
  fun L => eml_rightstep_exceeds W1 W2 y L

/-- Repackages `eml_leftstep_blowup`'s mechanism to compose with an ARBITRARY already-forceable
`base`, not just `eml W1 W2` specifically. -/
theorem forceableLarge_leftstep {base C W2 : EMLTree} {y M_C : Real}
    (hbase : ForceableLarge base W2 y) (hC : Real.log (C.eval y) ≤ M_C) :
    ForceableLarge (EMLTree.eml base C) W2 y := by
  intro L
  obtain ⟨δ, hδpos, hM1⟩ := hbase (L + M_C)
  refine ⟨δ, hδpos, fun hpos hlt => ?_⟩
  have hWbig : L + M_C < base.eval y := hM1 hpos hlt
  show L < Real.exp (base.eval y) - Real.log (C.eval y)
  have hexp_gt : base.eval y < Real.exp (base.eval y) := exp_grows_strictly_thm _
  have h1 : L + M_C < Real.exp (base.eval y) := lt_trans_ax hWbig hexp_gt
  have h2 : L < Real.exp (base.eval y) - M_C := by
    have h3 := add_lt_add_left h1 (-M_C)
    rwa [show -M_C + (L + M_C) = L from by mach_mpoly [L, M_C],
        show -M_C + Real.exp (base.eval y) = Real.exp (base.eval y) - M_C
          from by mach_mpoly [M_C, Real.exp (base.eval y)]] at h3
  have h4 : Real.exp (base.eval y) - M_C ≤ Real.exp (base.eval y) - Real.log (C.eval y) := by
    have h5 := add_le_add_left (neg_le_neg hC) (Real.exp (base.eval y))
    rwa [← sub_def, ← sub_def] at h5
  exact lt_of_lt_of_le h2 h4

/-- Wraps `base` as the first child of a succession of `eml`-nodes, one per list element,
INNERMOST first. -/
def wrapLeft : List EMLTree → EMLTree → EMLTree
  | [], base => base
  | c :: cs, base => wrapLeft cs (EMLTree.eml base c)

/-- **The chain generalization.** Given a bound on EVERY sibling encountered along an
arbitrary-length run of left-steps, `ForceableLarge` survives the WHOLE chain. -/
theorem forceableLarge_wrapLeft {W2 : EMLTree} {y : Real} (Cs : List EMLTree)
    (M : EMLTree → Real) (hM : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c)
    {base : EMLTree} (hbase : ForceableLarge base W2 y) :
    ForceableLarge (wrapLeft Cs base) W2 y := by
  induction Cs generalizing base with
  | nil => exact hbase
  | cons c cs ih =>
    have hcbound : Real.log (c.eval y) ≤ M c := hM c (List.Mem.head cs)
    have hrest : ∀ c' ∈ cs, Real.log (c'.eval y) ≤ M c' :=
      fun c' hc' => hM c' (List.Mem.tail c hc')
    have hstep : ForceableLarge (EMLTree.eml base c) W2 y := forceableLarge_leftstep hbase hcbound
    show ForceableLarge (wrapLeft cs (EMLTree.eml base c)) W2 y
    exact ih hrest hstep

/-! ## Closing the "right-then-all-left" class -/

/-- **The full closure for this class of trees.** If `t = wrapLeft Cs (eml W1 W2)` (offender
`W2`, reached by one right step then the left-chain `Cs`) agrees with `sin`, and every sibling
along the chain has a boundable log at `y` (free via the EVT + no-crossing), then `W2.eval y`
CANNOT land in `(0, δ)` for the `δ` this produces — landing there would force `t.eval y > 1 + 1`,
contradicting `sin y ≤ 1`. -/
theorem eml_leftchain_sin_contradiction {W1 W2 : EMLTree} (Cs : List EMLTree) (y : Real)
    (M : EMLTree → Real) (hM : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c)
    (hsin : ∀ x : Real, (wrapLeft Cs (EMLTree.eml W1 W2)).eval x = Real.sin x) :
    ∃ δ : Real, 0 < δ ∧ ¬ (0 < W2.eval y ∧ W2.eval y < δ) := by
  obtain ⟨δ, hδpos, hforce⟩ :=
    forceableLarge_wrapLeft Cs M hM (forceableLarge_base W1 W2 y) (1 + 1)
  refine ⟨δ, hδpos, fun ⟨hpos, hlt⟩ => ?_⟩
  have h2 : 1 + 1 < (wrapLeft Cs (EMLTree.eml W1 W2)).eval y := hforce hpos hlt
  rw [hsin y] at h2
  have h1lt2 : (1 : Real) < 1 + 1 := by
    have h3 := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h3
  exact lt_irrefl_ax 1 (lt_of_lt_of_le (lt_trans_ax h1lt2 h2) (sin_le_one y))

/-- If `g` is continuous at `xs` and strictly positive throughout `[x0,xs)` (`x0 < xs`), `g xs`
is at least `0` — mirrors `eq_zero_at_of_eq_zero_below`'s technique (sign-preservation via
`neg_nbhd_of_continuousAt` + `exists_between`), for a `>` hypothesis instead of `=`. -/
theorem nonneg_at_of_pos_below {g : Real → Real} {x0 xs : Real} (hx0xs : x0 < xs)
    (hcont : ContinuousAt g xs) (hpos : ∀ y, x0 ≤ y → y < xs → 0 < g y) :
    0 ≤ g xs := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hgltxs : g xs < 0 := by
    rcases lt_total (g xs) 0 with h | h | h
    · exact h
    · exact absurd (le_of_eq h.symm) hcon
    · exact absurd (le_of_lt h) hcon
  obtain ⟨δ, hδ, hnbhd⟩ := neg_nbhd_of_continuousAt hcont hgltxs
  obtain ⟨y, hy1, hy2⟩ := exists_between (max x0 (xs - δ)) xs (iv_ltmax hx0xs (iv_subself xs hδ))
  have hyx0 : x0 ≤ y := le_trans (le_max_left x0 (xs - δ)) (le_of_lt hy1)
  have hyxsδ : xs - δ < y := lt_of_le_of_lt (le_max_right x0 (xs - δ)) hy1
  have hyxsneg : y - xs < 0 := by
    have h2 := add_lt_add_left hy2 (-xs)
    rwa [neg_add_self, add_comm (-xs) y, ← sub_def] at h2
  have habs : abs (y - xs) < δ := by
    rw [iv_aon hyxsneg, show -(y - xs) = xs - y from by mach_ring]
    have h2 := add_lt_add_left hyxsδ δ
    rw [show δ + (xs - δ) = xs from by mach_ring, show δ + y = y + δ from by mach_ring] at h2
    have h3 := add_lt_add_left h2 (-y)
    rwa [show -y + xs = xs - y from by mach_mpoly [xs, y],
        show -y + (y + δ) = δ from by mach_mpoly [y, δ]] at h3
  exact lt_irrefl_ax 0 (lt_trans_ax (hpos y hyx0 hy2) (hnbhd y habs))

/-! ## Reopening the wiring: local bounds suffice, not full-interval EVT

The obstacle above was framed as needing a "two-sided bound on `W1.eval` near `xs`" via the
interval-wide EVT. Re-examining: `δ = exp(exp(W1.eval y) − M₁)` is *monotonic* in `W1.eval y`
(composition of two strictly increasing `exp`s and a constant shift) and always strictly positive
regardless of how negative its argument gets — so keeping it bounded away from `0` as `y → xs`
needs only a LOCAL lower bound on `W1.eval y` near `xs` (from bare continuity at the single point
`xs`, `bdd_below_nbhd_of_continuousAt` — no compactness, no interval), plus a LOCAL upper bound on
each sibling `c.eval y` (`bdd_above_nbhd_of_continuousAt`, same local tool) converted to a bound on
`log(c.eval y)` via `log_le_of_le` below (a plain algebraic fact, not a continuity one — `log`'s
clamp is upper-bounded by `max 0 (log U)` whenever the argument is `≤ U`, regardless of sign). This
downgrades the obstacle from "needs new EVT machinery" to "needs bookkeeping the finite list of
local radii and an explicit (not existential) formula for `δ`" — mechanical, not a new idea. -/

/-- **Upper bound on the clamped log from an upper bound on its argument.** `Real.log` is
`0` for non-positive arguments and ordinary (increasing) for positive ones, so for `v ≤ U`:
if `v ≤ 0`, `log v = 0 ≤ max 0 (log U)` outright; if `0 < v ≤ U`, `log v ≤ log U` by monotonicity
(`Real.log_lt_log`, or equality) — either way bounded by `max 0 (log U)`. Purely algebraic, no
continuity needed; this is what lets a bound on a sibling's VALUE (from bare continuity) become a
bound on its LOG, without needing continuity of the log-composition itself (which can fail exactly
at a crossing of that sibling). -/
theorem log_le_of_le {v U : Real} (h : v ≤ U) : Real.log v ≤ max 0 (Real.log U) := by
  by_cases hv : v ≤ 0
  · rw [Real.log_nonpos hv]; exact le_max_left 0 (Real.log U)
  · have hvpos : 0 < v := by
      rcases lt_total 0 v with hp | heq | hn
      · exact hp
      · exact absurd (le_of_eq heq.symm) hv
      · exact absurd (le_of_lt hn) hv
    rcases (le_iff_lt_or_eq v U).mp h with hlt | heq
    · exact le_of_lt_r (lt_of_lt_of_le_r (Real.log_lt_log hvpos hlt) (le_max_right 0 (Real.log U)))
    · rw [heq]; exact le_max_right 0 (Real.log U)

/-- **Uniform local upper-bound radius over a finite list.** Given every `c` in `Cs` continuous at
`xs` (from `EMLNoCrossingAt`), there is a SINGLE radius `ρ > 0` within which ALL of them satisfy
the same local upper bound simultaneously — by induction on the list, taking the min of each new
element's own radius (`bdd_above_nbhd_of_continuousAt`) with the rest's (the IH). -/
theorem chain_radius (xs : Real) (Cs : List EMLTree) (hnc : ∀ c ∈ Cs, EMLNoCrossingAt c xs) :
    ∃ ρ : Real, 0 < ρ ∧ ∀ y, abs (y - xs) < ρ → ∀ c ∈ Cs, c.eval y < c.eval xs + 1 := by
  induction Cs with
  | nil => exact ⟨1, zero_lt_one_ax, fun y _ c hc => nomatch hc⟩
  | cons c cs ih =>
    obtain ⟨ρcs, hρcs, hcs⟩ := ih (fun c' hc' => hnc c' (List.Mem.tail c hc'))
    have hcontc : ContinuousAt c.eval xs :=
      eml_continuousAt_of_no_crossing c xs (hnc c (List.Mem.head cs))
    obtain ⟨ρc, hρc, hbc⟩ := bdd_above_nbhd_of_continuousAt hcontc
    refine ⟨min ρcs ρc, iv_ltmin hρcs hρc, fun y hy c' hc' => ?_⟩
    cases hc' with
    | head => exact hbc y (lt_of_lt_of_le_r hy (min_le_right ρcs ρc))
    | tail _ hc'' => exact hcs y (lt_of_lt_of_le_r hy (min_le_left ρcs ρc)) c' hc''

/-! ## The explicit-δ chain mechanism

`forceableLarge_wrapLeft`/`eml_leftchain_sin_contradiction` hide their `δ` behind an existential —
fine for a single-point contradiction, but the wiring above needs to COMPARE that `δ` against a
separately-computed lower bound, which needs the formula EXPOSED, not opaque behind `obtain`. This
section rebuilds the same mechanism with the δ made syntactically explicit throughout. -/

/-- Accumulates the per-sibling log bounds along a chain — the exact quantity the explicit `δ`
formula subtracts. -/
noncomputable def listLogSum (M : EMLTree → Real) : List EMLTree → Real
  | [] => 0
  | c :: cs => M c + listLogSum M cs

/-- Explicit-δ version of `eml_rightstep_exceeds`: same mechanism, δ exposed as
`exp(exp(W1.eval y) − M₁)` directly instead of behind `log_unbounded_below`'s existential. -/
theorem eml_rightstep_exceeds_exact (W1 W2 : EMLTree) (y M1 : Real)
    (hpos : 0 < W2.eval y) (hlt : W2.eval y < Real.exp (Real.exp (W1.eval y) - M1)) :
    M1 < (EMLTree.eml W1 W2).eval y := by
  have hlog : Real.log (W2.eval y) < Real.exp (W1.eval y) - M1 := log_lt_of_lt_exp hpos hlt
  show M1 < Real.exp (W1.eval y) - Real.log (W2.eval y)
  have h2 := neg_lt_neg hlog
  have h3 := add_lt_add_left h2 (Real.exp (W1.eval y))
  rwa [show Real.exp (W1.eval y) + -(Real.exp (W1.eval y) - M1) = M1
        from by mach_mpoly [Real.exp (W1.eval y), M1],
      show Real.exp (W1.eval y) + -(Real.log (W2.eval y))
        = Real.exp (W1.eval y) - Real.log (W2.eval y)
        from by mach_mpoly [Real.exp (W1.eval y), Real.log (W2.eval y)]] at h3

/-- **The explicit-δ chain.** Generalizes `eml_rightstep_exceeds_exact` through an arbitrary-length
`wrapLeft` chain, threading an abstract `base`/`f` pair (`f` being `base`'s own explicit
exceeds-threshold) through each left-step exactly as `forceableLarge_leftstep` does, but keeping
the resulting threshold syntactically explicit (`f (L + listLogSum M Cs)`) instead of hiding it
behind an existential. -/
theorem chain_exact {W2 : EMLTree} {y : Real} (Cs : List EMLTree)
    (M : EMLTree → Real) (hM : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c)
    {base : EMLTree} {f : Real → Real}
    (hbase : ∀ L, 0 < W2.eval y → W2.eval y < f L → L < base.eval y) :
    ∀ L : Real, 0 < W2.eval y → W2.eval y < f (L + listLogSum M Cs) →
      L < (wrapLeft Cs base).eval y := by
  induction Cs generalizing base f with
  | nil =>
    intro L hpos hlt
    show L < base.eval y
    apply hbase L hpos
    have hz : listLogSum M ([] : List EMLTree) = 0 := rfl
    rwa [hz, add_zero] at hlt
  | cons c cs ih =>
    intro L hpos hlt
    have hcbound : Real.log (c.eval y) ≤ M c := hM c (List.Mem.head cs)
    have hrest : ∀ c' ∈ cs, Real.log (c'.eval y) ≤ M c' :=
      fun c' hc' => hM c' (List.Mem.tail c hc')
    have hstep : ∀ L', 0 < W2.eval y → W2.eval y < f (L' + M c) → L' < (EMLTree.eml base c).eval y := by
      intro L' hpos' hlt'
      have hWbig : L' + M c < base.eval y := hbase (L' + M c) hpos' hlt'
      show L' < Real.exp (base.eval y) - Real.log (c.eval y)
      have hexp_gt : base.eval y < Real.exp (base.eval y) := exp_grows_strictly_thm _
      have h1 : L' + M c < Real.exp (base.eval y) := lt_trans_ax hWbig hexp_gt
      have h2 : L' < Real.exp (base.eval y) - M c := by
        have h3 := add_lt_add_left h1 (-(M c))
        rwa [show -(M c) + (L' + M c) = L' from by mach_mpoly [L', M c],
            show -(M c) + Real.exp (base.eval y) = Real.exp (base.eval y) - M c
              from by mach_mpoly [M c, Real.exp (base.eval y)]] at h3
      have h4 : Real.exp (base.eval y) - M c ≤ Real.exp (base.eval y) - Real.log (c.eval y) := by
        have h5 := add_le_add_left (neg_le_neg hcbound) (Real.exp (base.eval y))
        rwa [← sub_def, ← sub_def] at h5
      exact lt_of_lt_of_le h2 h4
    show L < (wrapLeft cs (EMLTree.eml base c)).eval y
    apply ih hrest hstep L hpos
    have heq : listLogSum M (c :: cs) = M c + listLogSum M cs := rfl
    rw [heq, show L + (M c + listLogSum M cs) = L + listLogSum M cs + M c from by mach_ring] at hlt
    exact hlt

/-- **Explicit-δ chain contradiction.** Same conclusion as `eml_leftchain_sin_contradiction`, but
taking `0 < W2.eval y` and the explicit threshold `W2.eval y < exp(exp(W1.eval y) − (1+1+ΣM_c))`
directly as hypotheses (instead of returning `∃δ,...`) — so its `δ` can be compared against an
independently-computed lower bound at the call site. -/
theorem eml_leftchain_sin_contradiction_exact {W1 W2 : EMLTree} (Cs : List EMLTree) (y : Real)
    (M : EMLTree → Real) (hM : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c)
    (hsin : ∀ x : Real, (wrapLeft Cs (EMLTree.eml W1 W2)).eval x = Real.sin x)
    (hpos : 0 < W2.eval y)
    (hlt : W2.eval y < Real.exp (Real.exp (W1.eval y) - (1 + 1 + listLogSum M Cs))) :
    False := by
  have hbase : ∀ L, 0 < W2.eval y → W2.eval y < Real.exp (Real.exp (W1.eval y) - L) →
      L < (EMLTree.eml W1 W2).eval y :=
    fun L hp hl => eml_rightstep_exceeds_exact W1 W2 y L hp hl
  have h2 : (1 : Real) + 1 < (wrapLeft Cs (EMLTree.eml W1 W2)).eval y :=
    chain_exact Cs M hM hbase (1 + 1) hpos hlt
  rw [hsin y] at h2
  have h1lt2 : (1 : Real) < 1 + 1 := by
    have h3 := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h3
  exact lt_irrefl_ax 1 (lt_of_lt_of_le (lt_trans_ax h1lt2 h2) (sin_le_one y))

/-- **The full closure for the "right-then-all-left" class.** If `t = wrapLeft Cs (eml W1 W2)`
(offender `W2`) agrees with `sin` everywhere, `W2` is positive at a witness `x0`, and `W1`/`W2`/every
sibling in `Cs` has no crossing throughout `[x0,b)`, `W2` stays positive on the WHOLE of `[x0,b)`.

Proof shape mirrors `eml_depth1_pos_of_pos_witness` (minimal-violation point `xs` via `inf_exists`,
`W2.eval xs = 0` exactly via `nonneg_at_of_pos_below` + the sign-preservation argument for `≤ 0`)
but the final contradiction, instead of an ODE/constant-ratio identity, uses the explicit-δ chain
mechanism: local bounds at `xs` alone (`bdd_below_nbhd_of_continuousAt` for `W1`, `chain_radius` +
`log_le_of_le` for the siblings) give a δ that provably stays away from `0` near `xs`, letting
continuity of `W2` (with `W2.eval xs = 0`) place a point `y` just below `xs` inside the
contradiction's window. -/
theorem eml_leftchain_pos_of_no_crossing {W1 W2 : EMLTree} (Cs : List EMLTree)
    (x0 b : Real) (hx0b : x0 < b)
    (hncW1 : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt W1 x)
    (hncW2 : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt W2 x)
    (hncCs : ∀ c ∈ Cs, ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt c x)
    (hsin : ∀ x : Real, (wrapLeft Cs (EMLTree.eml W1 W2)).eval x = Real.sin x)
    (hx0pos : 0 < W2.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < W2.eval x := by
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : W2.eval x ≤ 0 := by
    rcases lt_total 0 (W2.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedBelow (fun y => x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) := ⟨x0, fun y hy => hy.1⟩
  obtain ⟨xs, hlb, hglb⟩ := inf_exists _ hSne hSbd
  have hx0xs : x0 ≤ xs := hglb x0 (fun y hy => hy.1)
  have hxsb : xs < b := lt_of_le_of_lt (hlb x ⟨hx1, hx2, hxle⟩) hx2
  have hposbelow : ∀ y, x0 ≤ y → y < xs → 0 < W2.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : W2.eval y ≤ 0 := by
      rcases lt_total 0 (W2.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hyb : y < b := lt_trans_ax hy2 hxsb
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlb y ⟨hy1, hyb, hyle⟩) hy2)
  have hcontW2xs : ContinuousAt W2.eval xs :=
    eml_continuousAt_of_no_crossing W2 xs (hncW2 xs hx0xs hxsb)
  have hxsle : W2.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < W2.eval xs := by
      rcases lt_total (W2.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ := pos_nbhd_of_continuousAt hcontW2xs hxsgt
    have hbound2 : ∀ y, (x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) → xs + δ ≤ y := by
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
  rcases (le_iff_lt_or_eq x0 xs).mp hx0xs with hx0xslt | hx0xseq
  · -- x0 < xs: local bounds at xs give a δ bounded away from 0; place y just below xs.
    have hxsge0 : 0 ≤ W2.eval xs :=
      @nonneg_at_of_pos_below W2.eval x0 xs hx0xslt hcontW2xs hposbelow
    have hxseq0 : W2.eval xs = 0 := (le_antisymm hxsge0 hxsle).symm
    have hcontW1xs : ContinuousAt W1.eval xs :=
      eml_continuousAt_of_no_crossing W1 xs (hncW1 xs hx0xs hxsb)
    obtain ⟨ρ1, hρ1, hb1⟩ := bdd_below_nbhd_of_continuousAt hcontW1xs
    obtain ⟨ρCs, hρCs, hbCs⟩ := chain_radius xs Cs (fun c hc => hncCs c hc xs hx0xs hxsb)
    let M : EMLTree → Real := fun c => max 0 (Real.log (c.eval xs + 1))
    let S : Real := listLogSum M Cs
    have hMbound : ∀ y, abs (y - xs) < ρCs → ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c := by
      intro y hy c hc
      exact log_le_of_le (le_of_lt (hbCs y hy c hc))
    have hρpos : 0 < min ρ1 ρCs := iv_ltmin hρ1 hρCs
    let δfixed : Real := Real.exp (Real.exp (W1.eval xs - 1) - (1 + 1 + S))
    have hδfixedpos : 0 < δfixed := Real.exp_pos _
    obtain ⟨ρW2, hρW2, hnbhdW2⟩ := hcontW2xs δfixed hδfixedpos
    have hρfinalpos : 0 < min (min ρ1 ρCs) ρW2 := iv_ltmin hρpos hρW2
    obtain ⟨y, hy1, hy2⟩ := exists_between (max x0 (xs - min (min ρ1 ρCs) ρW2)) xs
      (iv_ltmax hx0xslt (iv_subself xs hρfinalpos))
    have hyx0 : x0 ≤ y :=
      le_of_lt_r (lt_of_le_of_lt (le_max_left x0 (xs - min (min ρ1 ρCs) ρW2)) hy1)
    have hyxsρfinal : xs - min (min ρ1 ρCs) ρW2 < y :=
      lt_of_le_of_lt (le_max_right x0 (xs - min (min ρ1 ρCs) ρW2)) hy1
    have hyabs : abs (y - xs) < min (min ρ1 ρCs) ρW2 := by
      rw [iv_absub (le_of_lt_r hy2)]
      have h2 := add_lt_add_left hyxsρfinal (min (min ρ1 ρCs) ρW2)
      rw [show min (min ρ1 ρCs) ρW2 + (xs - min (min ρ1 ρCs) ρW2) = xs from by mach_ring,
          show min (min ρ1 ρCs) ρW2 + y = y + min (min ρ1 ρCs) ρW2 from by mach_ring] at h2
      have h3 := add_lt_add_left h2 (-y)
      rw [show -y + xs = xs - y from by mach_mpoly [xs, y],
          show -y + (y + min (min ρ1 ρCs) ρW2) = min (min ρ1 ρCs) ρW2
            from by mach_mpoly [y, min (min ρ1 ρCs) ρW2]] at h3
      exact h3
    have hyρ : abs (y - xs) < min ρ1 ρCs := lt_of_lt_of_le hyabs (min_le_left (min ρ1 ρCs) ρW2)
    have hyρW2 : abs (y - xs) < ρW2 := lt_of_lt_of_le hyabs (min_le_right (min ρ1 ρCs) ρW2)
    have hyρ1 : abs (y - xs) < ρ1 := lt_of_lt_of_le hyρ (min_le_left ρ1 ρCs)
    have hyρCs : abs (y - xs) < ρCs := lt_of_lt_of_le hyρ (min_le_right ρ1 ρCs)
    have hposy : 0 < W2.eval y := hposbelow y hyx0 hy2
    have hW2ysmall : W2.eval y < δfixed := by
      have habs2 : abs (W2.eval y - W2.eval xs) < δfixed := hnbhdW2 y hyρW2
      rw [hxseq0, sub_zero] at habs2
      exact lt_of_abs_lt habs2
    have hM_y : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c := hMbound y hyρCs
    have hW1lb : W1.eval xs - 1 < W1.eval y := hb1 y hyρ1
    have hstep1 : Real.exp (W1.eval xs - 1) < Real.exp (W1.eval y) := Real.exp_lt hW1lb
    have hstep2 : Real.exp (W1.eval xs - 1) - (1 + 1 + S) < Real.exp (W1.eval y) - (1 + 1 + S) := by
      have h2 := add_lt_add_left hstep1 (-(1 + 1 + S))
      rwa [show -(1 + 1 + S) + Real.exp (W1.eval xs - 1) = Real.exp (W1.eval xs - 1) - (1 + 1 + S)
            from by mach_mpoly [Real.exp (W1.eval xs - 1), S],
          show -(1 + 1 + S) + Real.exp (W1.eval y) = Real.exp (W1.eval y) - (1 + 1 + S)
            from by mach_mpoly [Real.exp (W1.eval y), S]] at h2
    have hδlt : δfixed < Real.exp (Real.exp (W1.eval y) - (1 + 1 + S)) := Real.exp_lt hstep2
    have hfinallt : W2.eval y < Real.exp (Real.exp (W1.eval y) - (1 + 1 + S)) :=
      lt_trans_ax hW2ysmall hδlt
    exact eml_leftchain_sin_contradiction_exact Cs y M hM_y hsin hposy hfinallt
  · -- x0 = xs: hx0pos and hxsle contradict outright.
    rw [← hx0xseq] at hxsle
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hx0pos hxsle)

/-! ## Honest status: what this closes, and what's still open

`eml_leftchain_pos_of_no_crossing` fully closes the "right-then-all-left" class — any tree of the
shape `wrapLeft Cs (eml W1 W2)`, for `Cs` of ANY length — given a positivity witness at some `x0`
and no-crossing throughout `[x0,b)` for `W1`, `W2`, and every sibling in the chain. Round 11's
originally-flagged obstacle ("δ needs a two-sided bound, needing interval-wide EVT") turned out to
be resolvable with LOCAL bounds at the single point `xs` alone — `bdd_below_nbhd_of_continuousAt`
(one new small lemma) plus the ALREADY-available `bdd_above_nbhd_of_continuousAt`, combined with an
explicit-formula (not existential) restatement of the blow-up chain so the resulting `δ`'s
dependence on `W1.eval y` could be bounded directly via monotonicity. What looked like "needs new
EVT machinery" was actually "needs bookkeeping" — a real, useful downgrade in the finding's own
right, not just a code deliverable.

**What remains genuinely open:** (1) the pure left-descent witness problem (round 9.5/10) — an
exp-side node's own log-child still has no anchor for determining ITS sign, independent of this
chain mechanism; (2) generalizing beyond "right-then-all-left" to arbitrary interleavings of left
and right steps, which is what the full, unrestricted axiom needs. This theorem is a genuine
enlargement of provable territory (arbitrary depth for one large, well-defined class of shapes,
matching depth-1's completeness for that class) but the axiom itself quantifies over ALL tree
shapes, so it is not yet closed. -/

/-! ## Extending the reach: one trailing `R` step at the root

The state-machine analysis (round 5's docstring, above) says state `A` (forceable arbitrarily
large) survives any run of `L` steps and flips to `B` on an `R` step, but `B` ALWAYS dies on the
very next step, whichever kind. This means the value-blow-up mechanism's FULL reach — not just the
"stop after the L's" case just closed — is `R L* R?`: the mandatory first `R`, an arbitrary run of
`L`s, and OPTIONALLY one more trailing `R`, PROVIDED that trailing `R` is the root (nothing can
follow it). This section builds that trailing-`R` extension: `eml D (wrapLeft Cs (eml W1 W2))`,
offender `W2`, using `log`'s unboundedness ABOVE (`log_unbounded_above`, round 5) the same way the
base case used it below, plus `neg_one_le_sin` for the other side of the sin bound. -/

/-- Explicit-δ mirror of `log_lt_of_lt_exp`: if `y` exceeds `exp M`, `log y` exceeds `M`. Same
derivation as `log_unbounded_above`'s internal fact, exposed directly (not behind its
existential) so it can be chained with `chain_exact`'s own explicit output. -/
theorem log_gt_of_gt_exp {y M : Real} (hy : Real.exp M < y) : M < Real.log y := by
  have hypos : (0 : Real) < y := lt_trans_ax (Real.exp_pos M) hy
  have heq : Real.exp (Real.log y) = y := Real.exp_log hypos
  apply exp_reflect_lt
  rw [heq]
  exact hy

/-- **The trailing-`R` step, explicit.** If a node's log-argument `N` is known to exceed a
threshold forcing `log(N.eval y)` above `exp(D.eval y) - L`, the WHOLE `eml D N` node is forced
BELOW `L` — the mirror image of `eml_rootstep_exceeds_exact`, one level up. `EMLTree.eval`'s `log`
is already the clamped total function, so no positivity side-condition on `N.eval y` is needed for
the formula itself. -/
theorem eml_rootR_step_exact (D N : EMLTree) (y L : Real)
    (hK : Real.exp (D.eval y) - L < Real.log (N.eval y)) :
    (EMLTree.eml D N).eval y < L := by
  show Real.exp (D.eval y) - Real.log (N.eval y) < L
  have h2 := neg_lt_neg hK
  have h3 := add_lt_add_left h2 (Real.exp (D.eval y))
  rwa [show Real.exp (D.eval y) + -(Real.log (N.eval y)) = Real.exp (D.eval y) - Real.log (N.eval y)
        from by mach_mpoly [Real.exp (D.eval y), Real.log (N.eval y)],
      show Real.exp (D.eval y) + -(Real.exp (D.eval y) - L) = L
        from by mach_mpoly [Real.exp (D.eval y), L]] at h3

/-- **The trailing-`R` contradiction, explicit.** Combines `chain_exact` (forcing the whole
left-chain `wrapLeft Cs (eml W1 W2)` arbitrarily large) with `log_gt_of_gt_exp` (forcing its log
arbitrarily large too) and `eml_rootR_step_exact` (forcing the ROOT, `eml D (...)`, arbitrarily
negative) — contradicting `neg_one_le_sin`, the other side of the sin bound from
`eml_leftchain_sin_contradiction_exact`'s `sin_le_one`. -/
theorem eml_leftchain_rootlog_sin_contradiction_exact {W1 W2 D : EMLTree} (Cs : List EMLTree)
    (y : Real) (M : EMLTree → Real) (hM : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c)
    (hsin : ∀ x : Real, (EMLTree.eml D (wrapLeft Cs (EMLTree.eml W1 W2))).eval x = Real.sin x)
    (hpos : 0 < W2.eval y)
    (hlt : W2.eval y < Real.exp (Real.exp (W1.eval y) -
      (Real.exp (Real.exp (D.eval y) - (-1 - 1)) + listLogSum M Cs))) :
    False := by
  have hbase : ∀ L, 0 < W2.eval y → W2.eval y < Real.exp (Real.exp (W1.eval y) - L) →
      L < (EMLTree.eml W1 W2).eval y :=
    fun L hp hl => eml_rightstep_exceeds_exact W1 W2 y L hp hl
  have h2 : Real.exp (Real.exp (D.eval y) - (-1 - 1)) <
      (wrapLeft Cs (EMLTree.eml W1 W2)).eval y :=
    chain_exact Cs M hM hbase (Real.exp (Real.exp (D.eval y) - (-1 - 1))) hpos hlt
  have h3 : Real.exp (D.eval y) - (-1 - 1) < Real.log ((wrapLeft Cs (EMLTree.eml W1 W2)).eval y) :=
    log_gt_of_gt_exp h2
  have h4 : (EMLTree.eml D (wrapLeft Cs (EMLTree.eml W1 W2))).eval y < -1 - 1 :=
    eml_rootR_step_exact D (wrapLeft Cs (EMLTree.eml W1 W2)) y (-1 - 1) h3
  rw [hsin y] at h4
  have hlt1 : (-1 : Real) - 1 < -1 := by
    have h5 := add_lt_add_left (neg_neg_of_pos zero_lt_one_ax) (-1)
    rwa [add_zero, show (-1 : Real) + -1 = -1 - 1 from by mach_ring] at h5
  have hcombine : (-1 : Real) < -1 - 1 := lt_of_le_of_lt (neg_one_le_sin y) h4
  exact lt_irrefl_ax (-1) (lt_trans_ax hcombine hlt1)

/-- **Full closure for the "right-then-all-left-then-root-right" class.** Same shape as
`eml_leftchain_pos_of_no_crossing`, but for `t = eml D (wrapLeft Cs (eml W1 W2))` — one trailing
`R` step wrapping the whole left-chain at the root. Needs an EXTRA local bound (`D` bounded ABOVE
near the minimal-violation point `xs`, via `bdd_above_nbhd_of_continuousAt` — the same tool
already used for the chain siblings, just applied to `D` this time) composed with the existing `W1`
lower bound and chain bound via TWO chained monotonicity steps instead of one. -/
theorem eml_leftchain_rootR_pos_of_no_crossing {W1 W2 D : EMLTree} (Cs : List EMLTree)
    (x0 b : Real) (hx0b : x0 < b)
    (hncD : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt D x)
    (hncW1 : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt W1 x)
    (hncW2 : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt W2 x)
    (hncCs : ∀ c ∈ Cs, ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt c x)
    (hsin : ∀ x : Real, (EMLTree.eml D (wrapLeft Cs (EMLTree.eml W1 W2))).eval x = Real.sin x)
    (hx0pos : 0 < W2.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < W2.eval x := by
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : W2.eval x ≤ 0 := by
    rcases lt_total 0 (W2.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedBelow (fun y => x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) := ⟨x0, fun y hy => hy.1⟩
  obtain ⟨xs, hlb, hglb⟩ := inf_exists _ hSne hSbd
  have hx0xs : x0 ≤ xs := hglb x0 (fun y hy => hy.1)
  have hxsb : xs < b := lt_of_le_of_lt (hlb x ⟨hx1, hx2, hxle⟩) hx2
  have hposbelow : ∀ y, x0 ≤ y → y < xs → 0 < W2.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : W2.eval y ≤ 0 := by
      rcases lt_total 0 (W2.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hyb : y < b := lt_trans_ax hy2 hxsb
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlb y ⟨hy1, hyb, hyle⟩) hy2)
  have hcontW2xs : ContinuousAt W2.eval xs :=
    eml_continuousAt_of_no_crossing W2 xs (hncW2 xs hx0xs hxsb)
  have hxsle : W2.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < W2.eval xs := by
      rcases lt_total (W2.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ := pos_nbhd_of_continuousAt hcontW2xs hxsgt
    have hbound2 : ∀ y, (x0 ≤ y ∧ y < b ∧ W2.eval y ≤ 0) → xs + δ ≤ y := by
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
  rcases (le_iff_lt_or_eq x0 xs).mp hx0xs with hx0xslt | hx0xseq
  · have hxsge0 : 0 ≤ W2.eval xs :=
      @nonneg_at_of_pos_below W2.eval x0 xs hx0xslt hcontW2xs hposbelow
    have hxseq0 : W2.eval xs = 0 := (le_antisymm hxsge0 hxsle).symm
    have hcontW1xs : ContinuousAt W1.eval xs :=
      eml_continuousAt_of_no_crossing W1 xs (hncW1 xs hx0xs hxsb)
    have hcontDxs : ContinuousAt D.eval xs :=
      eml_continuousAt_of_no_crossing D xs (hncD xs hx0xs hxsb)
    obtain ⟨ρ1, hρ1, hb1⟩ := bdd_below_nbhd_of_continuousAt hcontW1xs
    obtain ⟨ρD, hρD, hbD⟩ := bdd_above_nbhd_of_continuousAt hcontDxs
    obtain ⟨ρCs, hρCs, hbCs⟩ := chain_radius xs Cs (fun c hc => hncCs c hc xs hx0xs hxsb)
    let M : EMLTree → Real := fun c => max 0 (Real.log (c.eval xs + 1))
    let S : Real := listLogSum M Cs
    have hMbound : ∀ y, abs (y - xs) < ρCs → ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c := by
      intro y hy c hc
      exact log_le_of_le (le_of_lt (hbCs y hy c hc))
    let Bfixed : Real := Real.exp (Real.exp (D.eval xs + 1) - (-1 - 1)) + S
    let δfixed : Real := Real.exp (Real.exp (W1.eval xs - 1) - Bfixed)
    have hδfixedpos : 0 < δfixed := Real.exp_pos _
    obtain ⟨ρW2, hρW2, hnbhdW2⟩ := hcontW2xs δfixed hδfixedpos
    have hρpos : 0 < min (min ρ1 ρD) (min ρCs ρW2) :=
      iv_ltmin (iv_ltmin hρ1 hρD) (iv_ltmin hρCs hρW2)
    obtain ⟨y, hy1, hy2⟩ := exists_between (max x0 (xs - min (min ρ1 ρD) (min ρCs ρW2))) xs
      (iv_ltmax hx0xslt (iv_subself xs hρpos))
    have hyx0 : x0 ≤ y :=
      le_of_lt_r (lt_of_le_of_lt (le_max_left x0 (xs - min (min ρ1 ρD) (min ρCs ρW2))) hy1)
    have hyxsrho : xs - min (min ρ1 ρD) (min ρCs ρW2) < y :=
      lt_of_le_of_lt (le_max_right x0 (xs - min (min ρ1 ρD) (min ρCs ρW2))) hy1
    have hyabs : abs (y - xs) < min (min ρ1 ρD) (min ρCs ρW2) := by
      rw [iv_absub (le_of_lt_r hy2)]
      have h2 := add_lt_add_left hyxsrho (min (min ρ1 ρD) (min ρCs ρW2))
      rw [show min (min ρ1 ρD) (min ρCs ρW2) + (xs - min (min ρ1 ρD) (min ρCs ρW2)) = xs
            from by mach_ring,
          show min (min ρ1 ρD) (min ρCs ρW2) + y = y + min (min ρ1 ρD) (min ρCs ρW2)
            from by mach_ring] at h2
      have h3 := add_lt_add_left h2 (-y)
      rw [show -y + xs = xs - y from by mach_mpoly [xs, y],
          show -y + (y + min (min ρ1 ρD) (min ρCs ρW2)) = min (min ρ1 ρD) (min ρCs ρW2)
            from by mach_mpoly [y, min (min ρ1 ρD) (min ρCs ρW2)]] at h3
      exact h3
    have hyρ1D : abs (y - xs) < min ρ1 ρD := lt_of_lt_of_le hyabs (min_le_left _ _)
    have hyρCsW2 : abs (y - xs) < min ρCs ρW2 := lt_of_lt_of_le hyabs (min_le_right _ _)
    have hyρ1 : abs (y - xs) < ρ1 := lt_of_lt_of_le hyρ1D (min_le_left ρ1 ρD)
    have hyρD : abs (y - xs) < ρD := lt_of_lt_of_le hyρ1D (min_le_right ρ1 ρD)
    have hyρCs : abs (y - xs) < ρCs := lt_of_lt_of_le hyρCsW2 (min_le_left ρCs ρW2)
    have hyρW2 : abs (y - xs) < ρW2 := lt_of_lt_of_le hyρCsW2 (min_le_right ρCs ρW2)
    have hposy : 0 < W2.eval y := hposbelow y hyx0 hy2
    have hW2ysmall : W2.eval y < δfixed := by
      have habs2 : abs (W2.eval y - W2.eval xs) < δfixed := hnbhdW2 y hyρW2
      rw [hxseq0, sub_zero] at habs2
      exact lt_of_abs_lt habs2
    have hM_y : ∀ c ∈ Cs, Real.log (c.eval y) ≤ M c := hMbound y hyρCs
    have hDub : D.eval y < D.eval xs + 1 := hbD y hyρD
    have hBstep1 : Real.exp (D.eval y) < Real.exp (D.eval xs + 1) := Real.exp_lt hDub
    have hBstep2 : Real.exp (D.eval y) - (-1 - 1) < Real.exp (D.eval xs + 1) - (-1 - 1) := by
      have h2 := add_lt_add_left hBstep1 (-(-1 - 1))
      rwa [show -(-1 - 1) + Real.exp (D.eval y) = Real.exp (D.eval y) - (-1 - 1)
            from by mach_mpoly [Real.exp (D.eval y)],
          show -(-1 - 1) + Real.exp (D.eval xs + 1) = Real.exp (D.eval xs + 1) - (-1 - 1)
            from by mach_mpoly [Real.exp (D.eval xs + 1)]] at h2
    have hBstep3 : Real.exp (Real.exp (D.eval y) - (-1 - 1)) <
        Real.exp (Real.exp (D.eval xs + 1) - (-1 - 1)) := Real.exp_lt hBstep2
    have hBcmp : Real.exp (Real.exp (D.eval y) - (-1 - 1)) + S < Bfixed := by
      show Real.exp (Real.exp (D.eval y) - (-1 - 1)) + S
          < Real.exp (Real.exp (D.eval xs + 1) - (-1 - 1)) + S
      have h2 := add_lt_add_left hBstep3 S
      rwa [add_comm S (Real.exp (Real.exp (D.eval y) - (-1 - 1))),
          add_comm S (Real.exp (Real.exp (D.eval xs + 1) - (-1 - 1)))] at h2
    have hW1lb : W1.eval xs - 1 < W1.eval y := hb1 y hyρ1
    have hstep1 : Real.exp (W1.eval xs - 1) < Real.exp (W1.eval y) := Real.exp_lt hW1lb
    have hinner : Real.exp (W1.eval xs - 1) - Bfixed <
        Real.exp (W1.eval y) - (Real.exp (Real.exp (D.eval y) - (-1 - 1)) + S) := by
      have h2 := add_lt_add hstep1 (neg_lt_neg hBcmp)
      rwa [← sub_def, ← sub_def] at h2
    have hδlt : δfixed <
        Real.exp (Real.exp (W1.eval y) - (Real.exp (Real.exp (D.eval y) - (-1 - 1)) + S)) :=
      Real.exp_lt hinner
    have hfinallt : W2.eval y <
        Real.exp (Real.exp (W1.eval y) - (Real.exp (Real.exp (D.eval y) - (-1 - 1)) + S)) :=
      lt_trans_ax hW2ysmall hδlt
    exact eml_leftchain_rootlog_sin_contradiction_exact Cs y M hM_y hsin hposy hfinallt
  · rw [← hx0xseq] at hxsle
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hx0pos hxsle)

/-! ## Toward the left-descent witness problem: an unconditional value formula for exp-children

Round 9.5/10's finding was that only right-descent nodes get explicit VALUE representations — the
`k·E` mechanism for an offender `t2` uses `exp∘log = id` on the POSITIVE reals (`exp_log`), which
needs `t2.eval x > 0` already established, so it can't hand out a value-based witness for free.

Re-examining: the LEFT (exp) child `N` of a node `eml N C` whose OWN value is known (`= target`,
e.g. because that node IS the root and `target = sin x`) gets an explicit value formula for a
DIFFERENT reason — `log∘exp = id` (`log_exp`) holds UNCONDITIONALLY, for every real input, not just
the positive ones. Rearranging `exp(N.eval x) − log(C.eval x) = target` to
`exp(N.eval x) = target + log(C.eval x)` and taking `log` of both sides needs no side condition at
all: this is exactly the asymmetry that makes the LEFT branch tractable where the right branch
wasn't. This turns "does `N`'s own log-child cross zero" into a problem with a FREE explicit target
(`log(target + log(C.eval x))` in place of `sin x`) — the same shape depth-1 already solves, one
level removed, via `eml_ode_step_general` (which never actually required its known-derivative
target to BE `cos x` — any known value works). Not yet assembled into a full closure theorem (that
would mean re-deriving depth-1's whole apparatus — witness, ODE, constant-ratio, minimal-violation
point — parametrized over an ARBITRARY known target instead of hardcoding `sin`/`cos` throughout),
but this is the missing piece that was blocking left-descent, isolated and verified. -/

/-- **Unconditional explicit value for an exp-child.** If `eml N C` (with `N` the exp/left branch)
takes a KNOWN value `target` at `x`, `N` itself has an explicit closed form there — no positivity
or validity assumption on `N` or `C` needed, since it uses `log∘exp = id` (`Real.log_exp`), which
holds for every real input unconditionally (unlike `exp∘log_clamped = id`, which needs positivity
and is exactly why the analogous fact fails for the RIGHT/log child). -/
theorem eml_leftchild_explicit_value (N C : EMLTree) (x target : Real)
    (heq : (EMLTree.eml N C).eval x = target) :
    N.eval x = Real.log (target + Real.log (C.eval x)) := by
  have h1 : Real.exp (N.eval x) - Real.log (C.eval x) = target := heq
  have h2 : Real.exp (N.eval x) = target + Real.log (C.eval x) := by
    have h3 : Real.exp (N.eval x) - Real.log (C.eval x) + Real.log (C.eval x)
        = target + Real.log (C.eval x) := by rw [h1]
    rwa [sub_def, add_assoc, neg_add_self, add_zero] at h3
  rw [← h2]
  exact (Real.log_exp (N.eval x)).symm

/-! ## The left-descent closure, attempted in full

`eml_leftchild_explicit_value` turns "does `(eml S2 S3)`'s log-child cross zero" into a depth-1
shaped problem with a COMPUTED target (`log(sin x + log(C.eval x))`) standing in for `sin` — and
`eml_ode_step_general`/`eml_E_step_general` (round 9) were already depth-independent, never
actually requiring their known-derivative input to be `cos x` specifically. This section reuses
BOTH exactly as-is, needing only ONE new piece: `(eml S2 S3)`'s own derivative, computed directly
from the closed-form target (via `HasDerivAt_of_eq`) instead of via structural descent — the same
"free transfer" trick that gave depth-1's ROOT its derivative, one level down. -/

/-- **`(eml S2 S3)`'s own derivative, for free.** Given `t = eml (eml S2 S3) C` agrees with `sin`
and `C` is differentiable with `C.eval x ≠ 0`, `(eml S2 S3)` is differentiable at `x` — computed by
differentiating `log(sin x + log(C.eval x))` directly (chain rule through `log`, `+`, `sin`, and
`log∘C.eval`) and transferring via `HasDerivAt_of_eq` using `eml_leftchild_explicit_value` as the
global equality. The inner sum `sin x + log(C.eval x)` is ALWAYS strictly positive — it equals
`exp((eml S2 S3).eval x)`, forced by `hsin` alone — so no case split is needed for the OUTER `log`,
only for `log∘C.eval`'s own derivative (`C.eval x`'s sign, exactly as `EMLNoCrossingAt` already
handles elsewhere). -/
theorem eml_leftdescent_N_hasDerivAt {S2 S3 C : EMLTree} {x c : Real}
    (hsin : ∀ z : Real, (EMLTree.eml (EMLTree.eml S2 S3) C).eval z = Real.sin z)
    (hc : HasDerivAt C.eval c x) (hCne : C.eval x ≠ 0) :
    ∃ D : Real, HasDerivAt (EMLTree.eml S2 S3).eval D x := by
  have hlogC : ∃ dC, HasDerivAt (fun z => Real.log (C.eval z)) dC x := by
    rcases lt_total (C.eval x) 0 with hlt | heq | hgt
    · exact ⟨0 * c, HasDerivAt_comp Real.log C.eval c 0 x hc (HasDerivAt_log_neg hlt)⟩
    · exact absurd heq hCne
    · exact ⟨1 / C.eval x * c,
        HasDerivAt_comp Real.log C.eval c (1 / C.eval x) x hc (HasDerivAt_log_pos _ hgt)⟩
  obtain ⟨dC, hdC⟩ := hlogC
  have hsum : HasDerivAt (fun z => Real.sin z + Real.log (C.eval z)) (Real.cos x + dC) x :=
    HasDerivAt_add Real.sin (fun z => Real.log (C.eval z)) (Real.cos x) dC x (HasDerivAt_sin x) hdC
  have hsumpos : 0 < Real.sin x + Real.log (C.eval x) := by
    have heq2 : Real.exp ((EMLTree.eml S2 S3).eval x) = Real.sin x + Real.log (C.eval x) := by
      have h1 : Real.exp ((EMLTree.eml S2 S3).eval x) - Real.log (C.eval x) = Real.sin x := hsin x
      have h2 : Real.exp ((EMLTree.eml S2 S3).eval x) - Real.log (C.eval x) + Real.log (C.eval x)
          = Real.sin x + Real.log (C.eval x) := by rw [h1]
      rwa [sub_def, add_assoc, neg_add_self, add_zero] at h2
    rw [← heq2]
    exact Real.exp_pos _
  have hRHSderiv : HasDerivAt (fun z => Real.log (Real.sin z + Real.log (C.eval z)))
      (1 / (Real.sin x + Real.log (C.eval x)) * (Real.cos x + dC)) x :=
    HasDerivAt_comp Real.log (fun z => Real.sin z + Real.log (C.eval z)) (Real.cos x + dC)
      (1 / (Real.sin x + Real.log (C.eval x))) x hsum (HasDerivAt_log_pos _ hsumpos)
  exact ⟨1 / (Real.sin x + Real.log (C.eval x)) * (Real.cos x + dC),
    HasDerivAt_of_eq (fun z => Real.log (Real.sin z + Real.log (C.eval z)))
      (EMLTree.eml S2 S3).eval _ x
      (fun z => (eml_leftchild_explicit_value (EMLTree.eml S2 S3) C z (Real.sin z) (hsin z)).symm)
      hRHSderiv⟩

/-- **Left-descent positivity propagation — the left-descent analogue of
`eml_depth1_pos_of_pos_witness`.** If `t = eml (eml S2 S3) C` agrees with `sin` on `[x0,b)`, `C`
never crosses zero there, `S3` is positive at the witness `x0`, and `S2`/`S3`/`C` are
differentiable throughout `[x0,b)`, `S3` stays positive on the WHOLE of `[x0,b)`. Same
minimal-violation-point proof shape as depth-1 (`inf_exists`, the `k·E` constant-ratio fact,
`eq_zero_at_of_eq_zero_below`), with `(eml S2 S3)`'s free derivative (`eml_leftdescent_N_hasDerivAt`
above) standing in for the free root derivative, and `eml_ode_step_general`/`eml_E_step_general`
(unchanged, round 9) standing in for `eml_depth1_t2_ode`/`eml_depth1_E_deriv`. -/
theorem eml_leftdescent_pos_of_pos_witness {S2 S3 C : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml (EMLTree.eml S2 S3) C).eval x = Real.sin x)
    (x0 b : Real) (hx0b : x0 < b)
    (S2' : Real → Real) (hS2'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S2.eval (S2' x) x)
    (S3' : Real → Real) (hS3'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S3.eval (S3' x) x)
    (C' : Real → Real) (hC'd : ∀ x, x0 ≤ x → x < b → HasDerivAt C.eval (C' x) x)
    (hCne : ∀ x, x0 ≤ x → x < b → C.eval x ≠ 0)
    (hx0pos : 0 < S3.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < S3.eval x := by
  have hNd : ∀ x, x0 ≤ x → x < b →
      ∃ D : Real, HasDerivAt (EMLTree.eml S2 S3).eval D x :=
    fun x hx1 hx2 => eml_leftdescent_N_hasDerivAt hsin (hC'd x hx1 hx2) (hCne x hx1 hx2)
  let Dfun : Real → Real := fun z => if h : x0 ≤ z ∧ z < b then (hNd z h.1 h.2).choose else 0
  have hDfund : ∀ z, x0 ≤ z → z < b → HasDerivAt (EMLTree.eml S2 S3).eval (Dfun z) z := by
    intro z hz1 hz2
    show HasDerivAt (EMLTree.eml S2 S3).eval
      (if h : x0 ≤ z ∧ z < b then (hNd z h.1 h.2).choose else 0) z
    rw [dif_pos ⟨hz1, hz2⟩]
    exact (hNd z hz1 hz2).choose_spec
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : S3.eval x ≤ 0 := by
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => x0 ≤ y ∧ y < b ∧ S3.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedBelow (fun y => x0 ≤ y ∧ y < b ∧ S3.eval y ≤ 0) := ⟨x0, fun y hy => hy.1⟩
  obtain ⟨xs, hlb, hglb⟩ := inf_exists _ hSne hSbd
  have hx0xs : x0 ≤ xs := hglb x0 (fun y hy => hy.1)
  have hxsb : xs < b := lt_of_le_of_lt (hlb x ⟨hx1, hx2, hxle⟩) hx2
  have hposbelow : ∀ y, x0 ≤ y → y < xs → 0 < S3.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : S3.eval y ≤ 0 := by
      rcases lt_total 0 (S3.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hyb : y < b := lt_trans_ax hy2 hxsb
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlb y ⟨hy1, hyb, hyle⟩) hy2)
  have hxsle : S3.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < S3.eval xs := by
      rcases lt_total (S3.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ :=
      pos_nbhd_of_continuousAt (hasDerivAt_continuousAt (hS3'd xs hx0xs hxsb)) hxsgt
    have hbound2 : ∀ y, (x0 ≤ y ∧ y < b ∧ S3.eval y ≤ 0) → xs + δ ≤ y := by
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
  let E1 : Real → Real := fun z => Real.exp (Real.exp (S2.eval z) - (EMLTree.eml S2 S3).eval z)
  have hE1pos : ∀ z, 0 < E1 z := fun z => Real.exp_pos _
  let k : Real := S3.eval x0 * (1 / E1 x0)
  have hkE1x0 : k * E1 x0 = S3.eval x0 := by
    show S3.eval x0 * (1 / E1 x0) * E1 x0 = S3.eval x0
    rw [mul_assoc, mul_comm (1 / E1 x0) (E1 x0), mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
        mul_one_ax]
  have hkpos : 0 < k := mul_pos hx0pos (one_div_pos_of_pos (hE1pos x0))
  have hS3ode : ∀ z, x0 ≤ z → z < xs →
      HasDerivAt S3.eval (S3.eval z * (Real.exp (S2.eval z) * S2' z - Dfun z)) z := by
    intro z hz1 hz2
    have hzb : z < b := lt_trans_ax hz2 hxsb
    have heq := eml_ode_step_general (hDfund z hz1 hzb) (hS2'd z hz1 hzb) (hS3'd z hz1 hzb)
      (hposbelow z hz1 hz2)
    have hderiv := hS3'd z hz1 hzb
    rwa [heq] at hderiv
  have hE1ode : ∀ z, x0 ≤ z → z < xs →
      HasDerivAt E1 (E1 z * (Real.exp (S2.eval z) * S2' z - Dfun z)) z := by
    intro z hz1 hz2
    have hzb : z < b := lt_trans_ax hz2 hxsb
    exact eml_E_step_general (hS2'd z hz1 hzb) (hDfund z hz1 hzb)
  have hzero : ∀ y, x0 ≤ y → y < xs → S3.eval y - k * E1 y = 0 := by
    intro y hy1 hy2
    rcases (le_iff_lt_or_eq x0 y).mp hy1 with hlt | heq
    · obtain ⟨k', hk'⟩ := const_ratio_of_shared_ode S3.eval E1
        (fun z => Real.exp (S2.eval z) * S2' z - Dfun z) x0 y hlt
        (fun z hz1 hz2 => hS3ode z hz1 (lt_of_le_of_lt hz2 hy2))
        (fun z hz1 hz2 => hE1ode z hz1 (lt_of_le_of_lt hz2 hy2))
        (fun z _ _ => (ne_of_lt (hE1pos z)).symm)
      have hkx0 : S3.eval x0 = k' * E1 x0 := hk' x0 (le_refl x0) (le_of_lt hlt)
      have hkeq : k' = k := by
        have h2 : k' * E1 x0 = k * E1 x0 := by rw [← hkx0, hkE1x0]
        have h3 : k' * E1 x0 * (1 / E1 x0) = k * E1 x0 * (1 / E1 x0) := by rw [h2]
        rwa [mul_assoc, mul_assoc, mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
            mul_one_ax, mul_one_ax] at h3
      have hky : S3.eval y = k' * E1 y := hk' y hy1 (le_refl y)
      rw [hky, hkeq, sub_def, add_neg]
    · rw [← heq, hkE1x0, sub_def, add_neg]
  have hxsE1pos : 0 < k * E1 xs := mul_pos hkpos (hE1pos xs)
  have hxseq2 : S3.eval xs = k * E1 xs := by
    rcases (le_iff_lt_or_eq x0 xs).mp hx0xs with hx0xslt | hx0xseq
    · have hcontdiff : HasDerivAt (fun z => S3.eval z - k * E1 z)
          (S3' xs - (0 * E1 xs + k * (E1 xs * (Real.exp (S2.eval xs) * S2' xs - Dfun xs)))) xs :=
        HasDerivAt_sub S3.eval (fun z => k * E1 z) (S3' xs)
          (0 * E1 xs + k * (E1 xs * (Real.exp (S2.eval xs) * S2' xs - Dfun xs))) xs
          (hS3'd xs hx0xs hxsb)
          (HasDerivAt_mul (fun _ => k) E1 0 (E1 xs * (Real.exp (S2.eval xs) * S2' xs - Dfun xs)) xs
            (HasDerivAt_const k xs) (eml_E_step_general (hS2'd xs hx0xs hxsb) (hDfund xs hx0xs hxsb)))
      have hxseq : S3.eval xs - k * E1 xs = 0 :=
        @eq_zero_at_of_eq_zero_below (fun z => S3.eval z - k * E1 z) x0 xs hx0xslt
          (hasDerivAt_continuousAt hcontdiff) hzero
      have h2 : S3.eval xs - k * E1 xs + k * E1 xs = 0 + k * E1 xs := by rw [hxseq]
      rwa [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
    · rw [← hx0xseq, hkE1x0]
  have hfinal : k * E1 xs ≤ 0 := hxseq2 ▸ hxsle
  exact lt_irrefl_ax 0 (lt_of_lt_of_le hxsE1pos hfinal)

/-! ## Generalizing left-descent to arbitrary depth

`eml_leftdescent_pos_of_pos_witness`/`eml_leftdescent_N_hasDerivAt` hardcoded `Real.sin` as the
known target, one level in from the root. Neither actually needs to: `eml_leftchild_explicit_value`
already takes an arbitrary `target : Real`, and `eml_ode_step_general`/`eml_E_step_general` already
take an arbitrary known derivative `D`. This section makes that genericity explicit — parametrizing
both the derivative-propagation step and the closure theorem over an ABSTRACT known target function
— then chains the propagation step through an arbitrary-length LEFT SPINE (a list of siblings, one
per level), closing the offender at the BOTTOM of a left-descent of ANY depth, not just one level. -/

/-- **Generalized left-child derivative.** `eml_leftdescent_N_hasDerivAt` with `Real.sin` replaced
by an arbitrary known target function `TARGET` (with its own known derivative `d` at `x`) — same
proof, no other changes. This is what lets the mechanism chain: the OUTPUT of one application
(a node's own new known derivative) is exactly the right shape to be the INPUT `TARGET`/`hTarget`
of the next. -/
theorem eml_leftchild_hasDerivAt_general {A B : EMLTree} {x c d : Real} {TARGET : Real → Real}
    (heq : ∀ z : Real, (EMLTree.eml A B).eval z = TARGET z)
    (hTarget : HasDerivAt TARGET d x)
    (hc : HasDerivAt B.eval c x) (hBne : B.eval x ≠ 0) :
    ∃ D : Real, HasDerivAt A.eval D x := by
  have hlogB : ∃ dB, HasDerivAt (fun z => Real.log (B.eval z)) dB x := by
    rcases lt_total (B.eval x) 0 with hlt | heqB | hgt
    · exact ⟨0 * c, HasDerivAt_comp Real.log B.eval c 0 x hc (HasDerivAt_log_neg hlt)⟩
    · exact absurd heqB hBne
    · exact ⟨1 / B.eval x * c,
        HasDerivAt_comp Real.log B.eval c (1 / B.eval x) x hc (HasDerivAt_log_pos _ hgt)⟩
  obtain ⟨dB, hdB⟩ := hlogB
  have hsum : HasDerivAt (fun z => TARGET z + Real.log (B.eval z)) (d + dB) x :=
    HasDerivAt_add TARGET (fun z => Real.log (B.eval z)) d dB x hTarget hdB
  have hsumpos : 0 < TARGET x + Real.log (B.eval x) := by
    have heq2 : Real.exp (A.eval x) = TARGET x + Real.log (B.eval x) := by
      have h1 : Real.exp (A.eval x) - Real.log (B.eval x) = TARGET x := heq x
      have h2 : Real.exp (A.eval x) - Real.log (B.eval x) + Real.log (B.eval x)
          = TARGET x + Real.log (B.eval x) := by rw [h1]
      rwa [sub_def, add_assoc, neg_add_self, add_zero] at h2
    rw [← heq2]
    exact Real.exp_pos _
  have hRHSderiv : HasDerivAt (fun z => Real.log (TARGET z + Real.log (B.eval z)))
      (1 / (TARGET x + Real.log (B.eval x)) * (d + dB)) x :=
    HasDerivAt_comp Real.log (fun z => TARGET z + Real.log (B.eval z)) (d + dB)
      (1 / (TARGET x + Real.log (B.eval x))) x hsum (HasDerivAt_log_pos _ hsumpos)
  exact ⟨1 / (TARGET x + Real.log (B.eval x)) * (d + dB),
    HasDerivAt_of_eq (fun z => Real.log (TARGET z + Real.log (B.eval z)))
      A.eval _ x
      (fun z => (eml_leftchild_explicit_value A B z (TARGET z) (heq z)).symm)
      hRHSderiv⟩

/-- **Generalized ODE closure.** `eml_depth1_pos_of_pos_witness`/`eml_leftdescent_pos_of_pos_witness`
with `Real.cos x`/`Dfun` replaced by an arbitrary known-derivative function `D` for `eml A B` —
literally the SAME proof (minimal-violation point via `inf_exists`, the `k·E` constant-ratio fact,
continuity extension), since neither `eml_ode_step_general` nor `eml_E_step_general` ever cared
what `D` actually was. This single theorem SUBSUMES both — depth-1 is the case `D := cos`
(free from the root), left-descent-one-level is `D := ` the output of
`eml_leftchild_hasDerivAt_general` applied once; arbitrary left-spine depth (below) is the same `D`
applied through the chained propagation. -/
theorem eml_ode_closure_general {A B : EMLTree}
    (x0 b : Real) (hx0b : x0 < b)
    (A' : Real → Real) (hA'd : ∀ x, x0 ≤ x → x < b → HasDerivAt A.eval (A' x) x)
    (B' : Real → Real) (hB'd : ∀ x, x0 ≤ x → x < b → HasDerivAt B.eval (B' x) x)
    (D : Real → Real) (hDd : ∀ x, x0 ≤ x → x < b → HasDerivAt (EMLTree.eml A B).eval (D x) x)
    (hx0pos : 0 < B.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < B.eval x := by
  intro x hx1 hx2
  refine Classical.byContradiction (fun hcon => ?_)
  have hxle : B.eval x ≤ 0 := by
    rcases lt_total 0 (B.eval x) with h | h | h
    · exact absurd h hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hSne : ∃ y, (fun y => x0 ≤ y ∧ y < b ∧ B.eval y ≤ 0) y := ⟨x, hx1, hx2, hxle⟩
  have hSbd : BoundedBelow (fun y => x0 ≤ y ∧ y < b ∧ B.eval y ≤ 0) := ⟨x0, fun y hy => hy.1⟩
  obtain ⟨xs, hlb, hglb⟩ := inf_exists _ hSne hSbd
  have hx0xs : x0 ≤ xs := hglb x0 (fun y hy => hy.1)
  have hxsb : xs < b := lt_of_le_of_lt (hlb x ⟨hx1, hx2, hxle⟩) hx2
  have hposbelow : ∀ y, x0 ≤ y → y < xs → 0 < B.eval y := by
    intro y hy1 hy2
    refine Classical.byContradiction (fun hcony => ?_)
    have hyle : B.eval y ≤ 0 := by
      rcases lt_total 0 (B.eval y) with h | h | h
      · exact absurd h hcony
      · exact le_of_eq h.symm
      · exact le_of_lt h
    have hyb : y < b := lt_trans_ax hy2 hxsb
    exact lt_irrefl_ax xs (lt_of_le_of_lt (hlb y ⟨hy1, hyb, hyle⟩) hy2)
  have hxsle : B.eval xs ≤ 0 := by
    refine Classical.byContradiction (fun hxscon => ?_)
    have hxsgt : 0 < B.eval xs := by
      rcases lt_total (B.eval xs) 0 with h | h | h
      · exact absurd (le_of_lt h) hxscon
      · exact absurd (le_of_eq h) hxscon
      · exact h
    obtain ⟨δ, hδ, hnbhd⟩ :=
      pos_nbhd_of_continuousAt (hasDerivAt_continuousAt (hB'd xs hx0xs hxsb)) hxsgt
    have hbound2 : ∀ y, (x0 ≤ y ∧ y < b ∧ B.eval y ≤ 0) → xs + δ ≤ y := by
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
  let E1 : Real → Real := fun z => Real.exp (Real.exp (A.eval z) - (EMLTree.eml A B).eval z)
  have hE1pos : ∀ z, 0 < E1 z := fun z => Real.exp_pos _
  let k : Real := B.eval x0 * (1 / E1 x0)
  have hkE1x0 : k * E1 x0 = B.eval x0 := by
    show B.eval x0 * (1 / E1 x0) * E1 x0 = B.eval x0
    rw [mul_assoc, mul_comm (1 / E1 x0) (E1 x0), mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
        mul_one_ax]
  have hkpos : 0 < k := mul_pos hx0pos (one_div_pos_of_pos (hE1pos x0))
  have hBode : ∀ z, x0 ≤ z → z < xs →
      HasDerivAt B.eval (B.eval z * (Real.exp (A.eval z) * A' z - D z)) z := by
    intro z hz1 hz2
    have hzb : z < b := lt_trans_ax hz2 hxsb
    have heq := eml_ode_step_general (hDd z hz1 hzb) (hA'd z hz1 hzb) (hB'd z hz1 hzb)
      (hposbelow z hz1 hz2)
    have hderiv := hB'd z hz1 hzb
    rwa [heq] at hderiv
  have hE1ode : ∀ z, x0 ≤ z → z < xs →
      HasDerivAt E1 (E1 z * (Real.exp (A.eval z) * A' z - D z)) z := by
    intro z hz1 hz2
    have hzb : z < b := lt_trans_ax hz2 hxsb
    exact eml_E_step_general (hA'd z hz1 hzb) (hDd z hz1 hzb)
  have hzero : ∀ y, x0 ≤ y → y < xs → B.eval y - k * E1 y = 0 := by
    intro y hy1 hy2
    rcases (le_iff_lt_or_eq x0 y).mp hy1 with hlt | heq
    · obtain ⟨k', hk'⟩ := const_ratio_of_shared_ode B.eval E1
        (fun z => Real.exp (A.eval z) * A' z - D z) x0 y hlt
        (fun z hz1 hz2 => hBode z hz1 (lt_of_le_of_lt hz2 hy2))
        (fun z hz1 hz2 => hE1ode z hz1 (lt_of_le_of_lt hz2 hy2))
        (fun z _ _ => (ne_of_lt (hE1pos z)).symm)
      have hkx0 : B.eval x0 = k' * E1 x0 := hk' x0 (le_refl x0) (le_of_lt hlt)
      have hkeq : k' = k := by
        have h2 : k' * E1 x0 = k * E1 x0 := by rw [← hkx0, hkE1x0]
        have h3 : k' * E1 x0 * (1 / E1 x0) = k * E1 x0 * (1 / E1 x0) := by rw [h2]
        rwa [mul_assoc, mul_assoc, mul_inv (E1 x0) (ne_of_lt (hE1pos x0)).symm,
            mul_one_ax, mul_one_ax] at h3
      have hky : B.eval y = k' * E1 y := hk' y hy1 (le_refl y)
      rw [hky, hkeq, sub_def, add_neg]
    · rw [← heq, hkE1x0, sub_def, add_neg]
  have hxsE1pos : 0 < k * E1 xs := mul_pos hkpos (hE1pos xs)
  have hxseq2 : B.eval xs = k * E1 xs := by
    rcases (le_iff_lt_or_eq x0 xs).mp hx0xs with hx0xslt | hx0xseq
    · have hcontdiff : HasDerivAt (fun z => B.eval z - k * E1 z)
          (B' xs - (0 * E1 xs + k * (E1 xs * (Real.exp (A.eval xs) * A' xs - D xs)))) xs :=
        HasDerivAt_sub B.eval (fun z => k * E1 z) (B' xs)
          (0 * E1 xs + k * (E1 xs * (Real.exp (A.eval xs) * A' xs - D xs))) xs
          (hB'd xs hx0xs hxsb)
          (HasDerivAt_mul (fun _ => k) E1 0 (E1 xs * (Real.exp (A.eval xs) * A' xs - D xs)) xs
            (HasDerivAt_const k xs) (eml_E_step_general (hA'd xs hx0xs hxsb) (hDd xs hx0xs hxsb)))
      have hxseq : B.eval xs - k * E1 xs = 0 :=
        @eq_zero_at_of_eq_zero_below (fun z => B.eval z - k * E1 z) x0 xs hx0xslt
          (hasDerivAt_continuousAt hcontdiff) hzero
      have h2 : B.eval xs - k * E1 xs + k * E1 xs = 0 + k * E1 xs := by rw [hxseq]
      rwa [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at h2
    · rw [← hx0xseq, hkE1x0]
  have hfinal : k * E1 xs ≤ 0 := hxseq2 ▸ hxsle
  exact lt_irrefl_ax 0 (lt_of_lt_of_le hxsE1pos hfinal)

/-- Builds the left-descent spine ROOT-first: `leftSpine [c0,c1,...,cn] base = eml (eml (... (eml
base cn) ...) c1) c0` — the FIRST list element is the ROOT's own sibling, recursing INWARD toward
`base`. Deliberately the opposite traversal direction from `wrapLeft` (which builds bottom-up,
suited to the value-blow-up chain): peeling a node's value/derivative from its PARENT's needs to
proceed root-to-base, matching this recursion exactly. -/
def leftSpine : List EMLTree → EMLTree → EMLTree
  | [], base => base
  | c :: cs, base => EMLTree.eml (leftSpine cs base) c

/-- **The left-descent derivative, chained through an arbitrary-length spine.** Given
`leftSpine Cs base` agrees with a known target (with known derivative) and every sibling in `Cs`
has no crossing, `base` gets a known derivative too — by induction on `Cs`, applying
`eml_leftchild_hasDerivAt_general` once per level, each time feeding the PREVIOUS level's freshly
established derivative back in as the next level's `TARGET`/`hTarget`. -/
theorem leftSpine_hasDerivAt_of_target {base : EMLTree} (Cs : List EMLTree) {x : Real}
    {TARGET : Real → Real} {d : Real}
    (heq : ∀ z, (leftSpine Cs base).eval z = TARGET z)
    (hTarget : HasDerivAt TARGET d x)
    (hncCs : ∀ c ∈ Cs, EMLNoCrossingAt c x)
    (hCsne : ∀ c ∈ Cs, c.eval x ≠ 0) :
    ∃ D : Real, HasDerivAt base.eval D x := by
  induction Cs generalizing TARGET d with
  | nil => exact ⟨d, HasDerivAt_of_eq TARGET base.eval d x (fun z => (heq z).symm) hTarget⟩
  | cons c cs ih =>
    have hncc : EMLNoCrossingAt c x := hncCs c (List.Mem.head cs)
    have hncrest : ∀ c' ∈ cs, EMLNoCrossingAt c' x := fun c' hc' => hncCs c' (List.Mem.tail c hc')
    have hcne : c.eval x ≠ 0 := hCsne c (List.Mem.head cs)
    have hcnerest : ∀ c' ∈ cs, c'.eval x ≠ 0 := fun c' hc' => hCsne c' (List.Mem.tail c hc')
    obtain ⟨cc, hcc⟩ := eml_hasDerivAt_of_no_crossing c x hncc
    obtain ⟨D', hD'⟩ := eml_leftchild_hasDerivAt_general
      (A := leftSpine cs base) (B := c) heq hTarget hcc hcne
    exact ih (heq := fun _ => rfl) hD' hncrest hcnerest

/-- **The full left-spine closure.** If `t = leftSpine Cs (eml Slast Offender)` agrees with `sin`
on `[x0,b)`, every sibling in `Cs` has no crossing there, and `Offender` is positive at the witness
`x0`, `Offender` stays positive throughout `[x0,b)` — for a spine `Cs` of ANY length. Combines
`leftSpine_hasDerivAt_of_target` (chained root-to-base derivative propagation) with
`eml_ode_closure_general` (the minimal-violation-point closure, generic in the known derivative). -/
theorem eml_leftspine_pos_of_pos_witness {Slast Offender : EMLTree} (Cs : List EMLTree)
    (x0 b : Real) (hx0b : x0 < b)
    (hsin : ∀ x : Real, (leftSpine Cs (EMLTree.eml Slast Offender)).eval x = Real.sin x)
    (hncCs : ∀ c ∈ Cs, ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt c x)
    (hCsne : ∀ c ∈ Cs, ∀ x, x0 ≤ x → x < b → c.eval x ≠ 0)
    (Slast' : Real → Real) (hSlast'd : ∀ x, x0 ≤ x → x < b → HasDerivAt Slast.eval (Slast' x) x)
    (Offender' : Real → Real)
    (hOffender'd : ∀ x, x0 ≤ x → x < b → HasDerivAt Offender.eval (Offender' x) x)
    (hx0pos : 0 < Offender.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < Offender.eval x := by
  have hDd : ∀ x, x0 ≤ x → x < b →
      ∃ D : Real, HasDerivAt (EMLTree.eml Slast Offender).eval D x := by
    intro x hx1 hx2
    exact leftSpine_hasDerivAt_of_target Cs (heq := hsin) (HasDerivAt_sin x)
      (fun c hc => hncCs c hc x hx1 hx2) (fun c hc => hCsne c hc x hx1 hx2)
  let Dfun : Real → Real := fun z => if h : x0 ≤ z ∧ z < b then (hDd z h.1 h.2).choose else 0
  have hDfund : ∀ z, x0 ≤ z → z < b → HasDerivAt (EMLTree.eml Slast Offender).eval (Dfun z) z := by
    intro z hz1 hz2
    show HasDerivAt (EMLTree.eml Slast Offender).eval
      (if h : x0 ≤ z ∧ z < b then (hDd z h.1 h.2).choose else 0) z
    rw [dif_pos ⟨hz1, hz2⟩]
    exact (hDd z hz1 hz2).choose_spec
  exact eml_ode_closure_general x0 b hx0b Slast' hSlast'd Offender' hOffender'd Dfun hDfund hx0pos

/-! ## Correcting scope, and a genuinely different direction: chaining RIGHT steps

`eml_leftspine_pos_of_pos_witness`'s tree shape (`leftSpine Cs (eml Slast Offender)`) turns out to
be the SAME FAMILY `eml_leftchain_pos_of_no_crossing` (round 12, `wrapLeft`) already closed —
`wrapLeft` also always wraps its accumulator as the new node's LEFT child, so `wrapLeft Cs base` and
`leftSpine Cs base` range over the same shapes with `Cs` reversed. Round 12's hypotheses are
actually a strict subset of this section's (no explicit derivative functions needed there, just
`EMLNoCrossingAt`). So this section's arbitrary-depth left-spine result is independent
CONFIRMATION via a different technique, not new coverage — worth having, but not what it was
reported as.

The genuinely open direction: does the ODE/constant-ratio mechanism reach past what the
value-blow-up mechanism PROVABLY cannot (round 5's state-machine argument: state `B` always dies
one step after the first right-turn, ruling out more than one non-terminal right turn)? Once
`eml_ode_closure_general` establishes `B`'s positivity throughout `[x0,b)` (not just up to a
hypothetical failure point), `B` ALSO gets its OWN known, independent derivative for free —
`eml_ode_step_general` applied with the NOW-GLOBAL positivity — with NO circularity, since this
derivative is expressed purely via `A`, `A'`, `D`, and `B`'s own VALUE (never `B`'s internal
derivative structure). That known derivative is exactly the right shape to feed BACK into
`eml_ode_closure_general` for a node one level inside `B` — chaining through a SECOND right step,
something the blow-up mechanism cannot do at all. -/

/-- **Positivity + a free derivative, bundled.** `eml_ode_closure_general`'s conclusion, plus the
one additional fact that makes chaining possible: once `B`'s positivity holds throughout
`[x0,b)` (not just below a hypothetical failure point), `eml_ode_step_general` applies GLOBALLY,
giving `B` its own known, structure-independent derivative — usable as the next level's `D`. -/
theorem eml_ode_closure_general_hasDerivAt {A B : EMLTree}
    (x0 b : Real) (hx0b : x0 < b)
    (A' : Real → Real) (hA'd : ∀ x, x0 ≤ x → x < b → HasDerivAt A.eval (A' x) x)
    (B' : Real → Real) (hB'd : ∀ x, x0 ≤ x → x < b → HasDerivAt B.eval (B' x) x)
    (D : Real → Real) (hDd : ∀ x, x0 ≤ x → x < b → HasDerivAt (EMLTree.eml A B).eval (D x) x)
    (hx0pos : 0 < B.eval x0) :
    ∀ x, x0 ≤ x → x < b →
      0 < B.eval x ∧
        HasDerivAt B.eval (B.eval x * (Real.exp (A.eval x) * A' x - D x)) x := by
  have hpos := eml_ode_closure_general x0 b hx0b A' hA'd B' hB'd D hDd hx0pos
  refine fun x hx1 hx2 => ⟨hpos x hx1 hx2, ?_⟩
  have heq := eml_ode_step_general (hDd x hx1 hx2) (hA'd x hx1 hx2) (hB'd x hx1 hx2)
    (hpos x hx1 hx2)
  have hderiv := hB'd x hx1 hx2
  rwa [heq] at hderiv

/-- **A genuine "right-right-right" instance.** Round 5 proved the value-blow-up mechanism
CANNOT reach this shape (three log-slots below the root, the third turn not landing on the root) —
"the longest chain it can certify" was exactly two. This closes it anyway via the ODE mechanism,
chaining `eml_ode_closure_general_hasDerivAt` twice: level 0 uses the free root derivative
(`cos x`) to close `N1 := eml S2 (eml S4 S5)` AND expose N1's own free derivative; level 1 uses
THAT to close `N2 := eml S4 S5` and expose N2's derivative; level 2 uses THAT to close the actual
offender `S5`. Each level needs its own positivity witness at `x0` (the witness problem — round
9.5/10 — is not solved here, just required as a hypothesis at every level, same as everywhere
else this session). -/
theorem eml_rrr_pos_of_pos_witness {T1 S2 S4 S5 : EMLTree}
    (hsin : ∀ x : Real, (EMLTree.eml T1 (EMLTree.eml S2 (EMLTree.eml S4 S5))).eval x = Real.sin x)
    (x0 b : Real) (hx0b : x0 < b)
    (T1' : Real → Real) (hT1'd : ∀ x, x0 ≤ x → x < b → HasDerivAt T1.eval (T1' x) x)
    (N1' : Real → Real)
    (hN1'd : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml S2 (EMLTree.eml S4 S5)).eval (N1' x) x)
    (S2' : Real → Real) (hS2'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S2.eval (S2' x) x)
    (N2' : Real → Real)
    (hN2'd : ∀ x, x0 ≤ x → x < b → HasDerivAt (EMLTree.eml S4 S5).eval (N2' x) x)
    (S4' : Real → Real) (hS4'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S4.eval (S4' x) x)
    (S5' : Real → Real) (hS5'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S5.eval (S5' x) x)
    (hN1x0pos : 0 < (EMLTree.eml S2 (EMLTree.eml S4 S5)).eval x0)
    (hN2x0pos : 0 < (EMLTree.eml S4 S5).eval x0)
    (hS5x0pos : 0 < S5.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < S5.eval x := by
  have hD0d : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml T1 (EMLTree.eml S2 (EMLTree.eml S4 S5))).eval (Real.cos x) x :=
    fun x _ _ => eml_hasDerivAt_of_sin_eq _ hsin x
  have hN1 := eml_ode_closure_general_hasDerivAt x0 b hx0b T1' hT1'd N1' hN1'd
    Real.cos hD0d hN1x0pos
  let D1 : Real → Real := fun x => (EMLTree.eml S2 (EMLTree.eml S4 S5)).eval x *
    (Real.exp (T1.eval x) * T1' x - Real.cos x)
  have hD1d : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml S2 (EMLTree.eml S4 S5)).eval (D1 x) x :=
    fun x hx1 hx2 => (hN1 x hx1 hx2).2
  have hN2 := eml_ode_closure_general_hasDerivAt x0 b hx0b S2' hS2'd N2' hN2'd D1 hD1d hN2x0pos
  let D2 : Real → Real := fun x => (EMLTree.eml S4 S5).eval x *
    (Real.exp (S2.eval x) * S2' x - D1 x)
  have hD2d : ∀ x, x0 ≤ x → x < b → HasDerivAt (EMLTree.eml S4 S5).eval (D2 x) x :=
    fun x hx1 hx2 => (hN2 x hx1 hx2).2
  exact eml_ode_closure_general x0 b hx0b S4' hS4'd S5' hS5'd D2 hD2d hS5x0pos

/-! ## Generalizing right-descent chaining to arbitrary depth

`eml_rrr_pos_of_pos_witness` demonstrated the mechanism chains through TWO forced right turns
(three total, counting the mandatory one at the offender itself). This section generalizes to a
chain of ANY length, mirroring how `leftSpine`/`leftSpine_hasDerivAt_of_target` generalized
left-descent (rounds 15→16) — same shape of induction, but each step here genuinely needs its OWN
positivity witness (unlike left-descent, where `eml_leftchild_explicit_value` is unconditional). -/

/-- Builds a pure right-descent chain: `rightChain [A1,...,An] base = eml A1 (eml A2 (... (eml An
base) ...))` — `A1` is the OUTERMOST (root-adjacent) sibling, matching `eml_rrr_pos_of_pos_witness`'s
`T1`. -/
def rightChain : List EMLTree → EMLTree → EMLTree
  | [], base => base
  | A :: As, base => EMLTree.eml A (rightChain As base)

/-- The positivity witnesses this mechanism genuinely needs, one per intermediate accumulator node
(every proper tail of `As`, applied to `base`) — NOT needed for the outermost node itself (that
witness is supplied separately, at the call site, since it's about `rightChain As base` as a
whole, already given via `hDd`'s domain). -/
def rightChainWitnesses : List EMLTree → EMLTree → Real → Prop
  | [], _, _ => True
  | _ :: As, base, x0 => 0 < (rightChain As base).eval x0 ∧ rightChainWitnesses As base x0

/-- **The right-descent derivative, chained through an arbitrary-length pure-right chain.** Given
`rightChain As base` has a known derivative and a witness at every intermediate level, `base`
(whatever sits at the bottom) ALSO gets a known derivative — by induction on `As`, peeling one
sibling off at a time via `eml_ode_closure_general_hasDerivAt`, each step needing its own witness
(the genuine difference from left-descent) plus a STRUCTURAL derivative for the new tail (via
`EMLNoCrossingAt`, just for internal continuity bookkeeping — not the "smart" ODE-derived one). -/
theorem rightChain_hasDerivAt_of_target {base : EMLTree} (As : List EMLTree)
    (x0 b : Real) (hx0b : x0 < b)
    (D : Real → Real)
    (hDd : ∀ x, x0 ≤ x → x < b → HasDerivAt (rightChain As base).eval (D x) x)
    (Aderiv : EMLTree → Real → Real)
    (hAderivd : ∀ A ∈ As, ∀ x, x0 ≤ x → x < b → HasDerivAt A.eval (Aderiv A x) x)
    (hncFull : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt (rightChain As base) x)
    (hwit : rightChainWitnesses As base x0) :
    ∃ D' : Real → Real, ∀ x, x0 ≤ x → x < b → HasDerivAt base.eval (D' x) x := by
  induction As generalizing D with
  | nil => exact ⟨D, hDd⟩
  | cons A As' ih =>
    have hA : ∀ x, x0 ≤ x → x < b → HasDerivAt A.eval (Aderiv A x) x :=
      fun x hx1 hx2 => hAderivd A (List.Mem.head As') x hx1 hx2
    have hAsrest : ∀ A' ∈ As', ∀ x, x0 ≤ x → x < b → HasDerivAt A'.eval (Aderiv A' x) x :=
      fun A' hA' x hx1 hx2 => hAderivd A' (List.Mem.tail A hA') x hx1 hx2
    have hncTail : ∀ x, x0 ≤ x → x < b → EMLNoCrossingAt (rightChain As' base) x :=
      fun x hx1 hx2 => (hncFull x hx1 hx2).2.1
    have hwitTail : 0 < (rightChain As' base).eval x0 := hwit.1
    have hwitRest : rightChainWitnesses As' base x0 := hwit.2
    let TailDeriv : Real → Real := fun z =>
      if h : x0 ≤ z ∧ z < b then
        (eml_hasDerivAt_of_no_crossing (rightChain As' base) z (hncTail z h.1 h.2)).choose
      else 0
    have hTailDerivd : ∀ z, x0 ≤ z → z < b →
        HasDerivAt (rightChain As' base).eval (TailDeriv z) z := by
      intro z hz1 hz2
      show HasDerivAt (rightChain As' base).eval
        (if h : x0 ≤ z ∧ z < b then
          (eml_hasDerivAt_of_no_crossing (rightChain As' base) z (hncTail z h.1 h.2)).choose
        else 0) z
      rw [dif_pos ⟨hz1, hz2⟩]
      exact (eml_hasDerivAt_of_no_crossing (rightChain As' base) z (hncTail z hz1 hz2)).choose_spec
    have hNext := eml_ode_closure_general_hasDerivAt x0 b hx0b (Aderiv A) hA TailDeriv hTailDerivd
      D hDd hwitTail
    let D' : Real → Real := fun x =>
      (rightChain As' base).eval x * (Real.exp (A.eval x) * Aderiv A x - D x)
    have hD'd : ∀ x, x0 ≤ x → x < b → HasDerivAt (rightChain As' base).eval (D' x) x :=
      fun x hx1 hx2 => (hNext x hx1 hx2).2
    exact ih D' hD'd hAsrest hncTail hwitRest

/-- **The full right-chain closure.** If `t = rightChain As (eml Slast Offender)` agrees with
`sin` on `[x0,b)`, every sibling in `As` has no crossing there (bundled with the tail's `≠0`
conditions via `EMLNoCrossingAt` on the whole chain), a witness exists at EVERY intermediate
accumulator node PLUS `Offender` itself, `Offender` stays positive throughout `[x0,b)` — for a pure
right-descent chain of ANY length, strictly beyond what the value-blow-up mechanism can ever reach
(round 5's proven ceiling). -/
theorem eml_rightchain_pos_of_pos_witness {Slast Offender : EMLTree} (As : List EMLTree)
    (x0 b : Real) (hx0b : x0 < b)
    (hsin : ∀ x : Real, (rightChain As (EMLTree.eml Slast Offender)).eval x = Real.sin x)
    (Aderiv : EMLTree → Real → Real)
    (hAderivd : ∀ A ∈ As, ∀ x, x0 ≤ x → x < b → HasDerivAt A.eval (Aderiv A x) x)
    (hncFull : ∀ x, x0 ≤ x → x < b →
      EMLNoCrossingAt (rightChain As (EMLTree.eml Slast Offender)) x)
    (hwit : rightChainWitnesses As (EMLTree.eml Slast Offender) x0)
    (Slast' : Real → Real) (hSlast'd : ∀ x, x0 ≤ x → x < b → HasDerivAt Slast.eval (Slast' x) x)
    (Offender' : Real → Real)
    (hOffender'd : ∀ x, x0 ≤ x → x < b → HasDerivAt Offender.eval (Offender' x) x)
    (hx0pos : 0 < Offender.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < Offender.eval x := by
  have hD0d : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (rightChain As (EMLTree.eml Slast Offender)).eval (Real.cos x) x :=
    fun x _ _ => eml_hasDerivAt_of_sin_eq _ hsin x
  obtain ⟨D, hDd⟩ := rightChain_hasDerivAt_of_target As x0 b hx0b Real.cos hD0d
    Aderiv hAderivd hncFull hwit
  exact eml_ode_closure_general x0 b hx0b Slast' hSlast'd Offender' hOffender'd D hDd hx0pos

/-! ## Toward the fully general witness question: a free witness at depth 2

Round 19's negative finding (no uniform invariant survives an arbitrary sibling) does NOT rule out
a DIRECT, elementary argument for CONCRETE sibling shapes. If the offender `S3` were identically
`≤ 0` everywhere, its log-branch collapses to the constant `0` (`Real.log_nonpos`), forcing
`(eml S2 S3).eval x = exp(S2.eval x)` for ALL `x` — and then, via `log∘exp = id` UNCONDITIONALLY
(no positivity needed, the same asymmetry `eml_leftchild_explicit_value` exploits), the WHOLE tree
collapses to `exp(T1.eval x) − S2.eval x = sin x`. If `T1` is (globally) constant and `S2` is a
leaf (constant or the identity), this is refutable by evaluating at one or two concrete points —
giving a FREE witness for `S3`, no hypothesis needed, for this whole class of siblings. This does
NOT resolve the general case (compound `T1`/`S2` reopen exactly the recursive difficulty found in
round 19) but it is a genuine, unconditional result for a natural, common shape. -/

/-- **A free witness at depth 2, for constant `T1` and leaf `S2`.** If `t = eml T1 (eml S2 S3)`
agrees with `sin` globally, `T1` is (globally) constant, and `S2` is either constant or the
identity, then `S3` (the depth-2 offender) is positive SOMEWHERE — no witness hypothesis needed.
Proved by contradiction: assuming `S3 ≤ 0` everywhere collapses the tree to
`exp(c) − S2.eval x = sin x`, refuted by direct evaluation (`x = 0` and `x = π/2` for constant
`S2`, using `sin_pi_div_two`; `x = 0` alone for identity `S2`, using `exp_pos`). -/
theorem eml_depth2_witness_of_const_var {T1 S2 S3 : EMLTree} {c : Real}
    (hT1 : ∀ x, T1.eval x = c)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml S2 S3)).eval x = Real.sin x)
    (hS2 : (∃ c2, ∀ x, S2.eval x = c2) ∨ (∀ x, S2.eval x = x)) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hlog0 : ∀ x, Real.log (S3.eval x) = 0 := fun x => Real.log_nonpos (hallle x)
  have hNeval : ∀ x, (EMLTree.eml S2 S3).eval x = Real.exp (S2.eval x) := by
    intro x
    show Real.exp (S2.eval x) - Real.log (S3.eval x) = Real.exp (S2.eval x)
    rw [hlog0 x, sub_zero]
  have hcollapse : ∀ x, Real.exp c - S2.eval x = Real.sin x := by
    intro x
    have h1 : Real.exp (T1.eval x) - Real.log ((EMLTree.eml S2 S3).eval x) = Real.sin x := hsin x
    rw [hT1 x, hNeval x, Real.log_exp] at h1
    exact h1
  rcases hS2 with ⟨c2, hS2const⟩ | hS2var
  · have heq0 := hcollapse 0
    have heqhalf := hcollapse (Real.pi / (1 + 1))
    rw [hS2const 0, Real.sin_zero] at heq0
    rw [hS2const (Real.pi / (1 + 1)), Real.sin_pi_div_two] at heqhalf
    rw [heq0] at heqhalf
    have h01 : (0 : Real) < 1 := zero_lt_one_ax
    rw [heqhalf] at h01
    exact lt_irrefl_ax 1 h01
  · have heq0 := hcollapse 0
    rw [hS2var 0, Real.sin_zero] at heq0
    have hexp0 : Real.exp c = 0 := by rw [← heq0]; mach_ring
    exact absurd hexp0 (ne_of_lt (Real.exp_pos c)).symm

/-! ## Dropping the `T1`-constant restriction: it was only load-bearing for one sub-case

Re-examining `eml_depth2_witness_of_const_var`'s two branches: the "`S2` constant" branch
genuinely NEEDS `T1` constant (comparing `exp(T1.eval x) - c2` at two different points only forces
a contradiction if `exp(T1.eval x)` is the SAME number both times). The "`S2 = var`" branch does
NOT — evaluating the collapse equation at `x = 0` alone gives `exp(T1.eval 0) - var.eval 0 = sin 0`,
i.e. `exp(T1.eval 0) = 0` (since `var.eval 0 = 0` and `sin 0 = 0`), which is impossible for ANY
`T1` whatsoever, by `exp`'s bare positivity. The constant-`T1` hypothesis was carrying no weight at
all in that branch — dropped below. -/

/-- **A free witness at depth 2, for `S2 = var`, with `T1` COMPLETELY ARBITRARY.** Strengthens the
`S2 = var` half of `eml_depth2_witness_of_const_var`: no hypothesis on `T1` at all. Evaluating the
collapse equation at `x = 0` alone (`var.eval 0 = 0`, `sin 0 = 0`) forces `exp(T1.eval 0) = 0`,
impossible regardless of `T1`'s shape. -/
theorem eml_depth2_witness_of_var_sibling {T1 S3 : EMLTree}
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml EMLTree.var S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hlog0 : Real.log (S3.eval 0) = 0 := Real.log_nonpos (hallle 0)
  have h1 : Real.exp (T1.eval 0) - Real.log ((EMLTree.eml EMLTree.var S3).eval 0) = Real.sin 0 :=
    hsin 0
  have hNeval0 : (EMLTree.eml EMLTree.var S3).eval 0 = Real.exp (0 : Real) := by
    show Real.exp (0 : Real) - Real.log (S3.eval 0) = Real.exp (0 : Real)
    rw [hlog0, sub_zero]
  rw [hNeval0, Real.log_exp, Real.sin_zero, sub_zero] at h1
  exact absurd h1 (ne_of_lt (Real.exp_pos (T1.eval 0))).symm

/-- **A free witness at depth 2, for `S2` constant `≤ 1`, `T1` COMPLETELY ARBITRARY.** The other
half of `eml_depth2_witness_of_const_var`'s `S2`-constant branch also drops the `T1`-constant
restriction — but only within this narrower range: evaluating the collapse equation at
`x = -π/2` (`sin(-π/2) = -1`, via `sin_neg` + `sin_pi_div_two`) forces
`exp(T1.eval(-π/2)) = c2 - 1 ≤ 0` whenever `c2 ≤ 1`, impossible regardless of `T1`. For `c2 > 1`
this specific point gives no contradiction — matching round 19's finding that unconstrained
siblings can defeat single-point arguments; `eml_depth2_witness_of_const_var` still needs `T1`
constant to cover that range, via its two-point comparison. -/
theorem eml_depth2_witness_of_const_le_one_sibling {T1 S3 : EMLTree} {c2 : Real} (hc2 : c2 ≤ 1)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  let x0 : Real := -(Real.pi / (1 + 1))
  have hsinx0 : Real.sin x0 = -1 := by
    show Real.sin (-(Real.pi / (1 + 1))) = -1
    rw [Real.sin_neg, Real.sin_pi_div_two]
  have hlog0 : Real.log (S3.eval x0) = 0 := Real.log_nonpos (hallle x0)
  have h1 : Real.exp (T1.eval x0) -
      Real.log ((EMLTree.eml (EMLTree.const c2) S3).eval x0) = Real.sin x0 := hsin x0
  have hNeval : (EMLTree.eml (EMLTree.const c2) S3).eval x0 = Real.exp c2 := by
    show Real.exp c2 - Real.log (S3.eval x0) = Real.exp c2
    rw [hlog0, sub_zero]
  rw [hNeval, Real.log_exp, hsinx0] at h1
  have h2 : Real.exp (T1.eval x0) - c2 + c2 = -1 + c2 := by rw [h1]
  rw [sub_def, add_assoc, neg_add_self, add_zero,
      show (-1 : Real) + c2 = c2 - 1 from by mach_ring] at h2
  have hc2m1le : c2 - 1 ≤ 0 := by
    have h3 := add_le_add_left hc2 (-1)
    rwa [show (-1 : Real) + c2 = c2 - 1 from by mach_ring,
        show (-1 : Real) + 1 = 0 from by mach_ring] at h3
  have hcontra : Real.exp (T1.eval x0) ≤ 0 := h2 ▸ hc2m1le
  exact lt_irrefl_ax 0 (lt_of_lt_of_le (Real.exp_pos _) hcontra)

/-! ## Option C (counterexample search) redirected: the real dichotomy is bounded vs. unbounded `T1`

Trying to construct an explicit counterexample tree — a candidate compound `T1` making the
"`c2 > 1`" gap genuine — kept failing for a specific reason: natural compound `T1` choices are
either secretly constant (e.g. `eml (const a) (const b)` collapses to a fixed number) or
UNBOUNDED (e.g. `eml var (const 1) = exp(x)`, unbounded above). The unbounded case turns out to
give an IMMEDIATE elementary contradiction, with no dependence on `T1`'s syntactic shape at all —
this is the real line dividing "closes for free" from "needs `T1` constant", not "leaf vs.
compound" as the earlier framing suggested. -/

/-- **A free witness for `S2` constant, ANY `c2`, whenever `T1` is unbounded above.** Covers the
ENTIRE `c2 > 1` gap left by `eml_depth2_witness_of_const_le_one_sibling`, for any `T1` — compound
or not — that takes arbitrarily large values somewhere. If `S3` collapsed to `≤ 0` everywhere,
`exp(T1.eval x) = sin x + c2 ≤ c2 + 1` for ALL `x` (via `sin_le_one`) — but picking `x` with
`T1.eval x > c2 + 2` (from unboundedness) forces `exp(T1.eval x) > T1.eval x > c2 + 2` (via
`exp_grows_strictly_thm`), directly contradicting the upper bound. No Khovanskii/zero-counting
machinery needed — this is exactly the kind of elementary growth argument a counterexample search
was hoping to defeat, and it holds unconditionally. -/
theorem eml_depth2_witness_of_const_sibling_unbounded_T1 {T1 S3 : EMLTree} {c2 : Real}
    (hT1unbdd : ∀ M : Real, ∃ x, M < T1.eval x)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hcollapse : ∀ x, Real.exp (T1.eval x) - c2 = Real.sin x := by
    intro x
    have hlog0 : Real.log (S3.eval x) = 0 := Real.log_nonpos (hallle x)
    have hNeval : (EMLTree.eml (EMLTree.const c2) S3).eval x = Real.exp c2 := by
      show Real.exp c2 - Real.log (S3.eval x) = Real.exp c2
      rw [hlog0, sub_zero]
    have h1 : Real.exp (T1.eval x) -
        Real.log ((EMLTree.eml (EMLTree.const c2) S3).eval x) = Real.sin x := hsin x
    rwa [hNeval, Real.log_exp] at h1
  obtain ⟨x, hx⟩ := hT1unbdd (c2 + (1 + 1))
  have hexp_gt : T1.eval x < Real.exp (T1.eval x) := exp_grows_strictly_thm _
  have hbig : c2 + (1 + 1) < Real.exp (T1.eval x) := lt_trans_ax hx hexp_gt
  have hsmall : Real.exp (T1.eval x) ≤ c2 + 1 := by
    have h2 : Real.exp (T1.eval x) - c2 ≤ 1 := by rw [hcollapse x]; exact sin_le_one x
    have h3 := add_le_add_left h2 c2
    rwa [show c2 + (Real.exp (T1.eval x) - c2) = Real.exp (T1.eval x) from by mach_ring] at h3
  have h3 : c2 + (1 + 1) < c2 + 1 := lt_of_lt_of_le hbig hsmall
  have h4 := add_lt_add_left h3 (-c2)
  rw [show -c2 + (c2 + (1 + 1)) = 1 + 1 from by mach_ring,
      show -c2 + (c2 + 1) = 1 from by mach_ring] at h4
  have h5 : (1 : Real) < 1 + 1 := by
    have h6 := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h6
  exact lt_irrefl_ax (1 + 1) (lt_trans_ax h4 h5)

/-! ## Mixing the two mechanisms: a genuine "right-left-right" instance

Both descent mechanisms (left-spine, rounds 15–16; right-chain, rounds 17–18) are now individually
general to arbitrary depth. Neither, on its own, covers a tree whose root-to-offender path
GENUINELY alternates directions more than once (the value-blow-up mechanism's own reach, rounds
12–13, tops out at "R L* R?" via a totally different technique). This section checks the ODE
mechanism composes across a mixed path by building one concrete instance: `R` (root), then `L`
(one level in), then the mandatory final `R` to the offender — reusing
`eml_ode_closure_general_hasDerivAt` for both `R` steps and `eml_leftchild_hasDerivAt_general` for
the `L` step in between, with NO new lemma needed. -/

/-- **A genuine "R L R" instance.** `t = eml A1 (eml (eml S4 Offender) C2)`: root's log-child is
`N1 := eml (eml S4 Offender) C2` (an `R` step), `N1`'s left/exp child is `eml S4 Offender` (an `L`
step from `N1`), and `Offender` is that node's own log-child (the mandatory final `R`). Chains:
root's free `cos x` derivative closes `N1` (via `eml_ode_closure_general_hasDerivAt`, witness
`hN1x0pos`) and exposes `N1`'s own derivative; that derivative transfers UNCONDITIONALLY to
`eml S4 Offender` (via `eml_leftchild_hasDerivAt_general`, no witness — the `L`-step asymmetry);
that closes `Offender` (via `eml_ode_closure_general`, witness `hOffenderx0pos`). -/
theorem eml_rlr_pos_of_pos_witness {A1 C2 S4 Offender : EMLTree}
    (hsin : ∀ x, (EMLTree.eml A1 (EMLTree.eml (EMLTree.eml S4 Offender) C2)).eval x = Real.sin x)
    (x0 b : Real) (hx0b : x0 < b)
    (A1' : Real → Real) (hA1'd : ∀ x, x0 ≤ x → x < b → HasDerivAt A1.eval (A1' x) x)
    (N1' : Real → Real)
    (hN1'd : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml (EMLTree.eml S4 Offender) C2).eval (N1' x) x)
    (C2' : Real → Real) (hC2'd : ∀ x, x0 ≤ x → x < b → HasDerivAt C2.eval (C2' x) x)
    (hC2ne : ∀ x, x0 ≤ x → x < b → C2.eval x ≠ 0)
    (S4' : Real → Real) (hS4'd : ∀ x, x0 ≤ x → x < b → HasDerivAt S4.eval (S4' x) x)
    (Offender' : Real → Real)
    (hOffender'd : ∀ x, x0 ≤ x → x < b → HasDerivAt Offender.eval (Offender' x) x)
    (hN1x0pos : 0 < (EMLTree.eml (EMLTree.eml S4 Offender) C2).eval x0)
    (hOffenderx0pos : 0 < Offender.eval x0) :
    ∀ x, x0 ≤ x → x < b → 0 < Offender.eval x := by
  have hD0d : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml A1 (EMLTree.eml (EMLTree.eml S4 Offender) C2)).eval (Real.cos x) x :=
    fun x _ _ => eml_hasDerivAt_of_sin_eq _ hsin x
  have hN1 := eml_ode_closure_general_hasDerivAt x0 b hx0b A1' hA1'd N1' hN1'd
    Real.cos hD0d hN1x0pos
  let D1 : Real → Real := fun x =>
    (EMLTree.eml (EMLTree.eml S4 Offender) C2).eval x *
      (Real.exp (A1.eval x) * A1' x - Real.cos x)
  have hD1d : ∀ x, x0 ≤ x → x < b →
      HasDerivAt (EMLTree.eml (EMLTree.eml S4 Offender) C2).eval (D1 x) x :=
    fun x hx1 hx2 => (hN1 x hx1 hx2).2
  have hD2ex : ∀ x, x0 ≤ x → x < b →
      ∃ D2 : Real, HasDerivAt (EMLTree.eml S4 Offender).eval D2 x := by
    intro x hx1 hx2
    exact eml_leftchild_hasDerivAt_general
      (A := EMLTree.eml S4 Offender) (B := C2)
      (TARGET := (EMLTree.eml (EMLTree.eml S4 Offender) C2).eval)
      (heq := fun _ => rfl)
      (hD1d x hx1 hx2) (hC2'd x hx1 hx2) (hC2ne x hx1 hx2)
  let D2 : Real → Real := fun x =>
    if h : x0 ≤ x ∧ x < b then (hD2ex x h.1 h.2).choose else 0
  have hD2d : ∀ x, x0 ≤ x → x < b → HasDerivAt (EMLTree.eml S4 Offender).eval (D2 x) x := by
    intro x hx1 hx2
    show HasDerivAt (EMLTree.eml S4 Offender).eval
      (if h : x0 ≤ x ∧ x < b then (hD2ex x h.1 h.2).choose else 0) x
    rw [dif_pos ⟨hx1, hx2⟩]
    exact (hD2ex x hx1 hx2).choose_spec
  exact eml_ode_closure_general x0 b hx0b S4' hS4'd Offender' hOffender'd D2 hD2d hOffenderx0pos

end MachLib
