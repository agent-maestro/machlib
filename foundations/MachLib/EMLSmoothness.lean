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

end MachLib
