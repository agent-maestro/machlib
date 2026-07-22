import MachLib.TailApproximationBarrier
import MachLib.EMLExplicitBoundSinBarrier

/-!
# The compact-interval quantitative non-approximation theorem

Track C's real remaining blocker for the "Certcom handshake" (C7), per two rounds of external
review (cont. 76/78): no depth-`d` EML tree is `ε`-close to `sin` on any interval longer than an
EXPLICIT `L`, `L` computed from the tree's own structure — as opposed to C6/C7's TAIL-only result,
which says nothing about bounded intervals no matter how long.

**Feasibility, checked before building anything (matching this whole document's discipline).** The
needed ingredient — an EXPLICIT (not merely existential) Khovanskii-style zero-count bound as a
function of tree structure — already exists: `EMLExplicitBound.enc_combinedBound`/`combinedBoundE`
(`EMLExplicitBoundEncoder.lean`), used by `EMLExplicitBoundSinBarrier.lean`'s own
`sin_not_in_eml_any_depth` for the EXACT-equality case. Confirmed via a direct `#print axioms`
check: `enc_combinedBound` and the `combined_descent_3_explicit` it rests on are BOTH `sorryAx`-free
and do NOT depend on `zero_count_bound_classical` or the still-open `exp_hard` gap (a separate,
much heavier arc — `project_log_hard_fixedD_pivot`/`project_log_g0_analytic_discharge` in agent
memory) — the "_explicit" route sidesteps that entirely by taking structural chain data explicitly
rather than existentially. This is genuinely reusable, trustworthy machinery, not a dead end.

**The construction, worked out on paper first.** `sin`'s zeros at `π, 2π, ..., (M+1)π` are what the
EXACT-equality proof counts directly. For the `ε`-APPROXIMATE case, the tree doesn't need an EXACT
zero at each `jπ` — but if `T.eval` stays within `ε < 1` of `sin` throughout an interval containing
these zeros, `T.eval` is forced to have an INDUCED zero near each one, via a sign argument: at the
alternating extrema `π/2 + jπ` (where `sin` is exactly `±1`, alternating sign — proved below by a
one-line "successor flips sign" induction, `sin(x+π) = -sin(x)`), `ε`-closeness forces `T.eval` to
share `sin`'s sign there too (since `|sin| = 1 > ε`). Consecutive extrema straddle exactly one
`sin`-zero and have OPPOSITE forced signs, so IVT gives `T.eval` a zero strictly between them —
`M + 1` such zeros, one per pair of consecutive extrema, automatically DISTINCT since the intervals
housing them are pairwise disjoint. `enc_combinedBound` bounds `T.eval`'s own zero count by `M` —
contradiction once `M + 1 > M`.
-/

namespace MachLib
namespace Real

open MachLib
open MachLib.EMLExplicitBound

private theorem lt_add_of_sub_lt {a b c : Real} (h : a - b < c) : a < b + c := by
  have h2 := add_lt_add_left h b
  have e1 : b + (a - b) = a := by mach_ring
  rwa [e1] at h2

private theorem lt_of_add_lt_neg {a ε : Real} (h : a < -ε) : a + ε < 0 := by
  have h2 := add_lt_add_left h ε
  have e1 : ε + -ε = (0:Real) := by mach_ring
  rw [e1] at h2
  rwa [add_comm ε a] at h2

/-- **Piece A — the general IVT-induced-zero lemma.** If `g` is continuous throughout `(a,b)` and
stays within `ε` of `TARGET` there, and `TARGET` is sign-forced (magnitude `> ε`) with OPPOSITE
signs at two interior points `x1 < x2`, then `g` has a zero strictly between them. Target- and
tree-agnostic — nothing here mentions `EMLTree`, matching this session's own compression style. -/
theorem induced_zero_of_eps_close (g : Real → Real) (a b : Real)
    (hcont : ∀ z : Real, a < z → z < b → ContinuousAt g z)
    (TARGET : Real → Real) (ε : Real)
    (hclose : ∀ x : Real, a < x → x < b → abs (g x - TARGET x) < ε)
    (x1 x2 : Real) (hax1 : a < x1) (hx1x2 : x1 < x2) (hx2b : x2 < b)
    (hT1 : TARGET x1 < -ε) (hT2 : ε < TARGET x2) :
    ∃ c : Real, x1 < c ∧ c < x2 ∧ g c = 0 := by
  have hax2 : a < x2 := lt_trans_ax hax1 hx1x2
  have hg1 : g x1 < 0 := by
    have h1 : g x1 - TARGET x1 < ε := lt_of_abs_lt (hclose x1 hax1 (lt_trans_ax hx1x2 hx2b))
    have h2 : g x1 < TARGET x1 + ε := lt_add_of_sub_lt h1
    exact lt_trans_ax h2 (lt_of_add_lt_neg hT1)
  have hg2 : 0 < g x2 := by
    have habs2 : abs (TARGET x2 - g x2) < ε := by
      rw [show TARGET x2 - g x2 = -(g x2 - TARGET x2) from by mach_ring, abs_neg]
      exact hclose x2 hax2 hx2b
    have h1 : TARGET x2 - g x2 < ε := lt_of_abs_lt habs2
    have h2 := add_lt_add_left h1 (g x2 - ε)
    have e1 : g x2 - ε + (TARGET x2 - g x2) = TARGET x2 - ε := by
      mach_mpoly [g x2, TARGET x2, ε]
    have e2 : g x2 - ε + ε = g x2 := by mach_mpoly [g x2, ε]
    rw [e1, e2] at h2
    have h3 : (0:Real) < TARGET x2 - ε := by
      have h4 := add_lt_add_left hT2 (-ε)
      have e3 : -ε + ε = (0:Real) := by mach_ring
      have e4 : -ε + TARGET x2 = TARGET x2 - ε := by mach_ring
      rw [e3, e4] at h4
      exact h4
    exact lt_trans_ax h3 h2
  obtain ⟨c, hc1, hc2, hc0⟩ := intermediate_value g x1 x2 hx1x2
    (fun z hz1 hz2 => hcont z (lt_of_lt_of_le hax1 hz1) (lt_of_le_of_lt hz2 hx2b)) hg1 hg2
  exact ⟨c, hc1, hc2, hc0⟩

private theorem neg_lt_neg' {a b : Real} (h : a < b) : -b < -a := by
  have h2 := add_lt_add_left h (-a + -b)
  have e1 : -a + -b + a = -b := by mach_mpoly [a, b]
  have e2 : -a + -b + b = -a := by mach_mpoly [a, b]
  rwa [e1, e2] at h2

private theorem continuousAt_neg (f : Real → Real) (x : Real) (hf : ContinuousAt f x) :
    ContinuousAt (fun y => -f y) x := by
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have e : (fun y => -f y) y - (fun y => -f y) x = -(f y - f x) := by
    show -f y - -f x = -(f y - f x)
    mach_ring
  rw [e, abs_neg]
  exact hδprop y hy

/-- **Piece A, mirrored** — same conclusion, opposite sign convention at the endpoints (`TARGET`
positive-then-negative instead of negative-then-positive). Needed because `sin`'s alternating
extrema switch which convention applies at each successive pair. Reduces to Piece A by negating
both `g` and `TARGET`: a zero of `-g` is a zero of `g`; `ε`-closeness and the sign constraints
both survive negation. -/
theorem induced_zero_of_eps_close' (g : Real → Real) (a b : Real)
    (hcont : ∀ z : Real, a < z → z < b → ContinuousAt g z)
    (TARGET : Real → Real) (ε : Real)
    (hclose : ∀ x : Real, a < x → x < b → abs (g x - TARGET x) < ε)
    (x1 x2 : Real) (hax1 : a < x1) (hx1x2 : x1 < x2) (hx2b : x2 < b)
    (hT1 : ε < TARGET x1) (hT2 : TARGET x2 < -ε) :
    ∃ c : Real, x1 < c ∧ c < x2 ∧ g c = 0 := by
  have hcont' : ∀ z : Real, a < z → z < b → ContinuousAt (fun y => -g y) z :=
    fun z hz1 hz2 => continuousAt_neg g z (hcont z hz1 hz2)
  have hclose' : ∀ x : Real, a < x → x < b →
      abs ((fun y => -g y) x - (fun y => -TARGET y) x) < ε := by
    intro x hxa hxb
    have e : (fun y => -g y) x - (fun y => -TARGET y) x = -(g x - TARGET x) := by
      show -g x - -TARGET x = -(g x - TARGET x)
      mach_ring
    rw [e, abs_neg]
    exact hclose x hxa hxb
  have hT1' : (fun y => -TARGET y) x1 < -ε := neg_lt_neg' hT1
  have hT2' : ε < (fun y => -TARGET y) x2 := by
    show ε < -TARGET x2
    have h := neg_lt_neg' hT2
    have e : -(-ε) = ε := by mach_ring
    rwa [e] at h
  obtain ⟨c, hc1, hc2, hc0⟩ := induced_zero_of_eps_close (fun y => -g y) a b hcont'
    (fun y => -TARGET y) ε hclose' x1 x2 hax1 hx1x2 hx2b hT1' hT2'
  refine ⟨c, hc1, hc2, ?_⟩
  have h5 : -g c = 0 := hc0
  have e2 : g c = -(-g c) := by mach_ring
  rw [e2, h5]
  exact neg_zero

/-- **Piece B — `sin(x + π) = -sin(x)`.** -/
private theorem sin_add_pi (x : Real) : Real.sin (x + pi) = -(Real.sin x) := by
  rw [sin_add, cos_pi, sin_pi, mul_zero, add_zero]
  mach_mpoly [Real.sin x]

/-- **`sin`'s alternating extrema.** `sin (π/2 + (m+1)π) = -sin (π/2 + mπ)` — each successive
extremum flips sign, via `sin_add_pi`. Base case `sin(π/2) = 1` (`sin_pi_div_two`) gives the
starting sign; the alternation is all that's needed downstream (no closed-form `(-1)^m` required). -/
private theorem sin_extremum_succ_flip (m : Nat) :
    Real.sin (pi / (1 + 1) + natCast (m + 1) * pi) = -(Real.sin (pi / (1 + 1) + natCast m * pi)) := by
  have e : pi / (1 + 1) + natCast (m + 1) * pi = (pi / (1 + 1) + natCast m * pi) + pi := by
    rw [natCast_succ]
    mach_mpoly [pi, natCast m]
  rw [e, sin_add_pi]

/-- The `j`-th extremum, `π/2 + jπ`. -/
private noncomputable def ext (j : Nat) : Real := pi / (1 + 1) + natCast j * pi

/-- **Piece B, closed form.** `sin(ext j) = 1` for even `j`, `-1` for odd `j` — the parity-indexed
value, derived from the flip fact by induction (no separate closed-form `(-1)^j` machinery). -/
private theorem sin_extremum_val (j : Nat) :
    Real.sin (ext j) = if j % 2 = 0 then (1 : Real) else -1 := by
  induction j with
  | zero =>
    show Real.sin (ext 0) = if (0 : Nat) % 2 = 0 then (1 : Real) else -1
    rw [if_pos rfl]
    show Real.sin (pi / (1 + 1) + natCast 0 * pi) = 1
    rw [natCast_zero, zero_mul, add_zero]
    exact sin_pi_div_two
  | succ m ih =>
    show Real.sin (ext (m + 1)) = if (m + 1) % 2 = 0 then (1 : Real) else -1
    have hflip : Real.sin (ext (m + 1)) = -(Real.sin (ext m)) := sin_extremum_succ_flip m
    rw [hflip, ih]
    by_cases hm : m % 2 = 0
    · rw [if_pos hm, if_neg (by omega : ¬ (m + 1) % 2 = 0)]
    · rw [if_neg hm, if_pos (by omega : (m + 1) % 2 = 0)]
      mach_mpoly [(1:Real)]

/-- **`ext` is strictly increasing.** -/
private theorem ext_strictMono {i j : Nat} (hij : i < j) : ext i < ext j := by
  show pi / (1 + 1) + natCast i * pi < pi / (1 + 1) + natCast j * pi
  apply add_lt_add_left
  exact mul_lt_mul_of_pos_right (natCast_lt_natCast_of_lt hij) pi_pos

/-- **Piece C — the per-step induced zero, either orientation, selected by `j`'s parity.**
Combines `induced_zero_of_eps_close`/`induced_zero_of_eps_close'` (whichever the sign at `ext j`
calls for, via `sin_extremum_val`) into one existence statement, hiding the case split from
callers — they only ever need "there is a zero between consecutive extrema," never which lemma
supplied it. -/
private theorem zero_exists (g : Real → Real) (A B ε : Real)
    (hcont : ∀ z : Real, A < z → z < B → ContinuousAt g z)
    (hclose : ∀ x : Real, A < x → x < B → abs (g x - Real.sin x) < ε)
    (hεlt1 : ε < 1) (j : Nat) (hAj : A < ext j) (hjB : ext (j + 1) < B) :
    ∃ c : Real, ext j < c ∧ c < ext (j + 1) ∧ g c = 0 := by
  have hextj : ext j < ext (j + 1) := ext_strictMono (Nat.lt_succ_self j)
  have hsj := sin_extremum_val j
  have hsj1 := sin_extremum_val (j + 1)
  by_cases hm : j % 2 = 0
  · -- j even: sin(ext j) = 1, sin(ext(j+1)) = -1 (positive-then-negative)
    rw [if_pos hm] at hsj
    rw [if_neg (by omega : ¬ (j + 1) % 2 = 0)] at hsj1
    have hT1 : ε < Real.sin (ext j) := by rw [hsj]; exact hεlt1
    have hT2 : Real.sin (ext (j + 1)) < -ε := by rw [hsj1]; exact neg_lt_neg' hεlt1
    exact induced_zero_of_eps_close' g A B hcont Real.sin ε hclose (ext j) (ext (j + 1))
      hAj hextj hjB hT1 hT2
  · -- j odd: sin(ext j) = -1, sin(ext(j+1)) = 1 (negative-then-positive)
    rw [if_neg hm] at hsj
    rw [if_pos (by omega : (j + 1) % 2 = 0)] at hsj1
    have hT1 : Real.sin (ext j) < -ε := by rw [hsj]; exact neg_lt_neg' hεlt1
    have hT2 : ε < Real.sin (ext (j + 1)) := by rw [hsj1]; exact hεlt1
    exact induced_zero_of_eps_close g A B hcont Real.sin ε hclose (ext j) (ext (j + 1))
      hAj hextj hjB hT1 hT2

end Real
end MachLib
