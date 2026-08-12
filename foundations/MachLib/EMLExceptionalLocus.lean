import MachLib.EMLConstantFree
import MachLib.IntermediateValue
import MachLib.DerivMinimality
import MachLib.EMLTChartKhovanskii

/-!
# T3, first artifact: an exceptional locus solved for exactly

This arm keeps producing **exceptional sets** by accident — parameter values where a family's
qualitative behaviour changes, sitting on a transcendental locus that generic reasoning walks past.
It has already cost something: a grid search over 12,208 samples reported non-existence and missed a
witness living on exactly such a set.

The repair is to solve for these loci **deliberately**. This module does it for the one the arm
knows best, the depth-4 reciprocal family `invX4gen c₀ c₁`.

`EMLDepth2InvX` supplies the *sufficient* direction (`invX4gen_eval`: the relation implies the tree
computes `1/x`) and *existence* (`invX4gen_witness_for_any_c1`). Neither says the relation is
**necessary**, and without that there is no locus — only a supply of witnesses.

* **`invX4gen_iff`** — the tree computes `1/x` **if and only if** `exp(exp c₀) − exp(exp c₁) = 1`.
  The forward direction needs a **single point**, `x = 1`, where `log 1 = 0` collapses both branches.
* **`invX4gen_locus_unique`** — for each `c₁` at most one `c₀` works, so the locus is a **graph**.
* **`invX4gen_locus_solved`** — and exactly one does, namely `c₀ = log (log (1 + exp (exp c₁)))`.
  The locus is that explicit transcendental curve, nothing more and nothing less.
* **`invX4gen_off_locus`** — every other `(c₀, c₁)` fails. This is the statement that makes the grid
  failure inevitable rather than unlucky: the good set is a graph over one parameter, so sampling
  `c₀` independently misses it unless the sample lands on the curve exactly.

The template generalises: for a parameterised family, prove the behaviour is **equivalent** to an
equation, then solve the equation. "Here is a witness" is not a locus; "here is precisely the set" is.
-/

namespace MachLib

open Real

/-- The family's value at `x = 1`, where `log 1 = 0` collapses every branch. This single point is the
whole forward direction. -/
theorem invX4gen_eval_at_one (c0 c1 : Real) :
    (invX4gen c0 c1).eval 1 = exp (exp c0) - exp (exp c1) := by
  show exp ((EMLTree.eml (EMLTree.const c0) EMLTree.var).eval 1)
      - log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
          (EMLTree.const 1)) (EMLTree.const 1)).eval 1) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp ((EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
          (EMLTree.const 1)).eval 1) - log ((EMLTree.const (1 : Real)).eval 1)) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp (exp ((EMLTree.eml (EMLTree.const c1) EMLTree.var).eval 1)
          - log ((EMLTree.const (1 : Real)).eval 1)) - log (1 : Real)) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp (exp (exp c1 - log (1 : Real)) - log (1 : Real)) - log (1 : Real)) = _
  rw [log_one]
  have e0 : exp c0 - (0 : Real) = exp c0 := by mach_mpoly [exp c0]
  have e1 : exp c1 - (0 : Real) = exp c1 := by mach_mpoly [exp c1]
  rw [e0, e1]
  have e2 : exp (exp c1) - (0 : Real) = exp (exp c1) := by mach_mpoly [exp (exp c1)]
  rw [e2]
  have e3 : exp (exp (exp c1)) - (0 : Real) = exp (exp (exp c1)) := by
    mach_mpoly [exp (exp (exp c1))]
  rw [e3, log_exp]

/-- **The locus, exactly.** The relation is not merely sufficient — it is equivalent. -/
theorem invX4gen_iff (c0 c1 : Real) :
    (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x)
      ↔ exp (exp c0) - exp (exp c1) = 1 := by
  constructor
  · intro h
    have h1 := h 1 zero_lt_one_ax
    rw [invX4gen_eval_at_one] at h1
    have hone : (1 : Real) / 1 = 1 := by
      have hv := mul_inv (1 : Real) (ne_of_gt zero_lt_one_ax)
      have l : (1 : Real) * (1 / 1) = 1 / 1 := by mach_mpoly [(1 / 1 : Real)]
      rw [l] at hv; exact hv
    rw [hone] at h1; exact h1
  · intro hfam; exact invX4gen_eval hfam

/-- **At most one `c₀` per `c₁`**: the locus is a graph, not a region. -/
theorem invX4gen_locus_unique {c1 c0 c0' : Real}
    (h : exp (exp c0) - exp (exp c1) = 1) (h' : exp (exp c0') - exp (exp c1) = 1) :
    c0 = c0' := by
  have heq : exp (exp c0) = exp (exp c0') := by
    have u : exp (exp c0) - exp (exp c1) + exp (exp c1)
        = exp (exp c0') - exp (exp c1) + exp (exp c1) := by rw [h, h']
    have l : exp (exp c0) - exp (exp c1) + exp (exp c1) = exp (exp c0) := by
      mach_mpoly [exp (exp c0), exp (exp c1)]
    have r : exp (exp c0') - exp (exp c1) + exp (exp c1) = exp (exp c0') := by
      mach_mpoly [exp (exp c0'), exp (exp c1)]
    rw [l, r] at u; exact u
  have h1 : exp c0 = exp c0' := by
    have u : log (exp (exp c0)) = log (exp (exp c0')) := by rw [heq]
    rw [log_exp, log_exp] at u; exact u
  have u : log (exp c0) = log (exp c0') := by rw [h1]
  rw [log_exp, log_exp] at u; exact u

/-- **And exactly one does.** The locus is the explicit transcendental curve
`c₀ = log (log (1 + exp (exp c₁)))`. -/
theorem invX4gen_locus_solved (c1 : Real) :
    exp (exp (log (log (1 + exp (exp c1))))) - exp (exp c1) = 1 := by
  have hK : (0 : Real) < exp (exp c1) := exp_pos _
  have h1K : (1 : Real) < 1 + exp (exp c1) := by
    have u := add_lt_add_left hK 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hpos : (0 : Real) < 1 + exp (exp c1) := lt_trans_ax zero_lt_one_ax h1K
  have hlogpos : (0 : Real) < log (1 + exp (exp c1)) := by
    have hm := log_lt_log zero_lt_one_ax h1K
    rw [log_one] at hm; exact hm
  rw [exp_log hlogpos, exp_log hpos]
  mach_mpoly [exp (exp c1)]

/-- **Every other parameter pair fails.** The good set is a graph over `c₁`, so an independent sweep
of `c₀` misses it unless a sample lands on the curve exactly — which is why a grid found nothing. -/
theorem invX4gen_off_locus (c0 c1 : Real) (h : exp (exp c0) - exp (exp c1) ≠ 1) :
    ¬ (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x) :=
  fun hc => h ((invX4gen_iff c0 c1).mp hc)

/-- The locus, packaged: for every `c₁` there is a **unique** `c₀`, given explicitly, and it is
exactly the set of parameters for which the depth-4 family computes `1/x`. -/
theorem invX4gen_locus_is_a_graph (c1 : Real) :
    (∀ x : Real, 0 < x →
        (invX4gen (log (log (1 + exp (exp c1)))) c1).eval x = 1 / x)
    ∧ ∀ c0 : Real, (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x)
        → c0 = log (log (1 + exp (exp c1))) :=
  ⟨(invX4gen_iff _ c1).mpr (invX4gen_locus_solved c1),
   fun c0 hc => invX4gen_locus_unique ((invX4gen_iff c0 c1).mp hc) (invX4gen_locus_solved c1)⟩

/-! ## ▸ The Ω point: the second locus, solved completely

`depth_le_one_trichotomy`'s third branch carries a clause conditional on `exp (−G) = G`. That is the
**Ω point** (equivalently `G·exp G = 1`), and it is where the linear floor degenerates and the
quadratic one is needed. Until now it appeared only as a hypothesis nobody had solved: it was not
known whether the degenerate case *occurs*, nor whether it could occur more than once.

Both are settled here, and the answers are the two halves a locus needs:

* **`omega_point_bracket`** — any solution lies strictly inside `(e⁻¹, 1)`. An explicit cage.
* **`omega_point_unique`** — at most one, because `exp(−G)` decreases while `G` increases.
* **`omega_point_exists`** — at least one, by the intermediate value theorem on `G ↦ G − exp(−G)`,
  which is negative at `e⁻¹` and positive at `1`.

So the degeneracy is **real and isolated**: exactly one parameter value in the whole positive line.
That is why the quadratic floor could not be avoided, and why no perturbation argument reaches it.
-/

private theorem exp_neg_one_lt_one_locus : exp (-1 : Real) < 1 := by
  have hneg : (-1 : Real) < 0 := by
    have u := add_lt_add_left zero_lt_one_ax (-1 : Real)
    have l : (-1 : Real) + 0 = -1 := by mach_ring
    have r : (-1 : Real) + 1 = 0 := by mach_ring
    rw [l, r] at u; exact u
  have hm := exp_lt hneg
  rw [exp_zero] at hm; exact hm

/-- **The cage.** Every positive solution of `exp (−G) = G` lies strictly between `e⁻¹` and `1`. -/
theorem omega_point_bracket {G : Real} (hG : 0 < G) (h : exp (-G) = G) :
    exp (-1 : Real) < G ∧ G < 1 := by
  have hlt1 : G < 1 := by
    rcases lt_total G 1 with hl | he | hg
    · exact hl
    · exfalso
      rw [he] at h
      exact lt_irrefl_ax _ (h ▸ exp_neg_one_lt_one_locus)
    · exfalso
      have hnn : -G < -1 := by
        have u := add_lt_add_left hg (-G + -1)
        have l : -G + -1 + 1 = -G := by mach_mpoly [G]
        have r : -G + -1 + G = -1 := by mach_mpoly [G]
        rw [l, r] at u; exact u
      have hm := exp_lt hnn
      rw [h] at hm
      exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hm exp_neg_one_lt_one_locus) hg)
  refine ⟨?_, hlt1⟩
  rcases lt_total (exp (-1 : Real)) G with hl | he | hg
  · exact hl
  · exfalso
    -- `G = e⁻¹` would force `exp (−e⁻¹) = e⁻¹`, i.e. `1 ≤ e⁻¹`
    rw [← he] at h
    have hm := exp_lt (by
      have u := add_lt_add_left exp_neg_one_lt_one_locus (-1 + -exp (-1 : Real))
      have l : -1 + -exp (-1 : Real) + exp (-1 : Real) = -1 := by
        mach_mpoly [exp (-1 : Real)]
      have r : -1 + -exp (-1 : Real) + 1 = -exp (-1 : Real) := by
        mach_mpoly [exp (-1 : Real)]
      rw [l, r] at u; exact u : (-1 : Real) < -exp (-1 : Real))
    rw [h] at hm
    exact lt_irrefl_ax _ hm
  · exfalso
    have hnn : -exp (-1 : Real) < -G := by
      have u := add_lt_add_left hg (-exp (-1 : Real) + -G)
      have l : -exp (-1 : Real) + -G + G = -exp (-1 : Real) := by
        mach_mpoly [G, exp (-1 : Real)]
      have r : -exp (-1 : Real) + -G + exp (-1 : Real) = -G := by
        mach_mpoly [G, exp (-1 : Real)]
      rw [l, r] at u; exact u
    have hm := exp_lt hnn
    rw [h] at hm
    -- `exp (−e⁻¹) < G ≤ e⁻¹` while `−1 < −e⁻¹` gives `e⁻¹ < exp (−e⁻¹)`
    have hgt : exp (-1 : Real) < exp (-exp (-1 : Real)) := by
      refine exp_lt ?_
      have u := add_lt_add_left exp_neg_one_lt_one_locus (-1 + -exp (-1 : Real))
      have l : -1 + -exp (-1 : Real) + exp (-1 : Real) = -1 := by
        mach_mpoly [exp (-1 : Real)]
      have r : -1 + -exp (-1 : Real) + 1 = -exp (-1 : Real) := by
        mach_mpoly [exp (-1 : Real)]
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hgt hm) hg)

/-- **At most one.** `exp (−G)` strictly decreases while `G` strictly increases, so they meet once. -/
theorem omega_point_unique {G G' : Real} (h : exp (-G) = G) (h' : exp (-G') = G') : G = G' := by
  rcases lt_total G G' with hl | he | hg
  · exfalso
    have hnn : -G' < -G := by
      have u := add_lt_add_left hl (-G + -G')
      have l : -G + -G' + G = -G' := by mach_mpoly [G, G']
      have r : -G + -G' + G' = -G := by mach_mpoly [G, G']
      rw [l, r] at u; exact u
    have hm := exp_lt hnn
    rw [h, h'] at hm
    exact lt_irrefl_ax _ (lt_trans_ax hl hm)
  · exact he
  · exfalso
    have hnn : -G < -G' := by
      have u := add_lt_add_left hg (-G + -G')
      have l : -G + -G' + G' = -G := by mach_mpoly [G, G']
      have r : -G + -G' + G = -G' := by mach_mpoly [G, G']
      rw [l, r] at u; exact u
    have hm := exp_lt hnn
    rw [h, h'] at hm
    exact lt_irrefl_ax _ (lt_trans_ax hg hm)

/-- **At least one.** IVT on `G ↦ G − exp (−G)`, negative at `e⁻¹` and positive at `1`. So the
degeneracy in `depth_le_one_trichotomy` genuinely occurs — the quadratic floor is not defending
against an empty case. -/
theorem omega_point_exists : ∃ G : Real, exp (-1 : Real) < G ∧ G < 1 ∧ exp (-G) = G := by
  have hab : exp (-1 : Real) < 1 := exp_neg_one_lt_one_locus
  have hdiff : ∀ z : Real, exp (-1 : Real) ≤ z → z ≤ 1 →
      ∃ f' : Real, HasDerivAt (fun G => G - exp (-G)) f' z := by
    intro z _ _
    have hid : HasDerivAt (fun t : Real => t) 1 z := HasDerivAt_id z
    have hneg : HasDerivAt (fun t : Real => -t) (-1) z :=
      hasDerivAt_neg_derivable (fun t : Real => t) 1 z hid
    have hexp : HasDerivAt (fun t : Real => exp (-t)) (exp (-z) * (-1)) z :=
      hasDerivAt_exp_comp (fun t : Real => -t) (-1) z hneg
    exact ⟨1 - exp (-z) * (-1),
      hasDerivAt_sub_derivable (fun t : Real => t) (fun t : Real => exp (-t))
        1 (exp (-z) * (-1)) z hid hexp⟩
  have hfa : exp (-1 : Real) - exp (-exp (-1 : Real)) < 0 := by
    have hgt : exp (-1 : Real) < exp (-exp (-1 : Real)) := by
      refine exp_lt ?_
      have u := add_lt_add_left exp_neg_one_lt_one_locus (-1 + -exp (-1 : Real))
      have l : -1 + -exp (-1 : Real) + exp (-1 : Real) = -1 := by
        mach_mpoly [exp (-1 : Real)]
      have r : -1 + -exp (-1 : Real) + 1 = -exp (-1 : Real) := by
        mach_mpoly [exp (-1 : Real)]
      rw [l, r] at u; exact u
    have u := add_lt_add_left hgt (-exp (-exp (-1 : Real)))
    have l : -exp (-exp (-1 : Real)) + exp (-1 : Real)
        = exp (-1 : Real) - exp (-exp (-1 : Real)) := by
      mach_mpoly [exp (-1 : Real), exp (-exp (-1 : Real))]
    have r : -exp (-exp (-1 : Real)) + exp (-exp (-1 : Real)) = 0 := by
      mach_mpoly [exp (-exp (-1 : Real))]
    rw [l, r] at u; exact u
  have hfb : (0 : Real) < 1 - exp (-1 : Real) := by
    have u := add_lt_add_left exp_neg_one_lt_one_locus (-exp (-1 : Real))
    have l : -exp (-1 : Real) + exp (-1 : Real) = 0 := by mach_mpoly [exp (-1 : Real)]
    have r : -exp (-1 : Real) + 1 = 1 - exp (-1 : Real) := by mach_mpoly [exp (-1 : Real)]
    rw [l, r] at u; exact u
  obtain ⟨c, hc1, hc2, hc0⟩ :=
    intermediate_value_of_hasDerivAt (fun G => G - exp (-G)) (exp (-1 : Real)) 1 hab hdiff hfa hfb
  refine ⟨c, hc1, hc2, ?_⟩
  have e : c - exp (-c) = 0 := hc0
  have u : c - exp (-c) + exp (-c) = 0 + exp (-c) := by rw [e]
  have l : c - exp (-c) + exp (-c) = c := by mach_mpoly [c, exp (-c)]
  have r : (0 : Real) + exp (-c) = exp (-c) := by mach_mpoly [exp (-c)]
  rw [l, r] at u; exact u.symm

/-- **The Ω locus, packaged: exactly one point, and it is caged.** -/
theorem omega_point_is_a_single_caged_value :
    (∃ G : Real, exp (-1 : Real) < G ∧ G < 1 ∧ exp (-G) = G)
    ∧ (∀ G G' : Real, exp (-G) = G → exp (-G') = G' → G = G')
    ∧ (∀ G : Real, 0 < G → exp (-G) = G → exp (-1 : Real) < G ∧ G < 1) :=
  ⟨omega_point_exists, fun _ _ h h' => omega_point_unique h h',
   fun _ hG h => omega_point_bracket hG h⟩

end MachLib
