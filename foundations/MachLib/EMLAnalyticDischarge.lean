import MachLib.EMLZeroBoundAssembly
import MachLib.EMLSignInductionV2
import MachLib.AnalyticFiniteZeros

/-!
# Discharging the hard node from analyticity

`(db)` rewrote the induction so the hard node receives eventual continuity and eventual
log-argument stability without circularity, and identified the one missing piece: analyticity of an
EML value on an interval. This module adds it as an axiom and completes the argument.

## §1 an open interval is infinite

`not_realSetFinite_of_contains_interval` — a bisection sequence `bis` strictly inside `(p,q)`,
strictly decreasing, gives arbitrarily long nodup lists. Pure arithmetic, no analyticity.

## §2 the axiom

`eml_tree_analytic_on_interval` is the interval-localised twin of the existing
`eml_tree_analytic_on_pos`. The latter needs log-argument positivity on **all** of `(0, ∞)`;
declamping supplies it only per interval, which is why the existing form could not be used.

**This is a genuine addition to the trust base** — `AxiomLedger` goes 242 → 243. It is a port of the
same upstream fact `eml_tree_analytic_on_pos` ports, with the domain localised, and it is *not* a
congruence: the alternative route (transport analyticity from the encoder's barrier along pointwise
equality) was rejected because `IsAnalyticOnReals f (Icc a b)` depends on `f` near each point, so a
plain set-congruence would be **unsound**.

## §3 the identity-theorem step

`analytic_finite_zeros_compact` contraposed: analytic on `Icc a b` with an infinite zero set forces
`f ≡ 0` on `Ioo a b`. Run on the **declamped** tree, so no analyticity ever has to be transported —
only *values* transfer to `t`, and those transfer by `declamp_eval`.

## §4 the discharge

If `t.eval` vanishes identically on one far-out interval, widening the interval and re-running the
identity theorem propagates the vanishing to every point beyond it, i.e. `EvZeroF t.eval`. So
`¬ EvZeroF` gives exactly the non-vanishing input `(da)`'s assembly needs.
-/

namespace MachLib

open Real

private theorem lt_of_mul_lt_mul_left_pos' {a b c : Real} (h : c * a < c * b) (hc : 0 < c) : a < b := by
  have h' : a * c < b * c := by rw [mul_comm a c, mul_comm b c]; exact h
  exact lt_of_mul_lt_mul_right_pos h' hc

/-- Midpoint facts. -/
private theorem mid_between {p w : Real} (h : p < w) :
    p < (p + w) / (1 + 1) ∧ (p + w) / (1 + 1) < w := by
  have h2 : (0 : Real) < 1 + 1 := two_pos
  have hm : (1 + 1) * ((p + w) / (1 + 1)) = p + w := mul_div_cancel_left (ne_of_gt h2)
  constructor
  · refine lt_of_mul_lt_mul_left_pos' ?_ h2
    rw [hm]
    have : p + p < p + w := add_lt_add_left h p
    have e : (1 + 1) * p = p + p := by mach_ring
    rw [e]; exact this
  · refine lt_of_mul_lt_mul_left_pos' ?_ h2
    rw [hm]
    have v : p + w < w + w := by
      have := add_lt_add_left h w
      have e1 : w + p = p + w := by mach_ring
      rw [e1] at this; exact this
    have e : (1 + 1) * w = w + w := by mach_ring
    rw [e]; exact v

/-- A strictly decreasing sequence inside `(p,q)`. -/
private noncomputable def bis (p q : Real) : Nat → Real
  | 0     => (p + q) / (1 + 1)
  | n + 1 => (p + bis p q n) / (1 + 1)

private theorem bis_mem {p q : Real} (hpq : p < q) : ∀ n, p < bis p q n ∧ bis p q n < q := by
  intro n
  induction n with
  | zero => exact mid_between hpq
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨g1, g2⟩ := mid_between h1
      exact ⟨g1, lt_trans_ax g2 h2⟩

private theorem bis_dec {p q : Real} (hpq : p < q) : ∀ n, bis p q (n + 1) < bis p q n := by
  intro n
  exact (mid_between (bis_mem hpq n).1).2

private theorem bis_anti {p q : Real} (hpq : p < q) :
    ∀ i j : Nat, i < j → bis p q j < bis p q i := by
  intro i j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge i k with hlt | hge
      · exact lt_trans_ax (bis_dec hpq k) (ih hlt)
      · have : i = k := Nat.le_antisymm (by omega) hge
        rw [this]; exact bis_dec hpq k

private noncomputable def bisList (p q : Real) : Nat → List Real
  | 0     => [bis p q 0]
  | k + 1 => bis p q (k + 1) :: bisList p q k

private theorem bisList_length (p q : Real) : ∀ k : Nat, (bisList p q k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih => show (bisList p q m).length + 1 = m + 1 + 1; rw [ih]

private theorem bisList_bounds {p q : Real} (hpq : p < q) :
    ∀ (k : Nat) (z : Real), z ∈ bisList p q k → bis p q k ≤ z ∧ p < z ∧ z < q := by
  intro k
  induction k with
  | zero =>
      intro z hz
      have hzz : z = bis p q 0 := by simpa [bisList] using hz
      rw [hzz]
      exact ⟨le_refl _, (bis_mem hpq 0).1, (bis_mem hpq 0).2⟩
  | succ m ih =>
      intro z hz
      rcases List.mem_cons.mp hz with hh | ht
      · rw [hh]
        exact ⟨le_refl _, (bis_mem hpq (m + 1)).1, (bis_mem hpq (m + 1)).2⟩
      · obtain ⟨hle, h1, h2⟩ := ih z ht
        exact ⟨le_trans (le_of_lt (bis_dec hpq m)) hle, h1, h2⟩

private theorem bisList_nodup {p q : Real} (hpq : p < q) :
    ∀ k : Nat, (bisList p q k).Nodup := by
  intro k
  induction k with
  | zero => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ m ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      obtain ⟨hle, _, _⟩ := bisList_bounds hpq m _ hmem
      exact (ne_of_lt (lt_of_lt_of_le (bis_dec hpq m) hle)) rfl

/-- **An open interval is infinite.** A set containing one is not `RealSetFinite`. -/
theorem not_realSetFinite_of_contains_interval {s : RealSet} {p q : Real} (hpq : p < q)
    (hsub : ∀ x : Real, p < x → x < q → s x) : ¬ RealSetFinite s := by
  rintro ⟨n, hn⟩
  have hb := hn (bisList p q n) (bisList_nodup hpq n)
    (fun z hz => by
      obtain ⟨_, h1, h2⟩ := bisList_bounds hpq n z hz
      exact hsub z h1 h2)
  rw [bisList_length p q n] at hb
  omega


/-! ## §2 — the axiom

Interval-localised twin of `eml_tree_analytic_on_pos`. `AxiomLedger` 242 → 243. -/

/-- **An EML tree with all log arguments positive on `(a,b)` is analytic strictly inside it.**

Interval-localised port of `eml_tree_analytic_on_pos`, which states the same fact with the domain
fixed to `(0, ∞)` and the side condition `EMLLogArgPosOnIoi`. The side condition here is the same one
localised: `LogArgPos t a b`. Strictly inside, because analyticity at a point needs a neighbourhood
and `LogArgPos` only controls the open interval. -/
axiom eml_tree_analytic_on_interval (t : EMLTree) (a b : Real) :
    LogArgPos t a b →
    ∀ a' b' : Real, a < a' → b' < b → IsAnalyticOnReals t.eval (Icc a' b')

/-! ## §3 — the identity-theorem step -/

/-- **Contrapositive of `analytic_finite_zeros_compact`.** Analytic on `Icc a b` with a zero set
containing an interval forces vanishing on all of `Ioo a b`. -/
theorem eq_zero_on_Ioo_of_zero_on_subinterval {f : Real → Real} {a b p q : Real}
    (hab : a < b) (hpq : p < q)
    (hsub : ∀ x : Real, p < x → x < q → a ≤ x ∧ x ≤ b)
    (han : IsAnalyticOnReals f (Icc a b))
    (hz : ∀ x : Real, p < x → x < q → f x = 0) :
    ∀ x : Real, a < x → x < b → f x = 0 := by
  intro x hxa hxb
  rcases Classical.em (f x = 0) with h | h
  · exact h
  · exact absurd (analytic_finite_zeros_compact f a b hab han ⟨x, ⟨hxa, hxb⟩, h⟩)
      (not_realSetFinite_of_contains_interval hpq
        (fun y hy1 hy2 => ⟨hsub y hy1 hy2, hz y hy1 hy2⟩))

/-! ## §4 — vanishing on one interval propagates to a ray -/

private theorem sub_one_lt' (a : Real) : a - 1 < a := by
  have v := add_lt_add_left zero_lt_one_ax (a - 1)
  have l : a - 1 + 0 = a - 1 := by mach_ring
  have r : a - 1 + 1 = a := by mach_ring
  rw [l, r] at v; exact v

private theorem lt_add_one' (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have l : a + 0 = a := by mach_ring
  rw [l] at v; exact v

private theorem le_sub_one' {X a : Real} (h : X + 1 ≤ a) : X ≤ a - 1 := by
  have v := add_le_add_wit h (le_refl (-(1 : Real)))
  have e1 : X + 1 + -(1 : Real) = X := by mach_ring
  have e2 : a + -(1 : Real) = a - 1 := by mach_ring
  rw [e1, e2] at v; exact v

/-- **Vanishing on one far-out interval propagates to a whole ray.** Widen the interval past any
target point, re-run the identity theorem on the declamped tree there, and transfer the value back. -/
theorem evZeroF_of_zero_on_interval (t : EMLTree) (X₀ : Real)
    (hst : ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b)
    (a b : Real) (hXa : X₀ + 1 ≤ a) (hab : a < b)
    (hz : ∀ x : Real, a < x → x < b → t.eval x = 0) :
    EvZeroF t.eval := by
  have key : ∀ x : Real, a < x → t.eval x = 0 := by
    intro x hax
    have hgen : ∀ M : Real, b ≤ M → x ≤ M → t.eval x = 0 := by
      intro M hbM hxM
      have haM : a < M := lt_of_lt_of_le hab hbM
      have hPQ : a - 1 < M + 1 + 1 :=
        lt_trans_ax (sub_one_lt' a)
          (lt_trans_ax haM (lt_trans_ax (lt_add_one' M) (lt_add_one' (M + 1))))
      have hstab : LogArgStable t (a - 1) (M + 1 + 1) := hst _ _ (le_sub_one' hXa) hPQ
      have hin : ∀ z : Real, a - 1 < z → z < M + 1 + 1 →
          (declamp t (a - 1) (M + 1 + 1)).eval z = t.eval z :=
        declamp_eval t (a - 1) (M + 1 + 1) hstab
      have han : IsAnalyticOnReals (declamp t (a - 1) (M + 1 + 1)).eval (Icc a (M + 1)) :=
        eml_tree_analytic_on_interval _ (a - 1) (M + 1 + 1)
          (declamp_logArgPos t (a - 1) (M + 1 + 1) hstab) a (M + 1)
          (sub_one_lt' a) (lt_add_one' (M + 1))
      have hzv : ∀ y : Real, a < y → y < b → (declamp t (a - 1) (M + 1 + 1)).eval y = 0 := by
        intro y hy1 hy2
        rw [hin y (lt_trans_ax (sub_one_lt' a) hy1)
          (lt_trans_ax (lt_of_lt_of_le hy2 hbM)
            (lt_trans_ax (lt_add_one' M) (lt_add_one' (M + 1))))]
        exact hz y hy1 hy2
      have hall := eq_zero_on_Ioo_of_zero_on_subinterval
        (f := (declamp t (a - 1) (M + 1 + 1)).eval) (a := a) (b := M + 1) (p := a) (q := b)
        (lt_trans_ax haM (lt_add_one' M)) hab
        (fun y hy1 hy2 => ⟨le_of_lt hy1,
          le_of_lt (lt_trans_ax (lt_of_lt_of_le hy2 hbM) (lt_add_one' M))⟩)
        han hzv
      have hx := hall x hax (lt_of_le_of_lt hxM (lt_add_one' M))
      rw [hin x (lt_trans_ax (sub_one_lt' a) hax)
        (lt_trans_ax (lt_of_le_of_lt hxM (lt_add_one' M)) (lt_add_one' (M + 1)))] at hx
      exact hx
    exact hgen (MachLib.Real.max b x) (le_max_left b x) (le_max_right b x)
  refine ⟨MachLib.Real.max 1 (a + 1), le_max_left 1 (a + 1), fun x hx => ?_⟩
  exact key x (lt_of_lt_of_le (lt_add_one' a) (le_trans (le_max_right 1 (a + 1)) hx))

/-- **Not eventually zero gives the non-vanishing input.** -/
theorem nonvanishing_of_not_evZeroF (t : EMLTree) (X₀ : Real)
    (hst : ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b)
    (hnz : ¬ EvZeroF t.eval) :
    ∀ a b : Real, X₀ + 1 ≤ a → a < b → ∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0 := by
  intro a b hXa hab
  rcases Classical.em (∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0) with h | h
  · exact h
  · exact absurd (evZeroF_of_zero_on_interval t X₀ hst a b hXa hab
      (fun x h1 h2 => Classical.byContradiction (fun hne => h ⟨x, h1, h2, hne⟩))) hnz

/-! ## §5 — the hard node, discharged -/

private theorem eml_fun (A B : EMLTree) :
    (EMLTree.eml A B).eval = fun x => exp (A.eval x) - log (B.eval x) := by
  funext x; rfl

private theorem ray_join3' {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

/-- **The hard node is discharged.** Either the node value is eventually zero — and then it is
eventually `≤ 0`, so `EvSign` holds outright — or it is not, and then §4 supplies the non-vanishing
input, `(da)`'s assembly turns that into a uniform zero bound, the ray bridge turns *that* into
eventual non-vanishing, and continuity plus the IVT finish it.

Both ingredients the obligation is handed — eventual continuity and eventual log-argument stability —
are used, and neither is assumed of the caller: the induction of `(db)` manufactures both. -/
theorem signHardCtsStable_holds : SignHardCtsStable := by
  intro A B X₀ hX₀ hpos hcont hstable
  obtain ⟨X, hX1, hst⟩ := hstable
  rcases Classical.em (EvZeroF (fun x => exp (A.eval x) - log (B.eval x))) with hz | hz
  · obtain ⟨Y, hY1, hzero⟩ := hz
    exact Or.inr ⟨Y, hY1, fun x hx => le_of_eq (hzero x hx)⟩
  · have hzt : ¬ EvZeroF (EMLTree.eml A B).eval := by rw [eml_fun A B]; exact hz
    obtain ⟨N, hN⟩ := uniformZeroBoundFrom_of_nonvanishing (EMLTree.eml A B) X hst
      (nonvanishing_of_not_evZeroF (EMLTree.eml A B) X hst hzt)
    obtain ⟨Yz, hYz1, hne⟩ := eventually_nonzero_of_uniformZeroBoundFrom hN
    obtain ⟨Yc, hYc1, hcc⟩ := hcont
    obtain ⟨R, hR1, hRz, hRc⟩ := ray_join3' hYz1 hYc1
    rw [eml_fun A B] at hne
    exact evSign_of_continuous_nonzero_on_ray hR1
      (fun x hx => hne x (le_trans hRz hx))
      (fun x hx => hcc x (le_trans hRc hx))

/-- **Sign-definiteness at every depth, unconditionally.** -/
theorem evSign_all (t : EMLTree) : EvSign t.eval :=
  evSign_of_ctsStable signHardCtsStable_holds t

/-- **`SignHardCase` holds.** The positivity hypothesis is not even consumed — the node's sign is
decided whether or not its log argument is the real one. -/
theorem signHardCase_holds : SignHardCase := by
  intro A B X₀ _ _
  have h := evSign_all (EMLTree.eml A B)
  rw [eml_fun A B] at h
  exact h

end MachLib
