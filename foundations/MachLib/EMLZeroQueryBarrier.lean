import MachLib.EMLBasisOverhead

/-!
# The zero-query barrier: what an `F`-free `L_F` term can compute

The first lower-bound instrument on the `L_F` side. Everything else in this development is an upper
bound or an exact count of a construction; this says a construction is **necessary**.

The chain is deliberately narrow:

```
fOcc T = 0  ⟹  T is eventually polynomially bounded  ⟹  T ≠ exp
```

so any target with proved super-polynomial growth automatically costs at least one `F`-query. The
reusable theorem is the *envelope*, not `exp_not_rational` — `exp` is only the first customer.

## Scope, stated up front: this closes the division-free case

`divFree T` is a hypothesis and it is load-bearing. The envelope induction closes for constants, the
variable, `+`, `−` and `×`; it does **not** close for `÷`, and the reason is precise.

To bound `a / b` one needs `|b|` bounded *below*, so the invariant has to be two-sided: an upper
envelope together with "eventually zero, or eventually `≥ c/xᴹ`". That strengthened invariant is
closed under `×` and `÷` — but **not under `+`**, because two terms can cancel to something of
strictly smaller order (`x` and `−x + 1/x` sum to `1/x`) and the leading-order data of the summands
does not determine the order of the sum. Recovering it needs the *full* rational germ at `+∞`, i.e. a
Laurent normal form with descent through cancelling leading terms.

So the obstruction is **cancellation under addition** — the same shape that gates the EML depth
program — and it is recorded as a refinement of the ledger row rather than hidden in a hypothesis.
-/

namespace MachLib

open Real

/-! ## A. The syntactic boundary -/

/-- `fOcc T = 0` is exactly "`T` has no `F` node", in the form the `fArgs`-based DAG measure sees. -/
theorem fOcc_zero_iff_fArgs_nil : ∀ T : FTerm, fOcc T = 0 ↔ fArgs T = [] := by
  intro T
  induction T with
  | const c => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | var => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | add a b iha ihb =>
      constructor
      · intro h
        have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
        have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
        show fArgs a ++ fArgs b = []
        rw [iha.mp ha, ihb.mp hb]; rfl
      · intro h
        have h' : fArgs a ++ fArgs b = [] := h
        have ha := iha.mpr (List.append_eq_nil_iff.mp h').1
        have hb := ihb.mpr (List.append_eq_nil_iff.mp h').2
        simp only [fOcc]; omega
  | sub a b iha ihb =>
      constructor
      · intro h
        have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
        have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
        show fArgs a ++ fArgs b = []
        rw [iha.mp ha, ihb.mp hb]; rfl
      · intro h
        have h' : fArgs a ++ fArgs b = [] := h
        have ha := iha.mpr (List.append_eq_nil_iff.mp h').1
        have hb := ihb.mpr (List.append_eq_nil_iff.mp h').2
        simp only [fOcc]; omega
  | mul a b iha ihb =>
      constructor
      · intro h
        have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
        have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
        show fArgs a ++ fArgs b = []
        rw [iha.mp ha, ihb.mp hb]; rfl
      · intro h
        have h' : fArgs a ++ fArgs b = [] := h
        have ha := iha.mpr (List.append_eq_nil_iff.mp h').1
        have hb := ihb.mpr (List.append_eq_nil_iff.mp h').2
        simp only [fOcc]; omega
  | div a b iha ihb =>
      constructor
      · intro h
        have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
        have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
        show fArgs a ++ fArgs b = []
        rw [iha.mp ha, ihb.mp hb]; rfl
      · intro h
        have h' : fArgs a ++ fArgs b = [] := h
        have ha := iha.mpr (List.append_eq_nil_iff.mp h').1
        have hb := ihb.mpr (List.append_eq_nil_iff.mp h').2
        simp only [fOcc]; omega
  | F a iha =>
      constructor
      · intro h; simp only [fOcc] at h; omega
      · intro h; exact absurd h (by simp [fArgs])

/-- No `÷` node. -/
def divFree : FTerm → Prop
  | .const _ => True
  | .var     => True
  | .add a b => divFree a ∧ divFree b
  | .sub a b => divFree a ∧ divFree b
  | .mul a b => divFree a ∧ divFree b
  | .div _ _ => False
  | .F a     => divFree a

/-! ## B. The eventual polynomial envelope -/

theorem powNat_zero (x : Real) : powNat x 0 = 1 := rfl

private theorem le_add_nonneg {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

theorem powNat_pos {x : Real} (hx : 0 < x) : ∀ n : Nat, 0 < powNat x n := by
  intro n
  induction n with
  | zero => exact zero_lt_one_ax
  | succ k ih => exact mul_pos hx ih

theorem powNat_add (x : Real) : ∀ m n : Nat, powNat x (m + n) = powNat x m * powNat x n := by
  intro m
  induction m with
  | zero =>
      intro n
      simp only [Nat.zero_add]
      show powNat x n = 1 * powNat x n
      mach_ring
  | succ k ih =>
      intro n
      have e : k + 1 + n = (k + n) + 1 := by omega
      rw [e]
      show x * powNat x (k + n) = x * powNat x k * powNat x n
      rw [ih n]; mach_ring

theorem powNat_mono_exp {x : Real} (hx : 1 ≤ x) {m n : Nat} (h : m ≤ n) :
    powNat x m ≤ powNat x n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [powNat_add]
  have h1 : (1 : Real) ≤ powNat x k := one_le_powNat hx k
  have hm : (0 : Real) ≤ powNat x m := le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx) m)
  have v := mul_le_mul_of_nonneg_left h1 hm
  have e : powNat x m * 1 = powNat x m := by mach_ring
  rw [e] at v; exact v

/-- `f` is bounded by a polynomial from some point on. Nothing here is optimised — `C` and `N` are
existentials and no attempt is made to make them tight. -/
def PolyEnvelope (f : Real → Real) : Prop :=
  ∃ (C : Real) (N : Nat) (X : Real), 0 ≤ C ∧ 1 ≤ X ∧
    ∀ x : Real, X ≤ x → abs (f x) ≤ C * powNat x N

private theorem two_bounds {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

/-- **The zero-query envelope.** Every `F`-free, division-free `L_F` term is eventually bounded by a
polynomial.

The induction is one line per constructor and closes because each of `+`, `−`, `×` composes
envelopes; `÷` is excluded by hypothesis and `F` by `fOcc T = 0`. -/
theorem polyEnvelope_of_zero_query :
    ∀ T : FTerm, fOcc T = 0 → divFree T → PolyEnvelope (FTerm.eval T) := by
  intro T
  induction T with
  | const c =>
      intro _ _
      refine ⟨abs c, 0, 1, abs_nonneg c, le_refl 1, fun x _ => ?_⟩
      show abs c ≤ abs c * powNat x 0
      rw [powNat_zero]
      have e : abs c * 1 = abs c := by mach_ring
      rw [e]; exact le_refl _
  | var =>
      intro _ _
      refine ⟨1, 1, 1, le_of_lt zero_lt_one_ax, le_refl 1, fun x hx => ?_⟩
      show abs x ≤ 1 * powNat x 1
      have hxp : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
      rw [abs_of_nonneg hxp]
      show x ≤ 1 * (x * powNat x 0)
      rw [powNat_zero]
      have e : (1 : Real) * (x * 1) = x := by mach_ring
      rw [e]; exact le_refl _
  | add a b iha ihb =>
      intro h hd
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨C₁, N₁, X₁, hC₁, hX₁, h₁⟩ := iha ha hd.1
      obtain ⟨C₂, N₂, X₂, hC₂, hX₂, h₂⟩ := ihb hb hd.2
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds hX₁ hX₂
      refine ⟨C₁ + C₂, max N₁ N₂, X, add_nonneg hC₁ hC₂, hX, fun x hx => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans hX hx
      have hu₁ := h₁ x (le_trans hXa hx)
      have hu₂ := h₂ x (le_trans hXb hx)
      have hm₁ : C₁ * powNat x N₁ ≤ C₁ * powNat x (max N₁ N₂) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_left N₁ N₂)) hC₁
      have hm₂ : C₂ * powNat x N₂ ≤ C₂ * powNat x (max N₁ N₂) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_right N₁ N₂)) hC₂
      have htri : abs (FTerm.eval a x + FTerm.eval b x)
          ≤ abs (FTerm.eval a x) + abs (FTerm.eval b x) := abs_add _ _
      have hsum : abs (FTerm.eval a x) + abs (FTerm.eval b x)
          ≤ C₁ * powNat x (max N₁ N₂) + C₂ * powNat x (max N₁ N₂) :=
        add_le_add_wit (le_trans hu₁ hm₁) (le_trans hu₂ hm₂)
      have e : C₁ * powNat x (max N₁ N₂) + C₂ * powNat x (max N₁ N₂)
          = (C₁ + C₂) * powNat x (max N₁ N₂) := by
        mach_mpoly [C₁, C₂, powNat x (max N₁ N₂)]
      rw [← e]
      exact le_trans htri hsum
  | sub a b iha ihb =>
      intro h hd
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨C₁, N₁, X₁, hC₁, hX₁, h₁⟩ := iha ha hd.1
      obtain ⟨C₂, N₂, X₂, hC₂, hX₂, h₂⟩ := ihb hb hd.2
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds hX₁ hX₂
      refine ⟨C₁ + C₂, max N₁ N₂, X, add_nonneg hC₁ hC₂, hX, fun x hx => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans hX hx
      have hu₁ := h₁ x (le_trans hXa hx)
      have hu₂ := h₂ x (le_trans hXb hx)
      have hm₁ : C₁ * powNat x N₁ ≤ C₁ * powNat x (max N₁ N₂) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_left N₁ N₂)) hC₁
      have hm₂ : C₂ * powNat x N₂ ≤ C₂ * powNat x (max N₁ N₂) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_right N₁ N₂)) hC₂
      have hneg : abs (FTerm.eval a x - FTerm.eval b x)
          ≤ abs (FTerm.eval a x) + abs (FTerm.eval b x) := by
        have e : FTerm.eval a x - FTerm.eval b x = FTerm.eval a x + -(FTerm.eval b x) := by mach_ring
        rw [e]
        have h2 := abs_add (FTerm.eval a x) (-(FTerm.eval b x))
        rw [abs_neg] at h2; exact h2
      have hsum : abs (FTerm.eval a x) + abs (FTerm.eval b x)
          ≤ C₁ * powNat x (max N₁ N₂) + C₂ * powNat x (max N₁ N₂) :=
        add_le_add_wit (le_trans hu₁ hm₁) (le_trans hu₂ hm₂)
      have e : C₁ * powNat x (max N₁ N₂) + C₂ * powNat x (max N₁ N₂)
          = (C₁ + C₂) * powNat x (max N₁ N₂) := by
        mach_mpoly [C₁, C₂, powNat x (max N₁ N₂)]
      rw [← e]
      exact le_trans hneg hsum
  | mul a b iha ihb =>
      intro h hd
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨C₁, N₁, X₁, hC₁, hX₁, h₁⟩ := iha ha hd.1
      obtain ⟨C₂, N₂, X₂, hC₂, hX₂, h₂⟩ := ihb hb hd.2
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds hX₁ hX₂
      refine ⟨C₁ * C₂, N₁ + N₂, X, mul_nonneg hC₁ hC₂, hX, fun x hx => ?_⟩
      have hu₁ := h₁ x (le_trans hXa hx)
      have hu₂ := h₂ x (le_trans hXb hx)
      have s1 : abs (FTerm.eval a x) * abs (FTerm.eval b x)
          ≤ (C₁ * powNat x N₁) * abs (FTerm.eval b x) :=
        mul_le_mul_of_nonneg_right hu₁ (abs_nonneg _)
      have hCp : (0 : Real) ≤ C₁ * powNat x N₁ :=
        mul_nonneg hC₁ (le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)) N₁))
      have s2 : (C₁ * powNat x N₁) * abs (FTerm.eval b x)
          ≤ (C₁ * powNat x N₁) * (C₂ * powNat x N₂) :=
        mul_le_mul_of_nonneg_left hu₂ hCp
      have e : (C₁ * powNat x N₁) * (C₂ * powNat x N₂)
          = C₁ * C₂ * powNat x (N₁ + N₂) := by
        rw [powNat_add]; mach_mpoly [C₁, C₂, powNat x N₁, powNat x N₂]
      show abs (FTerm.eval a x * FTerm.eval b x) ≤ C₁ * C₂ * powNat x (N₁ + N₂)
      rw [abs_mul, ← e]
      exact le_trans s1 s2
  | div a b iha ihb => intro _ hd; exact absurd hd (by simp [divFree])
  | F a iha => intro h _; simp only [fOcc] at h; omega

/-! ## C + D. Exponential escapes every envelope, so `exp` costs a query -/

/-- **No function with a polynomial envelope is `exp`.** The analytic input is `exp_beats_powNat`,
which the corpus already had. -/
theorem polyEnvelope_ne_exp {f : Real → Real} (h : PolyEnvelope f) :
    ¬ (∀ x : Real, f x = exp x) := by
  intro hf
  obtain ⟨C, N, X, hC, hX, hb⟩ := h
  obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_powNat N C (X + C + 1)
  have hXpos : (0 : Real) ≤ X := le_trans (le_of_lt zero_lt_one_ax) hX
  have hxX' : X ≤ x := by
    have e : X + C + 1 = X + (C + 1) := by mach_ring
    have h1 : X ≤ X + C + 1 := by
      rw [e]; exact le_add_nonneg (add_nonneg hC (le_of_lt zero_lt_one_ax))
    exact le_trans h1 hxX
  have hCx' : C ≤ x := by
    have e : X + C + 1 = C + (X + 1) := by mach_ring
    have h1 : C ≤ X + C + 1 := by
      rw [e]; exact le_add_nonneg (add_nonneg hXpos (le_of_lt zero_lt_one_ax))
    exact le_trans h1 hxX
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hbound := hb x hxX'
  rw [hf x] at hbound
  have hCx : C ≤ x * x := by
    have h3 : x ≤ x * x := by
      have v := mul_le_mul_of_nonneg_left hx1 hx0
      have e : x * 1 = x := by mach_ring
      rw [e] at v; exact v
    exact le_trans hCx' h3
  have hpn : (0 : Real) ≤ powNat x N :=
    le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1) N)
  have hstep : C * powNat x N ≤ powNat x (N + 2) := by
    have v := mul_le_mul_of_nonneg_right hCx hpn
    have e : x * x * powNat x N = powNat x (N + 2) := by
      rw [powNat_add]
      show x * x * powNat x N = powNat x N * (x * (x * 1))
      mach_mpoly [x, powNat x N]
    rw [e] at v; exact v
  have hchain : abs (exp x) < exp x := by
    have hle : powNat x (N + 2) ≤ powNat x (N + 2) + x + C := by
      have e : powNat x (N + 2) + x + C = powNat x (N + 2) + (x + C) := by mach_ring
      rw [e]; exact le_add_nonneg (add_nonneg hx0 hC)
    exact lt_of_le_of_lt (le_trans hbound (le_trans hstep hle)) hlt
  have hself : exp x ≤ abs (exp x) := le_abs_self _
  exact absurd (lt_of_le_of_lt hself hchain) (lt_irrefl_ax _)

/-- **`exp` costs at least one `F`-query** — division-free case. `FQueryLowerBound` for `divFree`
terms. -/
theorem fOcc_pos_of_eq_exp {T : FTerm} (hd : divFree T) (h : ∀ x : Real, FTerm.eval T x = exp x) :
    1 ≤ fOcc T := by
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exact absurd h (polyEnvelope_ne_exp (polyEnvelope_of_zero_query T h0 hd))
  · exact hp

/-! ## E. The barrier is not about polynomial *syntax*

A specimen with nested products and differences — nothing polynomial-looking about the term, and it
still falls under the envelope. -/

/-- `((x·x − x)·(x·x) + x) − 7`, as an `L_F` term. -/
noncomputable def nastyTerm : FTerm :=
  FTerm.sub (FTerm.add (FTerm.mul (FTerm.sub (FTerm.mul FTerm.var FTerm.var) FTerm.var)
    (FTerm.mul FTerm.var FTerm.var)) FTerm.var) (FTerm.const (1 + 1 + 1 + 1 + 1 + 1 + 1))

theorem nastyTerm_envelope : PolyEnvelope (FTerm.eval nastyTerm) :=
  polyEnvelope_of_zero_query nastyTerm rfl (by simp only [nastyTerm, divFree]; trivial)

/-- And therefore it is not `exp`, with no case analysis on its shape. -/
theorem nastyTerm_ne_exp : ¬ (∀ x : Real, FTerm.eval nastyTerm x = exp x) :=
  polyEnvelope_ne_exp nastyTerm_envelope

/-- **Named obligation, discharged**: the division-free case of `FQueryLowerBound`. Split from the
general row because the obligation gate — correctly — refused to accept a theorem with an extra
hypothesis as a discharger of the unrestricted statement. -/
def FQueryLowerBoundDivFree : Prop :=
  ∀ T : FTerm, divFree T → (∀ x : Real, FTerm.eval T x = exp x) → 1 ≤ fOcc T

theorem fQueryLowerBoundDivFree_holds : FQueryLowerBoundDivFree :=
  fun _ hd h => fOcc_pos_of_eq_exp hd h

/-! ## What remains: cancellation under addition

`FQueryLowerBound` is now discharged for division-free terms. The general case needs the envelope for
`÷`, which needs a two-sided invariant, which is not closed under `+`. The refined obligation is
therefore not "handle division" but:

```
RatGermSum : the order of a sum of two rational germs at +∞ is determined by
             a Laurent normal form, with descent through cancelling leading terms
```

which is the same obstruction shape — *cancellation* — that gates `SignHardCase` and the EML depth
program. Recorded rather than attempted. -/

end MachLib
