import MachLib.PevSignGerm

/-!
# The shape of a bounded rational germ — decay or a nonzero floor

`NEXT.md` says the first move at level 1 is a **classification, not a transcendence theorem**, and
this is it. The signed trichotomy removed the unbounded regime, so what remains is `S` bounded — and
"bounded" understates the structure. Classically a nonconstant bounded rational germ has a finite
limit `a`, and `S − a ∼ c·x^{−m}`; the two cases that matter for `F ∘ S` are `a = 0` and `a ≠ 0`,
because totalisation treats them differently.

**This corpus has no limits**, and does not need them. The same split is visible in the degrees, and
`pev_leading_form` already exposes those:

| degrees | classical | stated here, limit-free |
| --- | --- | --- |
| `d_P < d_Q` | `S → 0` | `x·\|S x\| ≤ K` — decays at least like `1/x` |
| `d_P = d_Q` | `S → a ≠ 0` | `c ≤ \|S x\|` — a **nonzero floor** |
| `d_P > d_Q` | unbounded | already handled: `c·x ≤ \|S x\|` |

Saying "`S → 0`" as "`x·|S x|` is bounded" is not a workaround. It is the same content in the idiom
the corpus can state, and it is *stronger* than convergence to `0` — it names the rate.

Combined with `ratGerm_eventual_sign` this is the full split `NEXT.md` asks for: a decaying germ with
a sign, or a germ with a nonzero floor and a sign — the latter being the `a < 0` / `a > 0` cases
where `F(S) = exp(S)` and `F(S) = exp(S) + log(S)` respectively.
-/

namespace MachLib

open Real

private theorem mul_div_assoc' (a b c : Real) (hc : c ≠ 0) : a * (b / c) = (a * b) / c := by
  rw [div_def b c hc, div_def (a * b) c hc]
  mach_mpoly [a, b, (1 : Real) / c]

/-- **The shape of a rational germ.** It dies, or it decays at least like `1/x`, or it has a nonzero
floor. The last case includes the unbounded germs; combined with `RatGermSignedTrichotomy` it is the
`a ≠ 0` branch of the classification. -/
theorem ratGerm_shape {f : Real → Real} (h : RatGerm f) :
    EvZeroF f
    ∨ (∃ K X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → x * abs (f x) ≤ K)
    ∨ (∃ c X : Real, 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → c ≤ abs (f x)) := by
  obtain ⟨P, Q, X₀, hX₀, hQ0, he⟩ := h
  rcases pev_leading_form Q with ⟨Z, hZ, hzq⟩ | ⟨cQ, CQ, dQ, XQ, hcQ, hXQ, hbQ⟩
  · exfalso
    obtain ⟨W, _, hW0, hWZ⟩ := two_bounds' hX₀ hZ
    exact hQ0 W hW0 (hzq W hWZ)
  rcases pev_leading_form P with ⟨Z, hZ, hzp⟩ | ⟨cP, CP, dP, XP, hcP, hXP, hbP⟩
  · refine Or.inl ?_
    obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hX₀ hZ
    refine ⟨W, hW, fun x hx => ?_⟩
    rw [he x (le_trans hWa hx), hzp x (le_trans hWb hx),
        zero_div_eq (hQ0 x (le_trans hWa hx))]
  obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
  obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
  have hbase : ∀ x : Real, W ≤ x →
      abs (f x) = abs (pev P x) / abs (pev Q x) ∧ (0 : Real) < abs (pev Q x)
      ∧ (cP * powNat x dP ≤ abs (pev P x) ∧ abs (pev P x) ≤ CP * powNat x dP)
      ∧ (cQ * powNat x dQ ≤ abs (pev Q x) ∧ abs (pev Q x) ≤ CQ * powNat x dQ) := by
    intro x hx
    have hx0 : X₀ ≤ x := le_trans (le_trans hW₁a hWW₁) hx
    have hqne : pev Q x ≠ 0 := hQ0 x hx0
    exact ⟨by rw [he x hx0]; exact abs_div_eq hqne, abs_pos_of_ne hqne,
           hbP x (le_trans hWP hx), hbQ x (le_trans (le_trans hW₁b hWW₁) hx)⟩
  have hposP : (0 : Real) < CP := by
    obtain ⟨_, _, ⟨hlo, hhi⟩, _⟩ := hbase W (le_refl W)
    have hp : (0 : Real) < powNat W dP := powNat_pos (lt_of_lt_of_le zero_lt_one_ax hW) dP
    refine lt_of_lt_of_le hcP (le_of_mul_le_mul_left' hp ?_)
    have e1 : powNat W dP * cP = cP * powNat W dP := by mach_mpoly [cP, powNat W dP]
    have e2 : powNat W dP * CP = CP * powNat W dP := by mach_mpoly [CP, powNat W dP]
    rw [e1, e2]; exact le_trans hlo hhi
  have hposQ : (0 : Real) < CQ := by
    obtain ⟨_, _, _, ⟨hlo, hhi⟩⟩ := hbase W (le_refl W)
    have hp : (0 : Real) < powNat W dQ := powNat_pos (lt_of_lt_of_le zero_lt_one_ax hW) dQ
    refine lt_of_lt_of_le hcQ (le_of_mul_le_mul_left' hp ?_)
    have e1 : powNat W dQ * cQ = cQ * powNat W dQ := by mach_mpoly [cQ, powNat W dQ]
    have e2 : powNat W dQ * CQ = CQ * powNat W dQ := by mach_mpoly [CQ, powNat W dQ]
    rw [e1, e2]; exact le_trans hlo hhi
  rcases Nat.lt_or_ge dP dQ with hlt | hge
  · -- numerator degree strictly smaller: DECAY, at rate 1/x
    refine Or.inr (Or.inl ⟨CP / cQ, W, hW, fun x hx => ?_⟩)
    obtain ⟨hfx, hqpos, ⟨_, hPhi⟩, ⟨hQlo, _⟩⟩ := hbase x hx
    have hx1 : (1 : Real) ≤ x := le_trans hW hx
    have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
    rw [hfx, mul_div_assoc' x (abs (pev P x)) (abs (pev Q x)) (ne_of_gt hqpos)]
    refine div_le_of_le_mul hqpos ?_
    have s1 : x * abs (pev P x) ≤ CP * powNat x (dP + 1) := by
      have v := mul_le_mul_of_nonneg_left hPhi hx0
      have e : x * (CP * powNat x dP) = CP * powNat x (dP + 1) := by
        show x * (CP * powNat x dP) = CP * (x * powNat x dP)
        mach_mpoly [x, CP, powNat x dP]
      rw [e] at v; exact v
    have s2 : CP * powNat x (dP + 1) ≤ CP * powNat x dQ :=
      mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 hlt) (le_of_lt hposP)
    have s3 : CP * powNat x dQ ≤ CP / cQ * (cQ * powNat x dQ) := by
      have e : CP / cQ * (cQ * powNat x dQ) = (CP / cQ * cQ) * powNat x dQ := by
        mach_mpoly [CP / cQ, cQ, powNat x dQ]
      rw [e, div_mul_self' (ne_of_gt hcQ)]
      exact le_refl _
    exact le_trans (le_trans (le_trans s1 s2) s3)
      (mul_le_mul_of_nonneg_left hQlo (le_of_lt (div_pos' hposP hcQ)))
  · -- degrees equal or numerator larger: a NONZERO FLOOR
    refine Or.inr (Or.inr ⟨cP / CQ, W, div_pos' hcP hposQ, hW, fun x hx => ?_⟩)
    obtain ⟨hfx, hqpos, ⟨hPlo, _⟩, ⟨_, hQhi⟩⟩ := hbase x hx
    have hx1 : (1 : Real) ≤ x := le_trans hW hx
    rw [hfx]
    refine div_ge_of_mul_le hqpos ?_
    have s1 : cP / CQ * (CQ * powNat x dQ) = cP * powNat x dQ := by
      have e : cP / CQ * (CQ * powNat x dQ) = (cP / CQ * CQ) * powNat x dQ := by
        mach_mpoly [cP / CQ, CQ, powNat x dQ]
      rw [e, div_mul_self' (ne_of_gt hposQ)]
    have s2 : cP * powNat x dQ ≤ cP * powNat x dP :=
      mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 hge) (le_of_lt hcP)
    refine le_trans (mul_le_mul_of_nonneg_left hQhi (le_of_lt (div_pos' hcP hposQ))) ?_
    rw [s1]
    exact le_trans s2 hPlo

/-! ## The bounded case, which is the one `F ∘ S` still needs -/

/-- **A bounded rational germ either decays like `1/x` or has a nonzero floor.**

This is the `a = 0` versus `a ≠ 0` split of the classical picture, stated without limits. The two
branches are what `F ∘ S` must be attacked on separately, because totalisation treats them
differently: with a nonzero floor and `ratGerm_eventual_sign`, `S` is eventually of one sign and
bounded away from `0`, so `F(S) = exp(S)` when that sign is negative and `exp(S) + log(S)` when it is
positive — no branch ambiguity either way. In the decaying branch the sign still decides, but `log S`
now carries an explicit logarithmic scale, since `S ∼ c·x^{−m}` forces `log S` to grow like
`−m·log x`.

Nothing here is a transcendence result, and that is the point: the classification comes first. -/
theorem boundedRatGerm_shape {f : Real → Real} (h : RatGerm f)
    (hbd : ∃ K X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → abs (f x) ≤ K) :
    EvZeroF f
    ∨ (∃ K X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → x * abs (f x) ≤ K)
    ∨ (∃ c K X : Real, 0 < c ∧ 1 ≤ X ∧
        ∀ x : Real, X ≤ x → c ≤ abs (f x) ∧ abs (f x) ≤ K) := by
  obtain ⟨K, XK, hXK, hK⟩ := hbd
  rcases ratGerm_shape h with hz | hdecay | ⟨c, Xc, hc, hXc, hfloor⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl hdecay)
  · obtain ⟨W, hW, hWc, hWK⟩ := two_bounds' hXc hXK
    exact Or.inr (Or.inr ⟨c, K, W, hc, hW,
      fun x hx => ⟨hfloor x (le_trans hWc hx), hK x (le_trans hWK hx)⟩⟩)

end MachLib
