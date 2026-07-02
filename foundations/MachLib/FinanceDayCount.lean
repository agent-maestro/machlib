import MachLib.Basic

/-!
# Verified day-count & accrual — coupon periods compose exactly (30E/360)

The second finance kernel, same discipline as `FinanceAmortization`: a machine-checked certificate for
a property a bond desk and an auditor argue about — **does splitting a coupon period at an intermediate
date preserve the accrued interest?** It must: no interest may be manufactured or lost by choosing a
different accrual boundary.

We use the **30E/360 (Eurobond)** day-count convention. Under it every date `(y, m, d)` maps to a single
serial index `360·y + 30·m + min(d, 30)` (every month is 30 days, the day-of-month clamped to 30), and
the day-count between two dates is the difference of their serials. That single-serial structure is
exactly what makes 30E/360 **additive** — and it's the day-count analogue of amortization's telescoping
reconciliation. (The US 30/360 "bond basis" convention is **not** additive: its end-of-month rule
depends on the *other* endpoint, so the same intermediate date is counted differently as a period-end
than as a period-start. Choosing 30E/360 is a real, deliberate correctness decision, not an accident.)

All results are Mathlib-free, pure `Int` (`omega`): money and calendars are exact integer objects, and
none of this touches a float.

* `days30E360_additive` — **the headline.** For any intermediate date, the day-counts over the two
  sub-periods sum to the whole: `days(A,B) + days(B,C) = days(A,C)`.
* `accrual_additive` — the money corollary: accrued interest (`notional · rateNum · days`) composes
  exactly across a split, because it is linear in an additive day-count.
* `days30E360_months` — **regularity.** Two dates the same day-of-month and `m` whole months apart are
  exactly `30·m` days: equal calendar spacing ⇒ equal day-count ⇒ equal accrual (fair coupons).
* `days30E360_full_year` — a year is exactly 360 days (the reason the convention exists).
* `days30E360_nonneg` — a forward period never has a negative day-count.
-/

namespace MachLib.Finance

/-- 30E/360 (Eurobond) serial day index of a date `(y, m, d)`: every month is 30 days and the
day-of-month is clamped to 30. Each date has ONE serial, independent of any counterparty date — this is
what makes the convention additive. -/
def serial30E360 (y m d : Int) : Int := 360 * y + 30 * m + (if d ≤ 30 then d else 30)

/-- 30E/360 day-count between two dates: the difference of their serials. -/
def days30E360 (y1 m1 d1 y2 m2 d2 : Int) : Int :=
  serial30E360 y2 m2 d2 - serial30E360 y1 m1 d1

/-- **Additivity — a coupon period splits without creating or destroying days.** For ANY intermediate
date `(y2,m2,d2)`, `days(A,B) + days(B,C) = days(A,C)`. The day-count analogue of amortization's
telescoping reconciliation: interest cannot be manufactured by moving the accrual boundary. Holds
because each date has a single serial; the US 30/360 convention does NOT satisfy this. -/
theorem days30E360_additive (y1 m1 d1 y2 m2 d2 y3 m3 d3 : Int) :
    days30E360 y1 m1 d1 y2 m2 d2 + days30E360 y2 m2 d2 y3 m3 d3
      = days30E360 y1 m1 d1 y3 m3 d3 := by
  unfold days30E360; omega

/-- **Regularity.** Two dates on the same day-of-month, `m` whole months apart, are exactly `30·m`
days: `days = 30·(12·ΔY + ΔM)`. Equal calendar spacing gives equal day-count, hence equal accrual —
the property that makes 30/360 useful for level coupon periods. -/
theorem days30E360_months (y1 m1 y2 m2 d : Int) :
    days30E360 y1 m1 d y2 m2 d = 30 * (12 * (y2 - y1) + (m2 - m1)) := by
  unfold days30E360 serial30E360; omega

/-- A full year is exactly 360 days. -/
theorem days30E360_full_year (y m d : Int) :
    days30E360 y m d (y + 1) m d = 360 := by
  unfold days30E360 serial30E360; omega

/-- A forward period (later date serially ≥ earlier) never has a negative day-count. -/
theorem days30E360_nonneg (y1 m1 d1 y2 m2 d2 : Int)
    (h : serial30E360 y1 m1 d1 ≤ serial30E360 y2 m2 d2) :
    0 ≤ days30E360 y1 m1 d1 y2 m2 d2 := by
  unfold days30E360; omega

/-- Accrued-interest numerator over a period: `notional · rateNum · days` (kept as an exact integer;
divide by `rateDen · 360` at the boundary). Linear in the day-count. -/
def accrualNumer (notional rateNum : Int) (y1 m1 d1 y2 m2 d2 : Int) : Int :=
  notional * rateNum * days30E360 y1 m1 d1 y2 m2 d2

/-- **Accrued interest composes exactly across a split coupon period.** The money corollary of
`days30E360_additive`: because accrual is linear in an additive day-count, the accrued interest over
`[A,B]` plus that over `[B,C]` equals the accrued interest over `[A,C]` — exactly, for any notional and
rate. -/
theorem accrual_additive (notional rateNum : Int)
    (y1 m1 d1 y2 m2 d2 y3 m3 d3 : Int) :
    accrualNumer notional rateNum y1 m1 d1 y2 m2 d2
      + accrualNumer notional rateNum y2 m2 d2 y3 m3 d3
      = accrualNumer notional rateNum y1 m1 d1 y3 m3 d3 := by
  unfold accrualNumer
  rw [← days30E360_additive y1 m1 d1 y2 m2 d2 y3 m3 d3, Int.mul_add]

end MachLib.Finance
