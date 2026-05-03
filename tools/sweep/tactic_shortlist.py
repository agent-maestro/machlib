"""MachLib-tailored tactic vocabulary for the BFS proof sweep (C-239).

The default :data:`gym.tactics.TACTIC_VOCABULARY` is Mathlib-flavored
(``linarith``, ``nlinarith``, ``positivity``, ``field_simp``, …).
MachLib's foundations have ZERO Mathlib dependency by design, so those
tactics are not in scope; running them produces only expensive
negatives. Instead we use a small, curated shortlist drawn from the
lemmas actually re-exported by ``MachLib.Forge`` (see
``foundations/MachLib/Forge.lean``: ``exp_nonneg``, ``add_nonneg``,
``mul_nonneg``, ``nonneg_of_pos``, ``le_refl``, ``le_of_lt``,
``le_trans``, etc.).

Order matters for BFS — cheaper / higher-yield first. The depth-1
sweep tries each one in turn and stops at the first closure.
"""
from __future__ import annotations


# ── Tier-1 vocabulary (depth 1 sweep) ─────────────────────────────

#: 14 tactics chosen for the typical Discovered/ goal shapes:
#: ``f x ≥ 0`` (positivity) and ``f x ≥ -1`` (lower bound).
TIER1_TACTICS: tuple[str, ...] = (
    # ── single-tactic closes ──
    "exact exp_nonneg _",
    "exact le_refl _",
    "exact nonneg_of_pos (by assumption)",
    "rfl",
    "trivial",
    "simp",
    # ── apply with assumption hyp closure ──
    "apply add_nonneg <;> assumption",
    "apply mul_nonneg <;> assumption",
    "apply add_nonneg <;> exact exp_nonneg _",
    "apply le_trans (exp_nonneg _) (le_refl _)",
    # ── definitional simp sets ──
    "simp only [exp_log, log_exp]",
    "simp [exp_nonneg]",
    # ── intro + apply for forall-shaped subgoals ──
    "intro <;> apply nonneg_of_pos <;> assumption",
    # ── catch-all ──
    "assumption",
    # ── tanh lower-bound chain (post-C-239 literal fix) ──
    "exact le_of_lt (neg_one_lt_tanh _)",
    "exact le_of_lt (one_pos)",
    "exact sqrt_nonneg _",
)


# ── Tier-2 vocabulary (depth-1 + depth-2 sweep) ───────────────────

#: Tier-2 extends Tier-1 with the C-239 follow-up additions:
#: `exp_pos`/`tanh_lt_one` (strict-inequality chains), the new
#: `Forge.lean` min/max combinators, and a few compound `<;>`
#: shapes that close common multi-factor product / clamp idioms
#: in a single tactic invocation. Used for the depth-2 sweep
#: against the 212 theorems Tier-1 left open.
TIER2_TACTICS: tuple[str, ...] = TIER1_TACTICS + (
    # ── strict positivity (closes `0 < exp _` cases) ──
    "exact exp_pos _",
    # ── tanh upper bound ──
    "exact le_of_lt (tanh_lt_one _)",
    # ── min/max directional bounds (Forge.lean extensions) ──
    "exact le_max_left _ _",
    "exact le_max_right _ _",
    "exact min_le_left _ _",
    "exact min_le_right _ _",
    # ── min/max nonneg specialisations ──
    "apply min_nonneg <;> assumption",
    "apply max_nonneg_left <;> assumption",
    "apply max_nonneg_right <;> assumption",
    # ── `0 ≤ max <anything> 0` (very common codegen clamp idiom) ──
    "exact max_nonneg_right (le_refl _)",
    # ── product-of-products positivity for 3-way and 4-way chains ──
    "apply mul_nonneg <;> (apply mul_nonneg <;> assumption)",
    "apply mul_nonneg <;> exact sqrt_nonneg _",
    "apply mul_nonneg (exp_nonneg _) (sqrt_nonneg _)",
    # ── mixed-strictness sum ──
    "apply add_pos_of_nonneg_pos <;> assumption",
    # ── nonneg of strict-pos lemma applied through le_of_lt ──
    "exact le_of_lt (exp_pos _)",
)


# ── Tier-3 vocabulary (literal-positivity, C-240) ────────────────

#: Tier-3 extends Tier-2 with the C-240 `lit_pos` macro and a small
#: set of compound shapes that lift literal positivity through the
#: pre-existing `mul_nonneg` / `add_pos_of_nonneg_pos` combinators.
#: Used for the BFS sweep on the 209 theorems Tier-2 left open.
#: Goal: pick up codegen idioms of the form
#:   `0 ≤ <literal> * <var-pos>` and `0 < <literal> + <var-pos>`
#: that need both a literal-positivity step AND a structural
#: combinator in the same tactic.
TIER3_TACTICS: tuple[str, ...] = TIER2_TACTICS + (
    # ── direct literal positivity (C-240) ──
    "lit_pos",
    "exact ofScientific_pos _ (by decide)",
    "exact ofScientific_nonneg _ (by decide)",
    # ── literal × var product (closes `0 ≤ LIT * x` when `0 ≤ x` is hyp) ──
    "apply mul_nonneg <;> first | assumption | lit_pos",
    "apply mul_nonneg <;> first | exact exp_nonneg _ | lit_pos",
    "apply mul_nonneg <;> first | exact sqrt_nonneg _ | lit_pos",
    # ── literal + var-pos sum ──
    "apply add_pos_of_nonneg_pos <;> first | assumption | lit_pos",
    "apply add_nonneg <;> first | assumption | lit_pos",
)


# ── Tier-0 sample selection (10 theorems for the dry run) ────────

#: Hand-picked diverse sample. Format: (file_basename, theorem_name).
#: Picked across positivity / lower_bound / "other" buckets, biased
#: toward simpler shapes the Tier-1 vocab has a chance against.
TIER0_SAMPLE: tuple[tuple[str, str], ...] = (
    # exp-based positivity (3)
    ("abrams_strength.lean",        "abrams_strength_decreases_with_wc"),
    ("vega.lean",                   "bs_vega_non_negative"),
    ("voigt.lean",                  "voigt_peak_at_centre"),
    # other simple positivity (3)
    ("svpwm.lean",                  "phase_duty_in_unit_interval"),
    ("svpwm.lean",                  "modulation_index_nonneg"),
    ("tool_wear_taylor.lean",       "tool_life_decreases_with_speed"),
    # lower_bound -1 (2)
    ("tanh.lean",                   "hard_tanh_bounded"),
    ("tanh.lean",                   "tanh_monotone_in_x"),
    # "other" with strict > 0 (2)
    ("vant_hoff.lean",              "vant_hoff_predict_k"),
    ("var_monte_carlo.lean",        "parametric_var_monotone_in_sigma"),
)
