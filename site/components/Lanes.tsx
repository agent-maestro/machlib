type Result = { name: string; text: string };

const NUMERICS: Result[] = [
  {
    name: "fxaffine_traj_tracks_exact",
    text:
      "The bit-level fixed-point datapath of the affine plant kernel tracks the exact real " +
      "trajectory within ulp · geom c n, with the per-step error derived from the bits. This is " +
      "the end-to-end result. The same composition for the PID controller path is not yet " +
      "proved; its two halves exist and the bridge between them is prose.",
  },
  {
    name: "cross_target",
    text:
      "Two evaluations of one exact value at different precisions agree within their " +
      "forward-error bounds.",
  },
  {
    name: "kalman_update_1d_fwd_error",
    text:
      "A proven Q16.16 forward-error bound for the scalar Kalman update that ran on an Arty A7 " +
      "and is the datapath of the second chip.",
  },
  {
    name: "nonlinear_drift_clamp_safe",
    text:
      "A saturating guard keeps a plant's state inside a safe envelope for all time, under any " +
      "controller signal and bounded disturbance.",
  },
  {
    name: "intModel",
    text:
      "The flagship closure's axioms have an external ℤ-model, so those results are not vacuous. " +
      "A gate fails if the model ever becomes circular.",
  },
];

const LANGUAGE: Result[] = [
  {
    name: "chain2_khovanskii_bound_explicit",
    text:
      "A Khovanskii zero bound for depth-2 double-exponential chains (x, eˣ, e^{eˣ}) with the " +
      "reducibility witness constructed, in an explicit numeric form usable as a tool.",
  },
  {
    name: "invX4_depth_optimal",
    text:
      "The reciprocal is an EML tree on x > 0, and depth 4 is optimal — certified by a " +
      "lower-bound theorem, not by a search.",
  },
  {
    name: "x_plus_neg_c_depth_exact_four",
    text: "Translation by a constant costs depth exactly 4, both bounds proved.",
  },
  {
    name: "sign_query_cost_bounds_tight",
    text:
      "The query-complexity lane: log is not a rational germ on any interval, and the sign " +
      "function costs between 1 and 12 queries.",
  },
  {
    name: "depth3ApproachBelow_holds",
    text:
      "The depth-3 constant-gap statement is false (a witness refutes it), and its " +
      "decaying-floor replacement is proved: a depth-≤3 tree that dips below a constant does so " +
      "by at least exp(−C − exp(exp x)).",
  },
];

function Card({ title, sub, items }: { title: string; sub: string; items: Result[] }) {
  return (
    <div className="compare-card good">
      <h3>{title}</h3>
      <p style={{ marginTop: 0 }}>{sub}</p>
      <ul>
        {items.map((r) => (
          <li key={r.name}>
            <code>{r.name}</code> — {r.text}
          </li>
        ))}
      </ul>
    </div>
  );
}

export default function Lanes() {
  return (
    <section id="lanes">
      <div className="container">
        <div className="eyebrow">// two lanes</div>
        <h2>What it proves.</h2>
        <p className="section-lede">
          Everything named here is free of <code>sorry</code> and of any
          classical Khovanskii axiom; <code>#print axioms</code> confirms it.
          The general-depth Khovanskii bound is still cited, not proved, and is
          kept out of every featured result.
        </p>

        <div className="compare">
          <Card
            title="Verified numerics"
            sub="From bits toward trajectories, for the kernels Forge emits."
            items={NUMERICS}
          />
          <Card
            title="The EML language itself"
            sub="What finite exp/log depth can express, and how tame it is."
            items={LANGUAGE}
          />
        </div>
      </div>
    </section>
  );
}
