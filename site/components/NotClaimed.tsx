const NOT_CLAIMED: string[] = [
  "No claim about physical silicon beyond the reproduction package and the bench evidence it cites. A theorem about a datapath is a theorem about the datapath.",
  "No compiler-correctness claim for Forge. The certifier binds a proof to a kernel by hash; it does not verify code generation.",
  "The analytic base is axiomatised, not constructed. Every axiom is listed and modeled; none is proved here.",
  "The end-to-end composition from bits to a closed-loop trajectory is proved for the affine plant kernel, not yet for the PID controller path.",
  "The research lane on the EML language is the work of one author: kernel-checked, not yet externally reviewed.",
  "Counts are snapshots. Re-run the command before quoting one.",
];

export default function NotClaimed() {
  return (
    <section id="not-claimed">
      <div className="container">
        <div className="eyebrow">// what this does not claim</div>
        <h2>The seams, named.</h2>

        <div className="philosophy">
          <div>
            <ul>
              {NOT_CLAIMED.map((t) => (
                <li key={t}>{t}</li>
              ))}
            </ul>
          </div>
          <div className="philosophy-quote">
            <p>
              A partial result is committed by naming what it lacks. An open
              question is a proposition a theorem may consume and nothing may
              conclude, tracked in a ledger that fails the build in both
              directions: when a row says open after the corpus closed it,
              and when a row says discharged by a theorem that does not
              conclude it.
            </p>
            <p>
              Every instrument here must be shown capable of both verdicts
              before either is read. A check that cannot fail is not a check.
            </p>
          </div>
        </div>
      </div>
    </section>
  );
}
