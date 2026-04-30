const MATHLIB: string[] = [
  "45 minute cold build",
  "≈500,000 lines of dependencies",
  "No chain-order annotations",
  "No difficulty lanes",
  "No tactic trace, no failure data",
  "No common-mistake corpus",
  "Built for human mathematicians",
];

const MACHLIB: string[] = [
  "4.77 second cold build",
  "491 lines of foundations, axiomatic ℝ",
  "Chain-order annotations on every record",
  "6 difficulty lanes (foundations → open problems)",
  "Tactic trace + success rate per tactic",
  "Common-mistake corpus per theorem",
  "Built for machines and the agents that train on them",
];

export default function WhyMachLib() {
  return (
    <section id="why">
      <div className="container">
        <div className="eyebrow">// why machlib</div>
        <h2>Why a separate library?</h2>
        <p className="section-lede">
          Mathlib is a monumental human achievement. It was not built for
          agents — it&apos;s slow to import, sparse on metadata, and silent
          about the proofs that didn&apos;t work. MachLib is the opposite of
          that, on purpose.
        </p>

        <div className="compare">
          <div className="compare-card bad">
            <h3>Mathlib import</h3>
            <ul>
              {MATHLIB.map((t) => (
                <li key={t}>{t}</li>
              ))}
            </ul>
          </div>
          <div className="compare-card good">
            <h3>MachLib import</h3>
            <ul>
              {MACHLIB.map((t) => (
                <li key={t}>{t}</li>
              ))}
            </ul>
          </div>
        </div>
      </div>
    </section>
  );
}
