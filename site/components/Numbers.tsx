const TILES: { value: string; label: string }[] = [
  { value: "449",   label: "Records" },
  { value: "2,704", label: "Tests" },
  { value: "4.77s", label: "Cold Build" },
  { value: "0",     label: "Mathlib Imports" },
];

export default function Numbers() {
  return (
    <section id="numbers">
      <div className="container">
        <div className="eyebrow">// the numbers</div>
        <h2>What MachLib is, in four numbers.</h2>
        <p className="section-lede">
          A small, fast, fully-typed corpus that an agent can clone, build,
          and search end-to-end on a laptop. No Mathlib, no surprises.
        </p>

        <div className="numbers">
          {TILES.map((t) => (
            <div className="tile" key={t.label}>
              <div className="value">{t.value}</div>
              <div className="label">{t.label}</div>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}
