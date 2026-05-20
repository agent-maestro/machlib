const MACHLIB = {
  records: "By release manifest",
  tests: "By release manifest",
  build_label: "Snapshot-specific",
  mathlib_imports: "Gate-backed zero",
} as const;

const TILES: { value: string; label: string }[] = [
  { value: MACHLIB.records, label: "Records" },
  { value: MACHLIB.tests, label: "Tests" },
  { value: MACHLIB.build_label, label: "Cold Build" },
  { value: MACHLIB.mathlib_imports, label: "Mathlib Imports" },
];

export default function Numbers() {
  return (
    <section id="numbers">
      <div className="container">
        <div className="eyebrow">// the numbers</div>
        <h2>What MachLib is, in four numbers.</h2>
        <p className="section-lede">
          Counts and build timing are tied to release snapshots. The
          zero-Mathlib dependency gate must pass for every release that claims
          it.
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
