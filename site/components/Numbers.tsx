const MACHLIB = {
  records: "By release manifest",
  tests: "By release manifest",
  build_label: "Snapshot-specific",
  mathlib_imports: "Gate in progress",
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
          Counts, build timing, and zero-Mathlib gate status are tied to
          release snapshots. See the release manifest for current record and
          test totals.
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
