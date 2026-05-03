// Single source of truth for the marketing tiles. Update these
// values, not the JSX below. `live_counts.py` (in the forge repo)
// is the authority -- run it to read the live derivation:
//
//   python tools/cli/live_counts.py --pretty --slow
//
// Then bump any field whose value moved.
const MACHLIB = {
  records: 3316,
  tests: 2704,
  build_label: "<5 min",
  mathlib_imports: 0,
} as const;

const TILES: { value: string; label: string }[] = [
  { value: MACHLIB.records.toString(),                  label: "Records" },
  { value: MACHLIB.tests.toLocaleString("en-US"),       label: "Tests" },
  { value: MACHLIB.build_label,                         label: "Cold Build" },
  { value: MACHLIB.mathlib_imports.toString(),          label: "Mathlib Imports" },
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
