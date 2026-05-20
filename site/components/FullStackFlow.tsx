type Step = { num: string; text: string; sub?: string; highlight?: boolean };

// MachLib's framing of the same flow puts the spotlight on steps 03–04
// (where MachLib enters the chain). The accent rows are the "this is us"
// moments.
const STEPS: Step[] = [
  {
    num: "01",
    text: "Engineer writes equation (.eml)",
    sub: "Domain expert, single source of truth, no toolchain leaks.",
  },
  {
    num: "02",
    text: "Forge compiles to 9 targets",
    sub: "C, Rust, Python, LLVM, wasm, Lean, Verilog, VHDL, Chisel.",
  },
  {
    num: "03",
    text: "Lean output targets MachLib surfaces",
    sub: "Zero-Mathlib gate status is recorded with the release snapshot.",
    highlight: true,
  },
  {
    num: "04",
    text: "MachLib build status is snapshot-specific",
    sub: "Counts and timing should be read from the release manifest.",
    highlight: true,
  },
  {
    num: "05",
    text: "Lean-check status recorded per artifact",
    sub: "Verification metadata is scoped to the artifacts present in the release.",
  },
];

export default function FullStackFlow() {
  return (
    <section id="how-it-works">
      <div className="container">
        <div className="eyebrow">// how it works</div>
        <h2>The full chain — equation to proof.</h2>
        <p className="section-lede">
          MachLib is a local formal-library surface in a larger toolchain. It
          can work on its own, and stack integrations are reviewed separately.
          The zero-Mathlib release gate remains in progress.
          Here&apos;s the candidate path a single equation can take.
        </p>

        <div className="flow">
          {STEPS.map((step, i) => (
            <div key={step.num}>
              <div className={`flow-step${step.highlight ? " highlight" : ""}`}>
                <span className="flow-num">{step.num}</span>
                <span className="flow-text">
                  {step.text}
                  {step.sub ? <em>{step.sub}</em> : null}
                </span>
              </div>
              {i < STEPS.length - 1 ? (
                <div className="flow-arrow" aria-hidden>
                  ↓
                </div>
              ) : null}
            </div>
          ))}
        </div>

        <p className="flow-coda">
          Review every line from <strong>equation</strong> to{" "}
          <strong>generated artifact</strong> to <strong>Lean-check status</strong>.
          <br />
          No upload, public release, or marketplace action is implied here.
        </p>
      </div>
    </section>
  );
}
