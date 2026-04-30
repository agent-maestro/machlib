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
    text: "Lean output imports MachLib (not Mathlib)",
    sub: "import MachLib.EML, MachLib.Trig — that's it.",
    highlight: true,
  },
  {
    num: "04",
    text: "MachLib builds in 4.77 seconds",
    sub: "~500 lines of axiomatic foundations. Cold build. Laptop. Every time.",
    highlight: true,
  },
  {
    num: "05",
    text: "Proof verified. Zero external dependencies.",
    sub: "Lean kernel says yes. Nothing else needed.",
  },
];

export default function FullStackFlow() {
  return (
    <section id="how-it-works">
      <div className="container">
        <div className="eyebrow">// how it works</div>
        <h2>The full chain — equation to proof.</h2>
        <p className="section-lede">
          MachLib is the verification layer of a complete toolchain. It works
          on its own, but it really shines when the whole stack is wired up.
          Here&apos;s the path a single equation takes.
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
          You own every line from <strong>equation</strong> to{" "}
          <strong>silicon</strong> to <strong>proof</strong>.
          <br />
          No vendor. No external library. No 45-minute builds. No permission.
        </p>
      </div>
    </section>
  );
}
