const CLASSES: { value: string; label: string }[] = [
  { value: "112", label: "witnessed — a Mathlib term inhabits the interpreted type, kernel-checked" },
  { value: "12", label: "mapped — carrier or function symbol, interpreted rather than asserted" },
  { value: "3", label: "standard — propext, Classical.choice, Quot.sound" },
  { value: "22", label: "float-bridge — IEEE-754 facts with no model in ℝ, validated by measurement" },
];

export default function TrustBase() {
  return (
    <section id="trust">
      <div className="container">
        <div className="eyebrow">// what it rests on</div>
        <h2>Zero unmodeled axioms. Not zero axioms.</h2>
        <p className="section-lede">
          Everything Mathlib would prove as a theorem — the ordered field of
          reals, the definitions and derivatives of exp, log, sin and cos, the
          floating-point model — is an axiom here. A library built on axioms
          can be vacuous without a single <code>sorry</code>, so nothing
          inside MachLib is allowed to vouch for MachLib. A sibling project
          that imports both Mathlib and MachLib checks, in the kernel, that a
          Mathlib term inhabits each axiom&apos;s interpreted type. The
          manifest listing all 149 is generated, and a gate fails if the
          witness project stops running — it did once, for 33 days.
        </p>

        <div className="numbers">
          {CLASSES.map((c) => (
            <div className="tile" key={c.label}>
              <div className="value">{c.value}</div>
              <div className="label">{c.label}</div>
            </div>
          ))}
        </div>

        <p className="flow-coda" style={{ marginTop: 28 }}>
          The 22 float-bridge axioms are a different kind of trust and are not
          averaged in. A hardware certificate rests on exactly those; read that
          block of the manifest first.
        </p>
      </div>
    </section>
  );
}
