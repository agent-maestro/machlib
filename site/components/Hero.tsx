export default function Hero() {
  return (
    <section className="hero">
      <div className="container">
        <div className="tagline">// machlib.org</div>
        <h1>
          <span className="accent">MachLib</span>
        </h1>
        <p
          className="mono"
          style={{
            fontSize: "1.4rem",
            color: "var(--text-strong)",
            marginBottom: 32,
            marginTop: 8,
          }}
        >
          For machines, by machines.
        </p>
        <p
          className="mono"
          style={{
            color: "var(--accent)",
            fontSize: "0.95rem",
            letterSpacing: "0.04em",
            marginBottom: 18,
          }}
        >
          import MachLib.EML — release snapshot pending — counts by manifest
        </p>
        <p className="subtitle">
          A machine-native formal-library corpus workbench.
          <br />
          EML-native, Forge-linked, and Lean-checkable where verified artifacts
          are present. Zero Mathlib dependency, gate-backed.
        </p>
        <div className="hero-buttons">
          <a
            className="button primary"
            href="https://huggingface.co/datasets/Monogate/machlib"
            target="_blank"
            rel="noopener noreferrer"
          >
            Dataset Status →
          </a>
          <a className="button" href="#philosophy">
            Read the Philosophy
          </a>
        </div>
      </div>
    </section>
  );
}
