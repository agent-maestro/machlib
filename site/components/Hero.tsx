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
          import MachLib.EML — &lt;5 min core build — 2,786 records
        </p>
        <p className="subtitle">
          A machine-native formal mathematics library.
          <br />
          Fed by Forge. Trained on by agents. Verified by the Lean kernel.
          Zero Mathlib dependency.
        </p>
        <div className="hero-buttons">
          <a
            className="button primary"
            href="https://huggingface.co/datasets/Monogate/machlib"
            target="_blank"
            rel="noopener noreferrer"
          >
            Browse the Dataset →
          </a>
          <a className="button" href="#philosophy">
            Read the Philosophy
          </a>
        </div>
      </div>
    </section>
  );
}
