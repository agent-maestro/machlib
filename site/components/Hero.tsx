export default function Hero() {
  return (
    <section className="hero">
      <div className="container">
        <div className="tagline">// machlib.org</div>
        <h1>
          Machine-checked theorems about{" "}
          <span className="accent">compiled numerics.</span>
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
          MachLib — Lean 4, Mathlib-free, every axiom listed and modeled.
        </p>
        <p className="subtitle">
          MachLib is a Lean 4 library that proves things about EML kernels: the
          small exp/log expression language that Forge compiles to C, GPU code
          and RTL. It carries its own axiomatised reals instead of Mathlib, so
          the compiler&apos;s proof obligations build in a minute — and every
          one of those axioms is checked against Mathlib in a sibling project.
        </p>
        <div className="hero-buttons">
          <a
            className="button primary"
            href="https://github.com/agent-maestro/machlib/blob/master/foundations/docs/what_is_proven.md"
            target="_blank"
            rel="noopener noreferrer"
          >
            What is proven →
          </a>
          <a
            className="button"
            href="https://github.com/agent-maestro/machlib"
            target="_blank"
            rel="noopener noreferrer"
          >
            Read the source
          </a>
        </div>
      </div>
    </section>
  );
}
