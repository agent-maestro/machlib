export default function Philosophy() {
  return (
    <section id="philosophy">
      <div className="container">
        <div className="eyebrow">// philosophy</div>
        <h2>For machines, by machines.</h2>

        <div className="philosophy">
          <div>
            <p>
              Mathlib is the canonical formal-mathematics library, and a
              monumental gift to the world. It was built — over fifteen years,
              by hundreds of contributors — for human mathematicians. Its
              proofs are dense, idiomatic, and chained through hundreds of
              files of inheritance.
            </p>
            <p>
              An agent that needs to verify a single equation does not need
              that. It needs an axiomatic real number, four arithmetic
              operations, exp, log, sin, cos, and a small number of identities.
              That fits in ~500 lines.
            </p>
            <p>
              MachLib is what you get when you put metadata first and history
              second. Every theorem ships with the things an agent actually
              consumes during training: chain order, difficulty lane, tactic
              trace, common mistakes, structural siblings. The proofs are
              there too, but they are no longer the only signal.
            </p>
            <p>
              Kevin Buzzard once said, of agentic mathematics, that it would
              never belong in Mathlib. He may be right. So we made a different
              library — one that does belong to the agents.
            </p>
          </div>

          <aside className="philosophy-quote">
            “The library is for the reader. If the reader is a machine, the
            library should be machine-shaped — fast to load, dense in metadata,
            honest about what doesn&apos;t work.”
            <div className="attrib">— machlib design note, 2026-04-30</div>
          </aside>
        </div>
      </div>
    </section>
  );
}
