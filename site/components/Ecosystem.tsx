type Tile = {
  name: string;
  tagline: string;
  href: string | null;
  current?: boolean;
};

const TILES: Tile[] = [
  {
    name: "Forge",
    tagline: "The EML compiler; emits the proof obligations",
    href: "https://github.com/agent-maestro/forge",
  },
  {
    name: "MachLib",
    tagline: "This library",
    href: null,
    current: true,
  },
  {
    name: "monogate-lean",
    tagline: "Witnesses every MachLib axiom in Mathlib",
    href: "https://github.com/agent-maestro/monogate-lean",
  },
  {
    name: "eml-stdlib",
    tagline: "Kernels with @verify contracts checked here",
    href: "https://github.com/agent-maestro/eml-stdlib",
  },
  {
    name: "1op",
    tagline: "Live verification status, rained into buckets",
    href: "https://1op.io/research/machlib-pulse",
  },
];

export default function Ecosystem() {
  return (
    <section id="ecosystem">
      <div className="container">
        <div className="eyebrow">// where it sits</div>
        <h2>One link in a chain that has to hold end to end.</h2>
        <p className="section-lede">
          Forge compiles a kernel and emits its proof obligations into this
          library; this library proves what it can and names what it cannot;
          a sibling project checks this library&apos;s own axioms against
          Mathlib. None of the three vouches for itself.
        </p>

        <div className="ecosystem">
          {TILES.map((t) =>
            t.href ? (
              <a
                key={t.name}
                className={`eco-tile${t.current ? " current" : ""}`}
                href={t.href}
                target="_blank"
                rel="noopener noreferrer"
              >
                <div className="eco-name">{t.name}</div>
                <div className="eco-tagline">{t.tagline}</div>
              </a>
            ) : (
              <div
                key={t.name}
                className={`eco-tile${t.current ? " current" : ""}`}
              >
                <div className="eco-name">{t.name}</div>
                <div className="eco-tagline">{t.tagline}</div>
              </div>
            ),
          )}
        </div>
      </div>
    </section>
  );
}
