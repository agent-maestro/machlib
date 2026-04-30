type Tile = {
  name: string;
  tagline: string;
  href: string | null;
  current?: boolean;
};

const TILES: Tile[] = [
  {
    name: "Forge",
    tagline: "Math → silicon",
    href: "https://monogateforge.com",
  },
  {
    name: "CapCard",
    tagline: "Agent capability cards",
    href: "https://capcard.ai",
  },
  {
    name: "MachLib",
    tagline: "This library",
    href: null,
    current: true,
  },
  {
    name: "PETAL",
    tagline: "Lean verification API",
    href: "https://api.monogate.dev",
  },
  {
    name: "1op",
    tagline: "Equation playground",
    href: "https://1op.io",
  },
];

export default function Ecosystem() {
  return (
    <section id="ecosystem">
      <div className="container">
        <div className="eyebrow">// the monogate ecosystem</div>
        <h2>Part of a larger stack.</h2>
        <p className="section-lede">
          MachLib is the foundations layer. The Forge compiles to it, CapCard
          certifies on top of it, PETAL verifies through it, 1op visualises
          what runs on it. Each piece is independently useful — together they
          form a verified, agent-native math toolchain.
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
