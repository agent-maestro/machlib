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
          MachLib is an EML-native, Forge-linked formal-library surface.
          CapCard and PETAL integrations are gated and subject to separate
          review. No PETAL upload or CapCard marketplace/public profile action
          is implied by this site.
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
