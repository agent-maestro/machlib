type Path = {
  audience: string;
  body: string;
  cmd: string;
  href: string;
  hrefLabel: string;
};

const PATHS: Path[] = [
  {
    audience: "ML researchers",
    body:
      "Dataset access is pending/private-gated until a reviewed public " +
      "release is approved. Counts and schema status are published per " +
      "release snapshot.",
    cmd:
      "# No public Hugging Face release is performed by this site copy.\n# See the release manifest for dataset access status.",
    href: "https://huggingface.co/datasets/Monogate/machlib",
    hrefLabel: "Dataset access status →",
  },
  {
    audience: "Agent builders",
    body:
      "Use the Lean foundations as a local check target where verified " +
      "artifacts are present. The zero-Mathlib release gate must pass before " +
      "zero-dependency claims are made.",
    cmd: "git clone https://github.com/agent-maestro/machlib\ncd machlib/foundations && lake build",
    href: "https://github.com/agent-maestro/machlib",
    hrefLabel: "github.com/agent-maestro/machlib →",
  },
  {
    audience: "Lean developers",
    body:
      "Contribute. The schema is documented; the validator runs on every PR. " +
      "Add a theorem, add its tactic trace, add the mistakes that don&apos;t " +
      "work. The corpus grows from there.",
    cmd: "lake new my_theorem\nimport MachLib",
    href: "https://github.com/agent-maestro/machlib/blob/master/CONTRIBUTING.md",
    hrefLabel: "Read the contributing guide →",
  },
];

export default function GetStarted() {
  return (
    <section id="get-started">
      <div className="container">
        <div className="eyebrow">// get started</div>
        <h2>Three ways in.</h2>
        <p className="section-lede">
          Pick the one that matches what you do today. The corpus, the
          foundations, and the contribution loop are reviewed per release
          snapshot.
        </p>

        <div className="paths">
          {PATHS.map((p) => (
            <div className="path" key={p.audience}>
              <h3>{p.audience}</h3>
              <p>{p.body}</p>
              <div className="path-cmd">{p.cmd}</div>
              <a
                className="path-link"
                href={p.href}
                target="_blank"
                rel="noopener noreferrer"
              >
                {p.hrefLabel}
              </a>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}
