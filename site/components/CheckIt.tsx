type Path = {
  audience: string;
  body: string;
  cmd: string;
  href: string;
  hrefLabel: string;
};

const PATHS: Path[] = [
  {
    audience: "Check it",
    body:
      "Clone, build, and run every gate. The runner prints each verdict and exits non-zero " +
      "if any gate fails, and it refuses to certify a tree that changed while it ran.",
    cmd:
      "git clone https://github.com/agent-maestro/machlib\ncd machlib/foundations\nlake build\ntools/check_all.sh",
    href: "https://github.com/agent-maestro/machlib/blob/master/foundations/tools/check_all.sh",
    hrefLabel: "The gate runner →",
  },
  {
    audience: "Read it",
    body:
      "The claim inventory says what is proven, what it rests on and what is open, with a " +
      "command next to each claim. If something there cannot be reproduced in a few commands, " +
      "that is a bug in the document.",
    cmd: "cd machlib/foundations\nlake env lean AxiomLedger.lean\n# 243 axioms pinned; headline footprints ⊆ trusted",
    href: "https://github.com/agent-maestro/machlib/blob/master/foundations/docs/what_is_proven.md",
    hrefLabel: "what_is_proven.md →",
  },
  {
    audience: "Reproduce it",
    body:
      "The range-bearing EKF package holds everything a stranger needs to walk one kernel from " +
      "source to certificate to silicon anchor. It exists because the first outside reproducer " +
      "got two of five, and a reproduction claim that withholds its evidence is not one.",
    cmd: "cd machlib/reproduction/rb_ekf\ncat README.md\nsha256sum -c MANIFEST.sha256",
    href: "https://github.com/agent-maestro/machlib/tree/master/reproduction/rb_ekf",
    hrefLabel: "reproduction/rb_ekf →",
  },
];

export default function CheckIt() {
  return (
    <section id="check-it">
      <div className="container">
        <div className="eyebrow">// check it yourself</div>
        <h2>Three ways in, each ending in a command.</h2>
        <p className="section-lede">
          Nothing on this page asks to be believed. The library builds in about
          a minute and its gates run in about fifteen.
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
