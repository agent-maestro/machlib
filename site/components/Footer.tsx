export default function Footer() {
  return (
    <footer>
      <div className="container">
        <div className="footer-row">
          <div>
            <span style={{ color: "var(--text-strong)" }}>MachLib</span> ·
            <span> CC BY 4.0</span> ·
            <span> Mosa Creates LLC</span> ·
            <span> Seattle, WA</span>
          </div>
          <div className="footer-links">
            <a
              href="https://github.com/agent-maestro/machlib"
              target="_blank"
              rel="noopener noreferrer"
            >
              GitHub
            </a>
            <a
              href="https://github.com/agent-maestro/machlib/blob/master/foundations/docs/what_is_proven.md"
              target="_blank"
              rel="noopener noreferrer"
            >
              What is proven
            </a>
            <a
              href="https://github.com/agent-maestro/machlib/blob/master/foundations/AXIOM_MANIFEST.md"
              target="_blank"
              rel="noopener noreferrer"
            >
              Axiom manifest
            </a>
            <a
              href="https://github.com/agent-maestro/forge"
              target="_blank"
              rel="noopener noreferrer"
            >
              Forge
            </a>
          </div>
        </div>
      </div>
    </footer>
  );
}
