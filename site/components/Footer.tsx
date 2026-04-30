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
              href="https://huggingface.co/datasets/Monogate/machlib"
              target="_blank"
              rel="noopener noreferrer"
            >
              Hugging Face
            </a>
            <a href="#philosophy">Philosophy</a>
            <a
              href="https://monogateforge.com"
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
