import React from "react";

const RECORD = {
  schema_version: "1.0.0",
  theorem: {
    id: "depth_of_const",
    statement: {
      informal:
        "The depth of a constant-leaf EML tree is zero. A bare constant has no `ceml` operations to count.",
      formal_lean:
        "theorem depth_of_const (c : ℂ) : (EMLTree.const c).depth = 0 := rfl",
    },
    domain: "eml",
    lane: 1,
    tags: ["depth", "definition", "rfl", "lane-1"],
  },
  proofs: [
    {
      id: "p1",
      tactics: ["rfl"],
      tactic_count: 1,
      eml_node_cost: 1,
      style: "definitional",
      is_optimal: true,
    },
  ],
  difficulty: {
    lane: 1,
    label: "beginner",
    prerequisite_skills: [],
  },
  common_mistakes: [
    {
      why_fails:
        "Using `simp [EMLTree.depth]` works but is overkill — `rfl` already suffices.",
    },
    {
      why_fails:
        "`by decide` fails because `EMLTree.depth` is not a `Decidable` proposition.",
    },
  ],
  structural_profile: {
    chain_order: null,
    drift_risk: "LOW",
    dynamics: { oscillations: 0, decays: 0 },
  },
  relationships: {
    structural_siblings: ["depth_ceml_pos", "exp_in_EML_one"],
  },
  metadata: {
    verified: true,
    verification_method: "lean4_kernel",
  },
} as const;

// Tiny JSON-with-highlighting renderer. Renders the object as a syntax-coloured
// JSON string. Done in one pass over a stable JSON.stringify output so we don't
// re-implement a JSON parser.
function highlightJson(obj: unknown): React.ReactNode {
  const text = JSON.stringify(obj, null, 2);
  // token order matters: strings first (so the regex inside doesn't gobble
  // numbers or booleans inside string contents).
  const tokenRe =
    /("(?:[^"\\]|\\.)*")(\s*:)?|(\b(?:true|false)\b)|(\bnull\b)|(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)/g;

  const out: React.ReactNode[] = [];
  let lastIndex = 0;
  let match: RegExpExecArray | null;
  let key = 0;

  while ((match = tokenRe.exec(text)) !== null) {
    if (match.index > lastIndex) {
      out.push(text.slice(lastIndex, match.index));
    }
    const [, str, colon, bool, nullTok, num] = match;
    if (str !== undefined) {
      const cls = colon ? "json-key" : "json-str";
      out.push(
        <span key={key++} className={cls}>
          {str}
        </span>,
      );
      if (colon) out.push(colon);
    } else if (bool !== undefined) {
      out.push(
        <span key={key++} className="json-bool">
          {bool}
        </span>,
      );
    } else if (nullTok !== undefined) {
      out.push(
        <span key={key++} className="json-null">
          {nullTok}
        </span>,
      );
    } else if (num !== undefined) {
      out.push(
        <span key={key++} className="json-num">
          {num}
        </span>,
      );
    }
    lastIndex = tokenRe.lastIndex;
  }
  if (lastIndex < text.length) {
    out.push(text.slice(lastIndex));
  }
  return out;
}

export default function RecordViewer() {
  return (
    <section id="record">
      <div className="container">
        <div className="eyebrow">// what every record contains</div>
        <h2>Eight sections per theorem.</h2>
        <p className="section-lede">
          Every MachLib record is a self-contained training example. A single
          theorem ships with formal + informal statements, multiple proofs,
          tactic traces, common mistakes, structural profile, and relationships.
          One record, one JSON file, no ambient state.
        </p>

        <div className="record-card">
          <div className="record-header">
            <span
              className="mono"
              style={{ color: "var(--accent)" }}
            >
              depth_of_const.json
            </span>
            <span className="record-header-meta">lane 1 · beginner</span>
          </div>
          <pre className="record-body">
            <code>{highlightJson(RECORD)}</code>
          </pre>
        </div>
      </div>
    </section>
  );
}
