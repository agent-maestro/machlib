const ENGINES: { num: string; title: string; body: string }[] = [
  {
    num: "01",
    title: "Synthetic Generation",
    body:
      "Five strategies — constant_swap, domain_change, operator_swap, " +
      "composition_depth, negation — fan a single base theorem into a family " +
      "of structurally related variants. Release snapshots record which " +
      "candidate records came from this engine.",
  },
  {
    num: "02",
    title: "Forge Mining",
    body:
      "Every @verify(lean) annotation in Monogate Forge emits a Lean obligation. " +
      "When Forge compiles an industrial vertical, MachLib gains the precision " +
      "and overflow theorems that vertical demands.",
  },
  {
    num: "03",
    title: "Proof Gym (RL)",
    body:
      "A Gymnasium-compatible Lean environment with a 54-tactic vocabulary. " +
      "Agents discover non-obvious proofs; successful trajectories are added " +
      "back into the corpus along with their tactic traces.",
  },
  {
    num: "04",
    title: "Multi-Proof BFS",
    body:
      "For each theorem, breadth-first search enumerates alternative proofs " +
      "shorter or different from the canonical one. MachLib stores all of them — " +
      "is_optimal is a property, not a chosen branch.",
  },
  {
    num: "05",
    title: "Community",
    body:
      "Lean developers contribute new theorems through pull requests. Every " +
      "PR runs the schema validator + lake build + structural sibling check. " +
      "Accepted records inherit the contributor's name in metadata.",
  },
  {
    num: "06",
    title: "Cross-Domain",
    body:
      "When a structural sibling is discovered between two domains (Gaussian " +
      "↔ photoreceptor, sigmoid ↔ attention), the relationship is recorded on " +
      "both endpoints. The corpus densifies as it grows.",
  },
];

export default function Engines() {
  return (
    <section id="growth">
      <div className="container">
        <div className="eyebrow">// how it grows</div>
        <h2>Six engines feed the corpus.</h2>
        <p className="section-lede">
          MachLib is organized around release snapshots and pipeline metadata.
          Candidate records can arrive
          from synthesis, compilation, RL training, search, contribution, and
          cross-domain bridging, with status recorded per snapshot.
        </p>

        <div className="engines">
          {ENGINES.map((e) => (
            <div className="engine" key={e.num}>
              <div className="engine-num">{e.num}</div>
              <h3>{e.title}</h3>
              <p>{e.body}</p>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}
