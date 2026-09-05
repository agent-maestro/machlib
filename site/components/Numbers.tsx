"use client";

import { useEffect, useState } from "react";

// Static figures are measured, not remembered: each one is registered in
// foundations/tools/prose_counts.json and the prose-count gate fails the
// repository's check suite if the corpus drifts from what is printed here.
// The date is the measurement date; the command that reproduces each figure
// is in README.md under "Numbers, measured".
const MEASURED_ON = "2026-09-05";

const TILES: { value: string; label: string }[] = [
  { value: "7 570", label: "theorems, outside the Forge corpus" },
  { value: "149", label: "trusted axioms, every one modeled" },
  { value: "4", label: "distinct open obligations" },
  { value: "77.1 %", label: "of Forge @verify obligations auto-close" },
];

// Live status is written by CI to an orphan branch on every push to master;
// the JSON carries its own commit and timestamp and this page shows those,
// never the fetch time. If the fetch fails or the shape is wrong, say so
// loudly — never fall back to a remembered number.
const STATUS_URL =
  "https://raw.githubusercontent.com/agent-maestro/machlib/status-data/status.json";

interface LiveStatus {
  sha: string;
  generatedAt: string;
  buildPassed: boolean;
  coreSorries: number;
  discoveredSorries: number;
}

function parseStatus(raw: unknown): LiveStatus | null {
  if (typeof raw !== "object" || raw === null) return null;
  const d = raw as Record<string, unknown>;
  const build = d.build as Record<string, unknown> | undefined;
  const sorries = d.sorries as Record<string, unknown> | undefined;
  if (
    typeof d.machlib_sha !== "string" ||
    typeof d.generated_at_utc !== "string" ||
    !build ||
    typeof build.lake_build_passed !== "boolean" ||
    !sorries ||
    typeof sorries.core !== "number" ||
    typeof sorries.discovered !== "number"
  ) {
    return null;
  }
  return {
    sha: d.machlib_sha.slice(0, 8),
    generatedAt: d.generated_at_utc,
    buildPassed: build.lake_build_passed,
    coreSorries: sorries.core,
    discoveredSorries: sorries.discovered,
  };
}

export default function Numbers() {
  const [live, setLive] = useState<LiveStatus | null | "loading">("loading");

  useEffect(() => {
    let cancelled = false;
    fetch(STATUS_URL, { cache: "no-store" })
      .then((r) => (r.ok ? r.json() : null))
      .then((json: unknown) => {
        if (!cancelled) setLive(parseStatus(json));
      })
      .catch(() => {
        if (!cancelled) setLive(null);
      });
    return () => {
      cancelled = true;
    };
  }, []);

  return (
    <section id="numbers">
      <div className="container">
        <div className="eyebrow">// the numbers</div>
        <h2>Measured, with the command that reproduces each one.</h2>
        <p className="section-lede">
          Every figure here is the output of a command run on {MEASURED_ON},
          and a gate in the repository fails if the text drifts from the
          corpus. Re-run the command before quoting a number; the README lists
          them.
        </p>

        <div className="numbers">
          {TILES.map((t) => (
            <div className="tile" key={t.label}>
              <div className="value">{t.value}</div>
              <div className="label">{t.label}</div>
            </div>
          ))}
        </div>

        <p className="mono" style={{ marginTop: 28, fontSize: "0.95rem" }}>
          {live === "loading" ? (
            <>Live build status: fetching…</>
          ) : live === null ? (
            <span style={{ color: "var(--red)" }}>
              Live build status: unavailable (the status feed could not be
              fetched or did not parse). Nothing cached is shown in its place.
            </span>
          ) : (
            <>
              Live build status at commit {live.sha} ({live.generatedAt}):{" "}
              <span
                style={{
                  color: live.buildPassed ? "var(--accent)" : "var(--red)",
                }}
              >
                {live.buildPassed ? "lake build green" : "lake build RED"}
              </span>
              {" · "}
              core sorries {live.coreSorries} · Forge-corpus sorries{" "}
              {live.discoveredSorries}
            </>
          )}
        </p>
      </div>
    </section>
  );
}
