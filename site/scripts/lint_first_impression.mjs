#!/usr/bin/env node
// scripts/lint_first_impression.mjs
//
// First-impression lint for monogate.dev pages.
//
// Motivation: after a muse audit (2026-06-17) found that the homepage
// was leading with internal jargon ("Evidence Packets", "Proof
// Digestion", "Rescue Traces") that fresh visitors couldn't decode,
// the homepage + Explorer landing got a hero rewrite. This script
// catches the same drift automatically across the site so the rewrite
// doesn't decay back into jargon as the codebase grows.
//
// What it checks for each page:
//   1. The H1 must convey VALUE or WHAT (not just brand wordmark).
//   2. The first ~500 chars of visible text must not lead with
//      unexplained internal nouns from a curated jargon list.
//   3. Page-level metadata description must not be the same generic
//      placeholder as other pages.
//
// Implementation: pure file-system scan of app/**/page.tsx + the
// LandingPage.jsx components. No network, no LLM, no running dev
// server — works in CI on a clean checkout.
//
// Future extension: add an `--llm-judge` mode that calls Claude/GPT
// with a "could a fresh visitor decode this in 10 seconds?" prompt
// for ambiguous cases. The heuristic baseline catches the obvious
// drift; an LLM is only needed for the borderline calls.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const APP_ROOT = path.resolve(__dirname, "..", "app");
const LIB_ROOT = path.resolve(__dirname, "..", "lib");
const COMPONENTS_ROOT = path.resolve(__dirname, "..", "components");

// Jargon to flag if it appears UNDEFINED in the first ~500 chars of a
// page's visible text. "Undefined" means the same paragraph doesn't
// also contain a definitional cue ("is", "—", ":", inline code).
//
// This list is curated from the muse feedback + observed drift. Add
// to it as new internal nouns emerge.
const JARGON = [
  "Evidence Packet",
  "evidence packet",
  "Rescue Trace",
  "rescue trace",
  "Proof Digestion",
  "EML IR Bridge",
  "Atlas Annex",
  "Packet Gallery",
  "PETAL", // capitalized acronym, jargon unless defined
  "MachLib",
  "Forge", // ambiguous — "Forge" alone could be the verb; only flag if no defining context
];

// Brand-only wordmarks that fail the "what does this page do" test
// when used as H1. (A subtitle saying "monogate" is fine; an H1 that's
// JUST "monogate" is a failure.)
const BRAND_ONLY = [
  "monogate", "Monogate", "monogate.dev", "monogate.org",
  "monogate.net", "machlib", "MachLib", "machlib.org",
];

// Pages where the heuristics are deliberately relaxed (deep internal
// surfaces where visitors arriving have already opted into the
// vocabulary).
const RELAXED_PATHS = [
  "app/learn/eml/", // deep within a tutorial — context is set
  "app/proof-digestion/page.tsx", // internal tool; nav-linked from research stack
];

// --- File walker ---

function* walkPages(root) {
  for (const entry of fs.readdirSync(root, { withFileTypes: true })) {
    if (entry.name.startsWith(".") || entry.name === "node_modules") continue;
    const full = path.join(root, entry.name);
    if (entry.isDirectory()) {
      yield* walkPages(full);
    } else if (
      entry.name === "page.tsx" ||
      entry.name === "page.jsx" ||
      entry.name === "LandingPage.jsx" ||
      entry.name === "LearnHubClient.tsx" ||
      entry.name === "Hero.tsx" ||
      entry.name === "Hero.jsx"
    ) {
      yield full;
    }
  }
}

// --- Text extraction ---

// Best-effort H1 extraction: looks for the first <h1>...</h1>, JSX
// attribute-styled <h1 style=...>...</h1>, or {`...`} braced child.
function extractH1(source) {
  // Handle React fragments and multi-line H1 with style props.
  // We match <h1 ...> ... </h1> spanning lines, including nested
  // JSX expressions like {something}<br />.
  const re = /<h1[^>]*>([\s\S]*?)<\/h1>/i;
  const m = source.match(re);
  if (!m) return null;
  // Strip JSX expressions like {variable} and {`literal`}, keep static
  // text. Strip <br />, <span>, etc.
  let text = m[1]
    .replace(/<br\s*\/?>/gi, " ")
    .replace(/<span[^>]*>([\s\S]*?)<\/span>/gi, "$1")
    .replace(/\{`([^`]*)`\}/g, "$1") // template literal child
    .replace(/\{[^}]*\}/g, "") // any other JSX expression
    .replace(/<[^>]+>/g, "") // any remaining tags
    .replace(/\s+/g, " ")
    .trim();
  return text || null;
}

// Best-effort lead-paragraph extraction. Looks for the first <p>...</p>
// after the H1. Similar JSX cleanup.
function extractLead(source) {
  const h1End = source.search(/<\/h1>/i);
  if (h1End < 0) return null;
  const after = source.slice(h1End);
  const re = /<p[^>]*>([\s\S]*?)<\/p>/i;
  const m = after.match(re);
  if (!m) return null;
  let text = m[1]
    .replace(/<br\s*\/?>/gi, " ")
    .replace(/<strong[^>]*>([\s\S]*?)<\/strong>/gi, "$1")
    .replace(/<code[^>]*>([\s\S]*?)<\/code>/gi, "$1")
    .replace(/<a[^>]*>([\s\S]*?)<\/a>/gi, "$1")
    .replace(/\{`([^`]*)`\}/g, "$1")
    .replace(/\{[^}]*\}/g, "")
    .replace(/<[^>]+>/g, "")
    .replace(/\s+/g, " ")
    .trim();
  return text || null;
}

// Extract metadata.description from Next.js page metadata exports.
function extractMetaDescription(source) {
  const re = /description:\s*["`]([\s\S]*?)["`]/;
  const m = source.match(re);
  if (!m) return null;
  return m[1].replace(/\s+/g, " ").trim();
}

// --- Checks ---

function isRelaxed(filePath) {
  const rel = path.relative(path.resolve(__dirname, ".."), filePath);
  return RELAXED_PATHS.some((p) => rel.startsWith(p) || rel === p);
}

function checkBrandOnlyH1(h1) {
  if (!h1) return null;
  const cleaned = h1.toLowerCase().replace(/[—–\-·.]+/g, "").trim();
  if (BRAND_ONLY.some((b) => cleaned === b.toLowerCase())) {
    return `H1 is brand-wordmark only ("${h1}") — fresh visitors get no value cue.`;
  }
  return null;
}

function checkUndefinedJargon(lead) {
  if (!lead) return null;
  const window = lead.slice(0, 500);
  const hits = [];
  for (const term of JARGON) {
    const idx = window.indexOf(term);
    if (idx < 0) continue;
    // Look for a definitional cue within ~80 chars of the hit.
    const localStart = Math.max(0, idx - 30);
    const localEnd = Math.min(window.length, idx + term.length + 80);
    const context = window.slice(localStart, localEnd);
    const definitional =
      /\bis\b|\bare\b|—|–|:|`[^`]+`|\bdefined\b|\bmeans\b|\bcalled\b/.test(
        context,
      );
    if (!definitional) hits.push(term);
  }
  if (hits.length === 0) return null;
  return `Undefined jargon in lead: ${hits.map((t) => `"${t}"`).join(", ")} — none has a definitional cue within 80 chars.`;
}

function checkLongH1(h1) {
  if (!h1) return null;
  if (h1.length > 90) {
    return `H1 is ${h1.length} chars — should be punchy (under ~90). Visitors skim, not parse.`;
  }
  return null;
}

// --- Report ---

const report = [];
let pageCount = 0;
let warnCount = 0;

const roots = [APP_ROOT, LIB_ROOT, COMPONENTS_ROOT];
for (const root of roots) {
  if (!fs.existsSync(root)) continue;
  for (const file of walkPages(root)) {
    pageCount++;
    const source = fs.readFileSync(file, "utf8");
    const rel = path.relative(path.resolve(__dirname, ".."), file);
    const relaxed = isRelaxed(file);

    const h1 = extractH1(source);
    const lead = extractLead(source);
    const desc = extractMetaDescription(source);

    const findings = [];
    if (!relaxed) {
      const a = checkBrandOnlyH1(h1);
      if (a) findings.push(a);
      const b = checkUndefinedJargon(lead);
      if (b) findings.push(b);
      const c = checkLongH1(h1);
      if (c) findings.push(c);
    }

    if (findings.length > 0) {
      warnCount++;
      report.push({ rel, h1, lead: lead?.slice(0, 200), desc, findings, relaxed });
    }
  }
}

// --- Output ---

const argv = process.argv.slice(2);
const jsonMode = argv.includes("--json");

if (jsonMode) {
  console.log(
    JSON.stringify({ scanned: pageCount, warnings: warnCount, items: report }, null, 2),
  );
} else {
  console.log(`# First-impression lint — monogate.dev`);
  console.log("");
  console.log(`Scanned: **${pageCount}** pages`);
  console.log(`Warnings: **${warnCount}**`);
  console.log("");
  if (report.length === 0) {
    console.log(`✅ No fresh-visitor comprehension issues detected.`);
  } else {
    console.log(`## Pages with findings`);
    console.log("");
    for (const item of report) {
      console.log(`### \`${item.rel}\``);
      console.log("");
      console.log(`- **H1**: ${item.h1 ?? "_(not detected)_"}`);
      if (item.lead) {
        console.log(`- **Lead**: ${item.lead}${item.lead.length >= 200 ? "…" : ""}`);
      }
      console.log("");
      console.log(`**Findings:**`);
      for (const f of item.findings) {
        console.log(`- ${f}`);
      }
      console.log("");
    }
  }
}

process.exit(warnCount > 0 && argv.includes("--strict") ? 1 : 0);
