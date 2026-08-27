import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const NETWORK_APIS = [
  ["network-fetch", /\bfetch\s*\(/],
  ["network-xhr", /\bXMLHttpRequest\b/],
  ["network-websocket", /\bWebSocket\s*\(/],
  ["network-event-source", /\bEventSource\s*\(/],
  ["network-beacon", /\b(?:navigator\.)?sendBeacon\s*\(/],
  ["network-webtransport", /\bWebTransport\s*\(/],
];

const DYNAMIC_RESOURCE_APIS = [
  ["dynamic-script-create", /\bcreateElement\s*\(\s*["']script["']\s*\)/i],
  ["dynamic-source-assignment", /\.\s*src\s*=\s*["'`][^"'`]+["'`]/i],
  ["dynamic-source-attribute", /\bsetAttribute\s*\(\s*["']src["']\s*,/i],
];

const PRIVILEGED_MARKUP = [
  ["html-form", /<form\b/i],
  ["html-iframe", /<iframe\b/i],
  ["html-object", /<object\b/i],
  ["html-embed", /<embed\b/i],
];

const ALLOWED_STORAGE_KEYS = new Set(["STORAGE_KEY", "LANGUAGE_KEY"]);
const ALLOWED_SCRIPT_SOURCES = new Set([
  "readers/poetry-of-mathematics/hypothesis-orbit-wrapper.js",
]);

function scriptRecords(html) {
  return [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)]
    .map((match) => ({ attributes: match[1], body: match[2] }));
}

function storageArguments(script) {
  const calls = script.matchAll(
    /\blocalStorage\.(?:getItem|setItem|removeItem)\(\s*([A-Za-z_$][\w$]*|["'][^"']+["'])/g,
  );
  return [...calls].map((match) => match[1]);
}

export function inspectPublicStaticBoundary({ html, hosting }) {
  const scripts = scriptRecords(html);
  const inlineScript = scripts.map((script) => script.body).join("\n");
  const storageKeys = storageArguments(inlineScript);
  const checks = [];

  const add = (id, pass, detail) => checks.push({ id, pass, detail });

  add(
    "scripts-inline-only",
    scripts.every((script) => {
      const source = script.attributes.match(/\bsrc\s*=\s*["']([^"']+)["']/i);
      return !source || ALLOWED_SCRIPT_SOURCES.has(source[1]);
    }),
    "only the registered local PM-01 wrapper script is allowed",
  );

  add(
    "styles-inline-only",
    !/<link\b[^>]*\brel\s*=\s*["']?stylesheet\b/i.test(html) &&
      !/@import\s+(?:url\s*\()?["']?https?:/i.test(html),
    "external stylesheets and remote CSS imports are forbidden",
  );

  for (const [id, pattern] of NETWORK_APIS) {
    add(id, !pattern.test(inlineScript), `${pattern} is forbidden in executable script`);
  }

  for (const [id, pattern] of DYNAMIC_RESOURCE_APIS) {
    add(id, !pattern.test(inlineScript), `${pattern} is forbidden in executable script`);
  }

  add(
    "no-cookie-api",
    !/\bdocument\.cookie\b/.test(inlineScript),
    "document.cookie is forbidden",
  );

  add(
    "no-service-worker",
    !/\bserviceWorker\.(?:register|ready)\b/.test(inlineScript),
    "service-worker registration is forbidden",
  );

  add(
    "no-collector-route",
    !/["'`]\/collect(?:[/?#"'`]|$)/.test(inlineScript),
    "collector route literal is forbidden",
  );

  for (const [id, pattern] of PRIVILEGED_MARKUP) {
    add(id, !pattern.test(html), `${pattern} is forbidden in the public document`);
  }

  add(
    "no-admin-navigation",
    !/(?:href|action)\s*=\s*["'][^"']*\/admin(?:[/?#"' ]|$)/i.test(html),
    "public admin navigation is forbidden",
  );

  add(
    "registered-local-storage-only",
    storageKeys.every((key) => ALLOWED_STORAGE_KEYS.has(key)),
    `browser storage keys: ${storageKeys.join(", ") || "none"}`,
  );

  add(
    "d1-counter-only",
    hosting.d1 === "DB",
    "hosting.d1 must be exactly DB for the anonymous page-view counter",
  );

  add(
    "r2-unbound",
    hosting.r2 === null,
    "hosting.r2 must remain null in P0",
  );

  return {
    checks,
    ok: checks.every((check) => check.pass),
  };
}

export function formatBoundaryReport(result) {
  const rows = result.checks.map(
    (check) => `${check.pass ? "PASS" : "FAIL"}  ${check.id}  ${check.detail}`,
  );
  rows.push(`RESULT  ${result.ok ? "PASS" : "FAIL"}`);
  return rows.join("\n");
}

function runCli() {
  const scriptPath = fileURLToPath(import.meta.url);
  const projectRoot = path.resolve(path.dirname(scriptPath), "..");
  const html = fs.readFileSync(path.join(projectRoot, "public/index.html"), "utf8");
  const hosting = JSON.parse(
    fs.readFileSync(path.join(projectRoot, ".openai/hosting.json"), "utf8"),
  );
  const result = inspectPublicStaticBoundary({ html, hosting });
  process.stdout.write(`${formatBoundaryReport(result)}\n`);
  if (!result.ok) process.exitCode = 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runCli();
}
