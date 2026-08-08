import { access, readFile } from "node:fs/promises";
import { resolve } from "node:path";

const root = process.cwd();
const registryPath = resolve(root, "public/corpus/interfaces.json");
const registry = JSON.parse(await readFile(registryPath, "utf8"));
const failures = [];
const ids = new Set();
const sourceBase = "https://github.com/kernelpanic888/chertogi-razuma-research/blob/main/";

const exists = async (path, label) => {
  try {
    await access(resolve(root, path));
  } catch {
    failures.push(`${label}: missing ${path}`);
  }
};

if (registry.schema !== "CI-01/1") failures.push("schema: expected CI-01/1");
if (registry.contract?.sourceOfTruth !== "git") failures.push("contract: Git must remain primary");

for (const reader of registry.readers ?? []) {
  if (ids.has(reader.id)) failures.push(`id: duplicate ${reader.id}`);
  ids.add(reader.id);
  await exists(reader.sourcePath, reader.id);
  for (const journalPath of reader.journalPaths ?? []) await exists(journalPath, `${reader.id} journal`);

  if (reader.publicPath !== "/") {
    const html = await readFile(resolve(root, reader.sourcePath), "utf8");
    if (!html.includes(`${sourceBase}${reader.sourcePath}`)) failures.push(`${reader.id}: source return link missing`);
    if (reader.id !== "CI-01" && !html.includes("corpus-interface/index.html")) failures.push(`${reader.id}: corpus return link missing`);
  }
}

for (const edge of registry.edges ?? []) {
  if (!ids.has(edge.from)) failures.push(`edge: unknown source ${edge.from}`);
  if (!ids.has(edge.to)) failures.push(`edge: unknown target ${edge.to}`);
}

const home = await readFile(resolve(root, "public/index.html"), "utf8");
if (!home.includes("readers/corpus-interface/index.html")) failures.push("home: corpus interface gate missing");
if (!home.includes("https://github.com/kernelpanic888/chertogi-razuma-research")) failures.push("home: canonical repository link missing");

const readme = await readFile(resolve(root, "README.md"), "utf8");
if (!readme.includes("CORPUS_INTERFACE.md")) failures.push("README: corpus contract link missing");
if (!readme.includes(registry.site)) failures.push("README: live site link missing");

if (failures.length) {
  console.error("CI-01 / CORPUS INTERFACE: FAIL");
  for (const failure of failures) console.error(`- ${failure}`);
  process.exit(1);
}

const open = registry.readers.filter((reader) => reader.status.startsWith("open-")).length;
console.log(`CI-01 / CORPUS INTERFACE: PASS · ${ids.size} nodes · ${registry.edges.length} edges · ${open} open seams`);
