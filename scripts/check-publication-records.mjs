import { readFile } from "node:fs/promises";

const registryUrl = new URL("../public/publications/records.json", import.meta.url);
const registry = JSON.parse(await readFile(registryUrl, "utf8"));
const failures = [];
const expectedRoute = ["distinction", "transition", "trace", "return"];

if (registry.canon?.id !== "IF-0.1") failures.push("canon id must be IF-0.1");
if (JSON.stringify(registry.canon?.route) !== JSON.stringify(expectedRoute)) {
  failures.push("canonical publication route changed");
}
if (!Array.isArray(registry.records) || registry.records.length === 0) {
  failures.push("publication registry has no records");
}

for (const record of registry.records ?? []) {
  const label = record.id ?? "<missing-id>";
  for (const key of ["id", "titleRu", "titleEn", "kind", "voice", "stage", "status", "claimCeiling"]) {
    if (!record[key]) failures.push(`${label}: missing ${key}`);
  }
  if (!expectedRoute.includes(record.stage)) failures.push(`${label}: stage is outside the canon`);
  if (!record.formal?.commit?.match(/^[0-9a-f]{40}$/)) failures.push(`${label}: formal commit is not frozen`);
  if (record.formal?.source?.includes("/blob/main/")) failures.push(`${label}: formal source points to mutable main`);
  if (!Array.isArray(record.notProved) || record.notProved.length < 3) failures.push(`${label}: claim boundary is incomplete`);
  if (record.status === "release-candidate") {
    if (record.doi !== null) failures.push(`${label}: RC must not claim a DOI`);
    if (record.orcidWorkId !== null) failures.push(`${label}: RC must not claim an ORCID work id`);
    if (record.releaseTag !== null) failures.push(`${label}: RC must not claim a release tag`);
  }
}

if (failures.length) {
  console.error(`Publication registry check failed:\n- ${failures.join("\n- ")}`);
  process.exit(1);
}

console.log(`Publication registry check passed: ${registry.records.length} RC record(s), canon ${registry.canon.id}.`);
