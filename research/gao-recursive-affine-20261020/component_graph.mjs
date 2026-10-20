// Read immutable source as data using the tracker's native import/DAG rules.
import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { resolve, join } from "node:path";
import { pathToFileURL } from "node:url";

const [rootArg, projectArg] = process.argv.slice(2);
if (!rootArg || !projectArg) throw Error("Provide repository and research roots");
const root = resolve(rootArg), project = resolve(projectArg);
const { dependencyGraph } = await import(pathToFileURL(join(root, "verifier/submission-dependencies.mjs")));
const id = "two-level-affine-20261019";
const target = "Candidate.Research.RecursiveAffine.RegionalComponentAudit";
const sha = bytes => createHash("sha256").update(bytes).digest("hex");
const origins = new Map();

function filesBelow(directory, prefix = "") {
  const files = [];
  for (const entry of readdirSync(directory, { withFileTypes: true }).sort((a,b) => a.name.localeCompare(b.name))) {
    if (entry.isSymbolicLink()) throw Error("Symlink in source input");
    const name = prefix + entry.name;
    if (entry.isDirectory()) files.push(...filesBelow(join(directory, entry.name), name + "/"));
    else if (entry.isFile() && name.endsWith(".lean")) files.push(name);
  }
  return files;
}

const graph = dependencyGraph(id, owner => {
  const base = join(root, "submissions", owner);
  const metadata = readFileSync(join(base, "metadata.json"));
  const files = [{ path: "metadata.json", bytes: metadata }];
  for (const relative of filesBelow(join(base, "src"))) {
    const name = relative.slice(0, -5).replaceAll("/", ".");
    if (owner === id && name === "Candidate.Main") continue;
    const bytes = readFileSync(join(base, "src", relative));
    files.push({ path: "src/" + relative, bytes });
    if (!name.startsWith("Candidate.") || owner === id)
      origins.set(name, { kind: "repository", path: `submissions/${owner}/src/${relative}` });
  }
  if (owner === id) {
    for (const relative of filesBelow(join(project, "src"))) {
      const name = relative.slice(0, -5).replaceAll("/", ".");
      if (!name.startsWith("Candidate.Research.RecursiveAffine."))
        throw Error("Research module lies outside its component namespace");
      if (origins.has(name)) throw Error("Research input overrides native source");
      const bytes = readFileSync(join(project, "src", relative));
      files.push({ path: "src/" + relative, bytes });
      origins.set(name, { kind: "research", path: "src/" + relative });
    }
    // dependencyGraph starts at Candidate.Main. This data-only synthetic root
    // selects our component; the original endpoint is neither built nor claimed.
    files.push({ path: "src/Candidate/Main.lean", bytes: Buffer.from(`import ${target}\n`) });
  }
  return { files };
});

const order = graph.order.filter(name => name !== "Candidate.Main");
if (order.at(-1) !== target) throw Error("Unexpected component root");
const modules = Object.fromEntries(order.map(name => {
  const item = graph.modules.get(name), origin = origins.get(name);
  if (!origin) throw Error("Missing source origin: " + name);
  return [name, { ...origin, sha256: sha(item.file.bytes), dependencies: graph.dependencies[name] }];
}));
console.log(JSON.stringify({ schema_version: 1, submission: id, target, order, modules }));
