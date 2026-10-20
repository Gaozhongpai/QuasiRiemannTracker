#!/usr/bin/env python3
"""Typecheck one source component, never a leaderboard endpoint or admission.

Only source-matching products from the pinned, server-signed archive may
supply submission dependencies. A cache miss fails before any baseline rebuild.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request

PROJECT = Path(__file__).resolve().parent
TARGET = "Candidate.Research.RecursiveAffine.RegionalMainDriver"
DECLARATION = (
    "OAI.SevenEighths.Cycle153RegionalMain."
    "actual_affine_main_parent_component_payment_with_regional_returns"
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BASELINE_PREFIX = "Submissions.openai_baseline."
FRESH_PREFIXES = ("Candidate.", "Submissions.akashlevy_20261009_weighted_numerator.")
REFERENCE_HEAD = "0db497edc397d7076b1652b060e49c76b683e901"
CACHE = {
    "release": "https://github.com/GTimG/QuasiRiemannTracker/releases/download/submission-build-cache-v1/",
    "index_sha256": "21cec1d4949d791d01894118faa268ab6125d25b46fbd549f4cdcf699107958f",
    "archive_sha256": "5a36a0a56a4425d6f7cbf1e6e303ef2dfbd318f638addd20dc949df787578361",
    "size": 1056853185,
    "source_head": "edbb22b1a080c961b19e438e9e8ce6d6b3842739",
    "environment": "aea7ad38ebebc547968c7ea50dafc45430ee6a802ee39d7e160f99bd4bf6d045",
    "compiler": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    "public_key_sha256": "e40b1ceb0779cb57cd34d1437db8f54a67d84f1661ea13397dc4e252364ed6d1",
}
VERIFIER_PINS = {
    "verifier/standard/build_cache.py": "a5acfcefa0e30ffbf030ca620b4cbe87dff44530ace952fcc00aae40398ef9c3",
    "verifier/standard/compile.py": "f3f20b9272567d0724414721a5444749ff51259b9aea68bf4794f91486c303cd",
    "verifier/actions/setup.py": "f5ea7300c6116f7a901d940d67f8640f5a54c8796e00f9503413ed69bd9fa336",
    "verifier/submission-dependencies.mjs": "d410903d171b819d6bbec1fdfa250ea9be943cf4905520dac8bda500dd70c264",
    "verifier/actions/imports.mjs": "4ae77b27e5cb73be4a2c1181dc391804f7190f1c7153f6486467d048ebc3ee2e",
}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".new")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def log_text(value, root, project, work):
    # GitHub paths are public worker paths, but relative diagnostics are clearer.
    for path, replacement in [(work, "$COMPONENT_WORK"), (project, "$COMPONENT"), (root, "$REPOSITORY")]:
        value = value.replace(str(path), replacement)
    return value


def source_path(item, root, project):
    relative = Path(item["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("Nonrelative source path")
    base = project if item["kind"] == "research" else root
    candidate = base / relative
    if candidate.is_symlink() or not candidate.is_file():
        raise ValueError("Source input is not a regular file")
    return candidate


def make_plan(root, project):
    for name, expected in VERIFIER_PINS.items():
        if digest(root / name) != expected:
            raise ValueError("Protected verifier source differs: " + name)
    result = subprocess.run(
        ["node", str(project / "component_graph.mjs"), str(root), str(project)],
        capture_output=True, text=True,
    )
    if result.returncode:
        detail = result.stderr.replace(str(root), "$REPOSITORY").replace(str(project), "$COMPONENT")
        raise ValueError("Component source-graph preparation failed:\n" + detail[-5000:])
    plan = json.loads(result.stdout)
    if plan["target"] != TARGET or plan["order"][-1] != TARGET:
        raise ValueError("Incorrect component graph root")
    return plan


def check_source_lock(plan, root, project, *, refresh=False):
    native = {
        item["path"]: item["sha256"]
        for item in plan["modules"].values() if item["kind"] == "repository"
    }
    path = project / "source-lock.json"
    if refresh:
        save(path, {"reference_head": REFERENCE_HEAD, "native_sources": native})
    locked = json.loads(path.read_text())
    if locked.get("reference_head") != REFERENCE_HEAD or locked.get("native_sources") != native:
        raise ValueError("Native source closure differs from the reviewed PR67 lock")
    for item in plan["modules"].values():
        if digest(source_path(item, root, project)) != item["sha256"]:
            raise ValueError("Source changed while preparing component graph")


def download(url, destination, limit):
    """Never print redirect locations or exception URLs."""
    if destination.exists():
        return
    temporary = destination.with_name(destination.name + ".download")
    for attempt in range(3):
        temporary.unlink(missing_ok=True)
        try:
            with urllib.request.urlopen(url, timeout=120) as response, temporary.open("xb") as output:
                count = 0
                while chunk := response.read(1024 * 1024):
                    count += len(chunk)
                    if count > limit:
                        raise ValueError("Cache download exceeds its size limit")
                    output.write(chunk)
            temporary.replace(destination)
            return
        except (urllib.error.URLError, TimeoutError, OSError):
            temporary.unlink(missing_ok=True)
            if attempt == 2:
                raise RuntimeError("Public signed cache download failed after three attempts") from None
    raise RuntimeError("Cache download did not complete")


def authenticate_index(directory, root):
    directory.mkdir(parents=True, exist_ok=True)
    index_path, signature = directory / "cache.json", directory / "cache.sig"
    download(CACHE["release"] + "cache.json", index_path, 16 * 1024**2)
    download(CACHE["release"] + "cache.sig", signature, 1024)
    key = root / "verifier/standard/build-cache-public.pem"
    if digest(key) != CACHE["public_key_sha256"] or digest(index_path) != CACHE["index_sha256"]:
        raise ValueError("Signed cache index or pinned verification key changed")
    checked = subprocess.run(
        ["openssl", "pkeyutl", "-verify", "-pubin", "-inkey", str(key), "-rawin",
         "-in", str(index_path), "-sigfile", str(signature)],
        capture_output=True, timeout=15,
    )
    if checked.returncode:
        raise ValueError("Server compilation-cache signature did not verify")
    index = json.loads(index_path.read_text())
    expected = {
        "schema_version": 1, "sha256": CACHE["archive_sha256"], "size": CACHE["size"],
        "archive": CACHE["archive_sha256"] + ".tar.gz", "source_head": CACHE["source_head"],
        "environment": CACHE["environment"], "compiler": CACHE["compiler"],
    }
    if any(index.get(name) != value for name, value in expected.items()):
        raise ValueError("Signed compilation-cache identity differs from its explicit pins")
    return index


def prepare_environment(root):
    environment = Path(os.environ.get("QRH_WORKER_ROOT", root / "verification/environment")).resolve()
    source = environment / "lean-4.34.1-linux"
    lean = source / "bin/lean"
    if not lean.is_file() or digest(lean) != CACHE["compiler"]:
        raise ValueError("Pinned Lean 4.34.1 is missing; run original setup.py --warm-cache")
    libraries = sorted(
        path.resolve() for path in (environment / "project/.lake/packages").glob("*/.lake/build/lib/lean")
        if path.is_dir()
    )
    if not libraries:
        raise ValueError("Pinned package libraries are missing")
    products = (".olean", ".olean.private", ".olean.server", ".so", ".ir", ".ir.sig")
    inventory = {}
    for library in libraries:
        for path in sorted(library.rglob("*")):
            if path.name.endswith(products):
                if path.is_symlink() or not path.is_file():
                    raise ValueError("Nonregular pinned library product")
                inventory[str(path)] = digest(path)
    tools = json.loads((root / "verification/tool-pins.json").read_text())
    if tools.get("source_lean") != CACHE["compiler"]:
        raise ValueError("Setup compiler receipt differs from the pinned source tool")
    return lean, libraries, inventory, tools


def compile_component(root, project, work, plan, *, pack_products):
    sys.path.insert(0, str(root / "verifier"))
    from standard.build_cache import build_inputs, compatibility_error, restore_cache, pack_cache
    from standard.compile import compile_modules, publish_module
    from worker_resources import worker_threads

    lean, libraries, inventory, tools = prepare_environment(root)
    modules = plan["modules"]
    contract = {
        "schema_version": 2, "component_only": True, "endpoint_proved": False,
        "source_reference_head": REFERENCE_HEAD, "build_order": plan["order"],
        "module_dependencies": {name: item["dependencies"] for name, item in modules.items()},
        "source_files": {"src/" + name.replace(".", "/") + ".lean": item["sha256"]
                         for name, item in modules.items()},
    }
    save(work / "contract.json", contract)
    profile = {"libraries": list(map(str, libraries))}
    inputs = build_inputs(contract, profile, inventory, tools)
    save(work / "build-inputs.json", inputs)
    download_directory = root / "verification/component-cache-download"
    index = authenticate_index(download_directory, root)
    if reason := compatibility_error(index, inputs):
        raise ValueError(reason + "; baseline rebuild is disabled")
    baseline_modules = {name for name in plan["order"] if name.startswith(BASELINE_PREFIX)}
    missing = sorted(name for name in baseline_modules if index["modules"].get(name) != inputs["modules"][name])
    if missing:
        save(work / "cache-status.json", {"status": "incompatible", "missing_dependency_modules": missing})
        raise ValueError(f"{len(missing)} OpenAI baseline dependencies lack a source-matching signed product; baseline rebuild is disabled")

    archive = download_directory / index["archive"]
    print("Compiler, package libraries and every OpenAI baseline source key match the signed archive", flush=True)
    download(CACHE["release"] + index["archive"], archive, index["size"])
    if archive.stat().st_size != index["size"] or digest(archive) != index["sha256"]:
        raise ValueError("Authenticated compilation archive checksum or size differs")
    save(download_directory / "authenticated.json", {"sha256": index["sha256"], "index_sha256": CACHE["index_sha256"]})
    candidate = work / "candidate-lib"
    if candidate.exists():
        raise ValueError("Component output directory already exists; use a fresh worker directory")
    restored = restore_cache(archive, candidate, inputs)
    if not baseline_modules <= restored:
        raise ValueError("Signed cache restore did not supply every OpenAI baseline module")
    save(work / "cache-status.json", {
        "status": "authenticated source-matching hit", "environment": inputs["environment"],
        "source_head": index["source_head"], "archive_sha256": index["sha256"],
        "restored_modules": len(restored), "required_baseline_modules": len(baseline_modules),
    })

    source = work / "source/src"
    for name, item in modules.items():
        original = source_path(item, root, project)
        if digest(original) != item["sha256"]:
            raise ValueError("Source input changed before compilation")
        output = source / (name.replace(".", "/") + ".lean")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(original.read_bytes())
        output.chmod(0o444)
    order = [name for name in plan["order"] if name not in restored]
    if any(not name.startswith(FRESH_PREFIXES) for name in order):
        raise ValueError("Refusing to compile a dependency outside the explicitly locked Candidate/Akash component")
    dependencies = {name: [dep for dep in modules[name]["dependencies"] if dep not in restored] for name in order}
    jobs = worker_threads()
    jobs = min(jobs, 4)
    timings, timing_lock = {}, threading.Lock()
    logs = work / "logs"
    logs.mkdir(exist_ok=True)
    base_env = {
        "PATH": str(lean.parent) + ":/usr/bin:/bin", "LANG": "C.UTF-8",
        "LEAN_ABORT_ON_PANIC": "1", "LEAN_PATH": ":".join(map(str, [candidate, *libraries])),
    }

    def compile_one(name, threads):
        scratch = work / "compilers" / name
        if scratch.exists():
            shutil.rmtree(scratch)
        for part in ["out", "home", "tmp"]:
            (scratch / part).mkdir(parents=True, exist_ok=True)
        output = scratch / "out/module.olean"
        env = {**base_env, "HOME": str(scratch / "home"), "TMPDIR": str(scratch / "tmp")}
        start = time.monotonic()
        print(f"Compile {name} ({threads} Lean threads)", flush=True)
        try:
            result = subprocess.run(
                [str(lean), f"-j{threads}", "-o", str(output), name.replace(".", "/") + ".lean"],
                cwd=source, env=env, text=True, capture_output=True, timeout=1800,
            )
        except subprocess.TimeoutExpired:
            raise RuntimeError("Component module exceeded 1800 seconds: " + name) from None
        transcript = log_text(result.stdout + "\n" + result.stderr, root, project, work)
        (logs / (name + ".log")).write_text(transcript)
        if result.returncode or re.search(r"sorryAx|declaration uses ['’]?sorry", transcript):
            raise RuntimeError(f"Component module failed: {name}\n" + transcript[-5000:])
        publish_module(output, candidate / (name.replace(".", "/") + ".olean"))
        with timing_lock:
            timings[name] = round(time.monotonic() - start, 3)
            save(work / "compile-progress.json", timings)
        print(f"Compiled {name} in {time.monotonic() - start:.1f}s", flush=True)
        shutil.rmtree(scratch)

    print(f"Reused {len(restored)} signed modules; compiling {len(order)} component-closure modules with {jobs} workers", flush=True)
    compile_modules(order, dependencies, compile_one, jobs=jobs)
    audit = source / "ComponentAxiomAudit.lean"
    audit.write_text(f"import {TARGET}\n#print axioms {DECLARATION}\n")
    result = subprocess.run([str(lean), f"-j{jobs}", str(audit)], cwd=source,
                            env={**os.environ, **base_env}, text=True, capture_output=True, timeout=300)
    transcript = log_text(result.stdout + "\n" + result.stderr, root, project, work)
    (work / "axioms.log").write_text(transcript)
    match = re.search(re.escape(DECLARATION) + r"' depends on axioms:\s*\[([^\]]*)\]", transcript)
    if result.returncode or not match:
        raise ValueError("Component axiom audit did not complete")
    axioms = {name.strip() for name in match.group(1).split(",") if name.strip()}
    if not axioms <= STANDARD_AXIOMS:
        raise ValueError("Component contains a forbidden axiom: " + ", ".join(sorted(axioms - STANDARD_AXIOMS)))
    if digest(lean) != CACHE["compiler"] or any(digest(Path(name)) != expected for name, expected in inventory.items()):
        raise ValueError("Pinned compiler or library products changed during the component check")
    if any(digest(source_path(item, root, project)) != item["sha256"] for item in modules.values()):
        raise ValueError("Reviewed source inputs changed during the component check")
    if pack_products:
        products = work / "component-products"
        products.mkdir()
        shutil.copytree(candidate / "Candidate", products / "Candidate")
        akash = candidate / "Submissions/akashlevy_20261009_weighted_numerator"
        if akash.exists():
            shutil.copytree(akash, products / "Submissions/akashlevy_20261009_weighted_numerator")
        component_inputs = {**inputs, "modules": {name: key for name, key in inputs["modules"].items()
                                                 if name.startswith(FRESH_PREFIXES)}}
        pack_cache(products, work / "candidate-products.tar.gz", component_inputs)
        shutil.rmtree(products)
    return {
        "status": "PASS", "component_only": True, "endpoint_proved": False,
        "tracker_admission_claimed": False, "full_replay": False, "kernels_replayed": [],
        "target": TARGET, "declaration": DECLARATION, "axioms": sorted(axioms),
        "source_reference_head": REFERENCE_HEAD, "compiler_sha256": tools["source_lean"],
        "environment": inputs["environment"], "archive_sha256": index["sha256"],
        "required_modules": len(plan["order"]), "restored_modules": len(restored),
        "compiled_component_modules": len(order), "compile_seconds_sum": round(sum(timings.values()), 3),
        "source_lock_sha256": digest(project / "source-lock.json"),
        "target_source_sha256": modules[TARGET]["sha256"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, default=PROJECT.parents[1])
    parser.add_argument("--work", type=Path)
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--write-source-lock", action="store_true")
    parser.add_argument("--no-pack-products", action="store_true")
    args = parser.parse_args()
    root = args.repository_root.resolve()
    project = PROJECT
    work = (args.work or root / "verification/component-check").resolve()
    work.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    try:
        plan = make_plan(root, project)
        check_source_lock(plan, root, project, refresh=args.write_source_lock)
        save(work / "plan.json", plan)
        candidate_count = sum(name.startswith("Candidate.") for name in plan["order"])
        print(f"Component closure: {candidate_count} Candidate modules and {len(plan['order']) - candidate_count} submission dependencies", flush=True)
        if args.plan_only:
            save(work / "report.json", {"status": "PLANNED", "component_only": True,
                                       "endpoint_proved": False, "typecheck_complete": False})
            return
        if platform.system() != "Linux" or platform.machine() != "x86_64" or sys.flags.optimize:
            raise ValueError("Use unoptimized Python on Linux x86_64")
        report = compile_component(root, project, work, plan, pack_products=not args.no_pack_products)
    except Exception as error:
        report = {"status": "FAIL", "component_only": True, "endpoint_proved": False,
                  "reason": log_text(str(error), root, project, work), "error_type": type(error).__name__}
        save(work / "report.json", report)
        raise
    report["checked_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    report["elapsed_seconds"] = round(time.monotonic() - start, 3)
    save(work / "report.json", report)
    print("Source component PASS with only standard axioms; no endpoint or tracker admission is claimed", flush=True)


if __name__ == "__main__":
    main()
