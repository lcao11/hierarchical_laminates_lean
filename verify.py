#!/usr/bin/env python3
"""Build and audit the repository snapshot, then write verification records.

Certification requires passing proof checks and exact-snapshot review approvals.
Records are written to verification/.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from scripts.verification_gate import (
    MAIN_TARGETS, SUPPORTING_TARGETS, REQUIRED_DEPENDENCIES,
    STANDARD_AXIOMS, REVIEW_KINDS, certification_passes, import_graph_errors,
    proof_checks_pass, reachable, render_audit, review_matches,
    route_dependencies_match,
)
from scripts.verification_artifacts import write_artifacts

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_hashes(root=ROOT):
    return {
        str(path.relative_to(root)): digest(path)
        for path in sorted((root / "HierarchicalLaminates").rglob("*.lean"))
    }


def configuration_hashes(root=ROOT):
    names = [
        "HierarchicalLaminates.lean", "lakefile.toml", "lake-manifest.json",
        "lean-toolchain", "dependency-lock.json", "bin/lake", ".gitignore",
        "verify.py", "README.md", "SETUP.md", "LICENSE", "CITATION.bib",
    ]
    paths = [root / name for name in names]
    for folder, pattern in (("scripts", "*.py"), ("tests", "*.py"),
                            ("docs", "*.md"), ("docs", "*.pdf")):
        paths.extend(sorted((root / folder).rglob(pattern)))
    for path in paths:
        if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
            raise ValueError("Configuration must be an ordinary repository file: "
                             + str(path.relative_to(root)))
    return {str(path.relative_to(root)): digest(path) for path in sorted(set(paths))}


def current_snapshot(root=ROOT):
    """Identify exactly the proof, configuration, documentation and dependency lock."""
    return {
        "main_targets": list(MAIN_TARGETS),
        "supporting_targets": list(SUPPORTING_TARGETS),
        "source_sha256": source_hashes(root),
        "configuration_sha256": configuration_hashes(root),
        "dependency_lock_sha256": digest(root / "dependency-lock.json"),
    }


def run_logged(command, destination, root=ROOT):
    with destination.open("w") as output:
        try:
            result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
        except OSError as exc:
            output.write(f"Command could not start: {type(exc).__name__}: {exc}\n")
            return False
    return result.returncode == 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true",
                        help="Remove only this project's compiled proof output before building")
    args = parser.parse_args(argv)
    evidence = ROOT / "verification"
    logs = evidence / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    # Invalidate the previous certificate before source and configuration preflight.
    (evidence / "certificate.json").unlink(missing_ok=True)
    try:
        snapshot = current_snapshot()
        modules = [
            name.removesuffix(".lean").replace("/", ".")
            for name in snapshot["source_sha256"]
        ]
        errors = import_graph_errors(modules, ROOT)
    except (OSError, ValueError) as exc:
        report = {
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "main_targets": list(MAIN_TARGETS),
            "supporting_targets": list(SUPPORTING_TARGETS),
            "certified": False,
            "failed_stage": "preflight",
            "status": f"Source/configuration preflight failed: {type(exc).__name__}: {exc}",
        }
        (evidence / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        write_artifacts(evidence, report)
        print(report["status"])
        return 1
    report = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "artifact": "Current Lean formal proofs",
        **snapshot,
        "modules": modules,
        "module_count": len(modules),
        "clean_rebuild_requested": args.clean,
        "required_proof_dependencies": REQUIRED_DEPENDENCIES,
        "import_graph_errors": errors,
        "import_graph_passed": not errors,
        "environment_passed": None,
        "tests_passed": None,
        "build_passed": None,
        "axiom_audit_passed": None,
        "route_dependencies_passed": None,
        "snapshots_stable": None,
        "certified": False,
    }

    def save():
        (evidence / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        write_artifacts(evidence, report)

    def fail(status, stage):
        report["status"] = status
        report["failed_stage"] = stage
        save()
        print(status)
        return 1

    save()
    if errors:
        return fail("Noncanonical or missing proof imports; see verification/result.json", "imports")
    report["tests_passed"] = run_logged(
        [sys.executable, "tests/test_verification_gate.py"], logs / "tests.log")
    if not report["tests_passed"]:
        return fail("Verification acceptance tests failed; see verification/logs/tests.log", "tests")

    report["environment_passed"] = run_logged(
        [sys.executable, "scripts/check_environment.py"], logs / "environment.log")
    save()
    if not report["environment_passed"]:
        return fail("Pinned setup check failed; see verification/logs/environment.log", "environment")
    environment = json.loads((logs / "environment.json").read_text())
    report["environment"] = {
        key: environment[key] for key in (
            "mode", "lean_version", "dependency_lock_sha256", "dependencies",
            "network_used", "global_configuration_changed",
        )
    }

    if args.clean:
        shutil.rmtree(ROOT / ".lake/build", ignore_errors=True)
    report["build_passed"] = run_logged(
        [str(ROOT / "bin/lake"), "build", "HierarchicalLaminates", *modules],
        logs / "build.log")
    save()
    if not report["build_passed"]:
        return fail("Lean build failed; see verification/logs/build.log", "build")

    audit = logs / "Audit.lean"
    audit.write_text(render_audit(modules))
    audited = run_logged(
        [str(ROOT / "bin/lake"), "env", "lean", str(audit)], logs / "axioms.log")
    entries, graph = [], {}
    for line in (logs / "axioms.log").read_text().splitlines():
        if line.startswith("LEAN_AUDIT "):
            entries.append(json.loads(line.removeprefix("LEAN_AUDIT ")))
        elif line.startswith("LEAN_GRAPH "):
            entry = json.loads(line.removeprefix("LEAN_GRAPH "))
            graph[entry["name"]] = entry["deps"]
    theorem_names = {entry["name"] for entry in entries}
    axioms = set().union(*(set(entry["axioms"]) for entry in entries)) if entries else set()
    unexpected = sorted(axioms - STANDARD_AXIOMS)
    targets = (*MAIN_TARGETS, *SUPPORTING_TARGETS)
    dependencies = {name: reachable(name, graph) for name in targets}
    (logs / "proof_dependencies.json").write_text(json.dumps(dependencies, indent=2) + "\n")
    report.update(
        theorem_declarations=len(entries),
        axioms=sorted(axioms),
        unexpected_axioms=unexpected,
        axiom_audit_passed=audited and bool(entries) and not unexpected,
        targets_present={name: name in theorem_names for name in targets},
        route_dependencies_passed=route_dependencies_match(dependencies),
    )

    try:
        report["snapshots_stable"] = current_snapshot() == snapshot
    except (OSError, ValueError) as exc:
        report["snapshots_stable"] = False
        report["snapshot_error"] = f"{type(exc).__name__}: {exc}"
    reviews_match, review_errors = {}, {}
    for kind in REVIEW_KINDS:
        path = evidence / "reviews" / (kind + "_review.json")
        try:
            review = json.loads(path.read_text()) if path.exists() else {}
        except (OSError, ValueError) as exc:
            review = {}
            review_errors[kind] = type(exc).__name__
        reviews_match[kind] = review_matches(review, snapshot)
    report["reviews_match"] = reviews_match
    report["review_load_errors"] = review_errors
    report["certified"] = certification_passes(report)
    report["status"] = (
        "The principal declarations and required supporting results are certified"
        if report["certified"]
        else "Proof checks completed; certification awaits all acceptance conditions"
    )
    save()
    print(report["status"])
    print(f"Built {len(modules)} modules; audited {len(entries)} theorem declarations")
    if report["certified"]:
        print("Snapshot certificate: verification/certificate.json")
        return 0
    return 2 if proof_checks_pass(report) else 1


if __name__ == "__main__":
    raise SystemExit(main())
