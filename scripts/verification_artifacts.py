"""Generate snapshot certificates and diagnostics for verification checks."""

import json
from pathlib import Path
import re

from scripts.verification_gate import certification_passes


def certificate_for(report):
    """Build a certificate when every acceptance condition passes."""
    if not certification_passes(report):
        return None
    for key in ("source_sha256", "configuration_sha256"):
        hashes = report.get(key)
        if (not isinstance(hashes, dict) or not hashes
                or any(not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value)
                       for value in hashes.values())):
            return None
    lock = report.get("dependency_lock_sha256")
    if not isinstance(lock, str) or not re.fullmatch(r"[0-9a-f]{64}", lock):
        return None
    return {
        "schema_version": 1,
        "kind": "lean_kernel_checked_snapshot",
        "issued_utc": report["recorded_utc"],
        "scope": {
            "principal_theorems": report["main_targets"],
            "required_supporting_theorems": report["supporting_targets"],
            "meaning": "The listed formal declarations and their dependencies passed the "
                       "build, axiom, environment, dependency and exact-snapshot review checks.",
        },
        "module_count": report.get("module_count"),
        "theorem_declarations": report.get("theorem_declarations"),
        "axioms": report.get("axioms", []),
        "clean_rebuild": report.get("clean_rebuild_requested", False),
        "source_sha256": report["source_sha256"],
        "configuration_sha256": report["configuration_sha256"],
        "dependency_lock_sha256": lock,
        "review_receipts_match": report["reviews_match"],
        "signed": False,
    }


def findings_for(report):
    """Summarize completed checks as typed diagnostic findings."""
    findings = []
    stage = report.get("failed_stage")
    if stage:
        kinds = {
            "preflight": "source_or_configuration_failure",
            "imports": "import_integrity_failure",
            "tests": "verification_tooling_failure",
            "environment": "environment_failure",
            "build": "formal_proof_build_failure",
        }
        findings.append({"kind": kinds.get(stage, "verification_failure"),
                         "evidence": report.get("status", stage)})
    unexpected = report.get("unexpected_axioms", [])
    if unexpected:
        findings.append({"kind": "proof_integrity_flaw", "unexpected_axioms": unexpected,
                         "evidence": "A checked declaration depends on an unpermitted axiom; "
                                     "this may include an admitted proof (sorryAx)."})
    if report.get("build_passed") is True and report.get("axiom_audit_passed") is False:
        findings.append({"kind": "axiom_audit_failure",
                         "evidence": "The transitive Lean axiom audit did not pass. "
                                     "Inspect verification/logs/axioms.log for the rejected check."})
    targets = report.get("targets_present", {})
    missing = [name for name, present in targets.items() if present is not True]
    if missing:
        findings.append({"kind": "missing_required_theorems", "declarations": missing,
                         "evidence": "Required formal coverage is incomplete."})
    if report.get("build_passed") and report.get("route_dependencies_passed") is False:
        findings.append({"kind": "proof_dependency_failure",
                         "evidence": "A required declaration or substantive proof dependency "
                                     "was not established by the audit."})
    if report.get("build_passed") and report.get("snapshots_stable") is False:
        if report.get("snapshot_error"):
            findings.append({"kind": "source_snapshot_failure", "evidence": report["snapshot_error"]})
        else:
            findings.append({"kind": "snapshot_changed",
                             "evidence": "Sources or configuration changed during verification."})
    reviews = report.get("reviews_match", {})
    if reviews and not all(value is True for value in reviews.values()):
        findings.append({"kind": "review_incomplete_or_stale",
                         "reviews": reviews,
                         "evidence": "Approval of the exact current snapshot is missing, "
                                     "malformed or stale."})
    return {"schema_version": 1, "recorded_utc": report["recorded_utc"],
            "status": report.get("status", "verification_in_progress"),
            "certificate_issued": certificate_for(report) is not None,
            "findings": findings,
            "mathematical_counterexample_inferred": False}


def _write_json(path, value):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def write_artifacts(evidence, report):
    """Remove stale certificates on any non-passing or unfinished run."""
    evidence = Path(evidence)
    evidence.mkdir(parents=True, exist_ok=True)
    certificate = certificate_for(report)
    _write_json(evidence / "diagnostics.json", findings_for(report))
    destination = evidence / "certificate.json"
    if certificate is None:
        destination.unlink(missing_ok=True)
    else:
        _write_json(destination, certificate)
