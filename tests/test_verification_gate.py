"""Regression tests for verification acceptance, snapshots, imports and setup."""

from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import hashlib
import json
import subprocess
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import current_snapshot
import verify
from scripts.check_environment import check_compiler_version, check_git_pin
from scripts.verification_gate import (
    MAIN_TARGETS, SUPPORTING_TARGETS, REQUIRED_DEPENDENCIES, REVIEW_KINDS,
    SNAPSHOT_KEYS, certification_passes, import_graph_errors, lean_imports,
    proof_checks_pass, reachable, render_audit, review_matches, route_dependencies_match,
)
from scripts.verification_artifacts import certificate_for, findings_for, write_artifacts


class AcceptanceChecks(unittest.TestCase):
    def test_audit_includes_aggregate_and_source_origin(self):
        audit = render_audit(["HierarchicalLaminates.Example", "HierarchicalLaminates"])
        self.assertEqual(audit.splitlines().count("import HierarchicalLaminates"), 1)
        self.assertIn("import HierarchicalLaminates.Example", audit)
        self.assertIn("env.getModuleIdxFor? name", audit)
        self.assertIn('name.toString.startsWith "_private.HierarchicalLaminates."', audit)

    def valid(self):
        return dict(
            environment_passed=True, tests_passed=True, build_passed=True,
            axiom_audit_passed=True, import_graph_passed=True,
            route_dependencies_passed=True, snapshots_stable=True,
            main_targets=list(MAIN_TARGETS),
            supporting_targets=list(SUPPORTING_TARGETS),
            targets_present={t: True for t in (*MAIN_TARGETS, *SUPPORTING_TARGETS)},
            reviews_match={kind: True for kind in REVIEW_KINDS},
            unexpected_axioms=[], import_graph_errors=[],
        )

    def test_complete_report_only(self):
        self.assertTrue(certification_passes(self.valid()))
        for key, value in self.valid().items():
            if value is True:
                changed = self.valid()
                changed[key] = False
                self.assertFalse(certification_passes(changed), key)

    def test_main_statements_and_supporting_bridges_are_required(self):
        for target in (*MAIN_TARGETS, *SUPPORTING_TARGETS):
            changed = self.valid()
            changed["targets_present"][target] = False
            self.assertFalse(certification_passes(changed))
            del changed["targets_present"][target]
            self.assertFalse(certification_passes(changed))

    def test_historical_or_extra_main_statements_cannot_substitute(self):
        for names in [[], ["LegacyProof.full_statement"],
                      [*MAIN_TARGETS, "HierarchicalLaminates.extra"]]:
            changed = self.valid()
            changed["main_targets"] = names
            self.assertFalse(certification_passes(changed))

    def test_unexpected_axiom_or_import_is_rejected(self):
        for key, value in [("unexpected_axioms", ["sorryAx"]),
                           ("import_graph_errors", ["LegacyProof"])]:
            changed = self.valid()
            changed[key] = value
            self.assertFalse(certification_passes(changed))

    def test_all_three_exact_reviews_are_required(self):
        for kind in REVIEW_KINDS:
            changed = self.valid()
            changed["reviews_match"][kind] = False
            self.assertFalse(certification_passes(changed))
            del changed["reviews_match"][kind]
            self.assertFalse(certification_passes(changed))

    def test_stale_review_or_nonboolean_approval_is_rejected(self):
        snapshot = {key: [key] if key.endswith("targets") else {key: "hash"}
                    for key in SNAPSHOT_KEYS}
        review = dict(snapshot, approved=True)
        self.assertTrue(review_matches(review, snapshot))
        for key in SNAPSHOT_KEYS:
            changed = deepcopy(review)
            changed[key] = "changed"
            self.assertFalse(review_matches(changed, snapshot), key)
        self.assertFalse(review_matches(dict(review, approved=1), snapshot))

    def test_malformed_or_incomplete_receipts_are_rejected(self):
        snapshot = {key: [key] if key.endswith("targets") else {key: "hash"}
                    for key in SNAPSHOT_KEYS}
        for review in (None, [], True, 1, "approved", {"approved": True}):
            self.assertFalse(review_matches(review, snapshot), review)
        complete = dict(snapshot, approved=True)
        self.assertFalse(review_matches(complete, {}))
        for key in SNAPSHOT_KEYS:
            incomplete = dict(complete)
            del incomplete[key]
            self.assertFalse(review_matches(incomplete, snapshot), key)

    def test_proof_checks_and_review_completion_are_distinct(self):
        report = self.valid()
        report["reviews_match"] = {}
        self.assertTrue(proof_checks_pass(report))
        self.assertFalse(certification_passes(report))
        report["route_dependencies_passed"] = False
        self.assertFalse(proof_checks_pass(report))

    def test_actual_proof_routes_are_required(self):
        dependencies = deepcopy(REQUIRED_DEPENDENCIES)
        self.assertTrue(route_dependencies_match(dependencies))
        self.assertFalse(route_dependencies_match({}, {}))
        for target, needed in REQUIRED_DEPENDENCIES.items():
            for missing in needed:
                changed = deepcopy(dependencies)
                changed[target] = [x for x in changed[target] if x != missing]
                self.assertFalse(route_dependencies_match(changed), (target, missing))

    def test_dependency_walk_handles_cycles(self):
        self.assertEqual(reachable("a", {"a": ["b"], "b": ["a", "c"], "c": []}),
                         ["a", "b", "c"])

    def certificate_report(self):
        return dict(self.valid(), recorded_utc="2026-10-27T00:00:00+00:00",
                    source_sha256={"proof.lean": "a" * 64},
                    configuration_sha256={"verify.py": "b" * 64},
                    dependency_lock_sha256="c" * 64,
                    axioms=["propext", "Classical.choice", "Quot.sound"])

    def test_certificate_cannot_trust_a_forged_summary_flag(self):
        report = self.certificate_report()
        self.assertIsNotNone(certificate_for(report))
        report.update(certified=True, build_passed=False)
        self.assertIsNone(certificate_for(report))
        report = self.certificate_report()
        report["source_sha256"] = {}
        self.assertIsNone(certificate_for(report))

    def test_failed_run_removes_stale_certificate(self):
        with tempfile.TemporaryDirectory() as directory:
            report = self.certificate_report()
            write_artifacts(directory, report)
            self.assertTrue((Path(directory) / "certificate.json").exists())
            report["reviews_match"]["mathematical"] = False
            write_artifacts(directory, report)
            self.assertFalse((Path(directory) / "certificate.json").exists())
            diagnostics = json.loads((Path(directory) / "diagnostics.json").read_text())
            self.assertFalse(diagnostics["certificate_issued"])
            self.assertIn("review_incomplete_or_stale", [f["kind"] for f in diagnostics["findings"]])

    def test_missing_theorem_and_admission_are_distinct(self):
        report = self.certificate_report()
        report["targets_present"][MAIN_TARGETS[0]] = False
        diagnostics = findings_for(report)
        self.assertIn("missing_required_theorems", [f["kind"] for f in diagnostics["findings"]])
        self.assertNotIn("proof_integrity_flaw", [f["kind"] for f in diagnostics["findings"]])
        report["unexpected_axioms"] = ["sorryAx"]
        diagnostics = findings_for(report)
        self.assertIn("proof_integrity_flaw", [f["kind"] for f in diagnostics["findings"]])
        self.assertFalse(diagnostics["mathematical_counterexample_inferred"])

    def test_environment_failure_is_not_mislabeled_as_a_proof_flaw(self):
        report = self.certificate_report()
        report.update(environment_passed=False, failed_stage="environment", status="Compiler pin mismatch")
        diagnostics = findings_for(report)
        self.assertEqual(diagnostics["findings"][0]["kind"], "environment_failure")
        self.assertFalse(diagnostics["certificate_issued"])

    def test_preflight_exception_invalidates_an_existing_certificate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence = root / "verification"
            evidence.mkdir()
            (evidence / "certificate.json").write_text('{"old": true}\n')
            with (
                patch.object(verify, "ROOT", root),
                patch.object(verify, "current_snapshot", side_effect=ValueError("Invalid source link")),
                patch("builtins.print"),
            ):
                self.assertEqual(verify.main([]), 1)
            self.assertFalse((evidence / "certificate.json").exists())
            diagnostics = json.loads((evidence / "diagnostics.json").read_text())
            self.assertEqual(diagnostics["findings"][0]["kind"], "source_or_configuration_failure")

    def test_pending_checks_do_not_report_observed_failures(self):
        report = self.certificate_report()
        report.update(route_dependencies_passed=None, snapshots_stable=None,
                      axiom_audit_passed=None)
        kinds = [f["kind"] for f in findings_for(report)["findings"]]
        self.assertNotIn("proof_dependency_failure", kinds)
        self.assertNotIn("snapshot_changed", kinds)
        self.assertNotIn("axiom_audit_failure", kinds)
        self.assertIsNone(certificate_for(report))

    def test_audit_failure_without_an_unexpected_axiom_is_reported(self):
        report = self.certificate_report()
        report.update(axiom_audit_passed=False, unexpected_axioms=[])
        self.assertIn("axiom_audit_failure", [f["kind"] for f in findings_for(report)["findings"]])


class ImportChecks(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        (root / "HierarchicalLaminates").mkdir()
        (root / "HierarchicalLaminates.lean").write_text("import HierarchicalLaminates.Core\n")
        (root / "HierarchicalLaminates/Core.lean").write_text("import Mathlib.Data.Real.Basic\n")
        return root

    def test_comment_and_string_imports_are_not_executable(self):
        source = '''/- import LegacyProof /- nested -/ -/
          public import HierarchicalLaminates.Core -- import Old
          def message := "import LegacyProof"
          import Mathlib.Data.Real.Basic
        '''
        self.assertEqual(lean_imports(source),
                         ["HierarchicalLaminates.Core", "Mathlib.Data.Real.Basic"])
        with self.assertRaises(ValueError):
            lean_imports("import «OddName»")

    def test_transitive_noncanonical_imports_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            self.assertEqual(import_graph_errors(["HierarchicalLaminates.Core"], root), [])
            for imported in ["LegacyProof.Counterexample", "AlternativeProof.AllParameters",
                             "DifferentNamespace", "UntrackedProof", "Arbitrary.LocalProof"]:
                (root / "HierarchicalLaminates/Core.lean").write_text("import " + imported)
                self.assertIn("noncanonical import: " + imported,
                              import_graph_errors(["HierarchicalLaminates.Core"], root))

    def test_aggregate_and_missing_sources_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            (root / "HierarchicalLaminates.lean").write_text("import LegacyProof\n")
            self.assertIn("noncanonical import: LegacyProof",
                          import_graph_errors(["HierarchicalLaminates.Core"], root))
            (root / "HierarchicalLaminates.lean").write_text("import HierarchicalLaminates.Absent\n")
            self.assertIn("missing project module: HierarchicalLaminates.Absent",
                          import_graph_errors(["HierarchicalLaminates.Core"], root))

    def test_project_symlink_outside_canonical_tree_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            (root / "external.lean").write_text("module\n")
            (root / "HierarchicalLaminates/Core.lean").unlink()
            (root / "HierarchicalLaminates/Core.lean").symlink_to(root / "external.lean")
            self.assertIn("project source outside canonical tree: HierarchicalLaminates.Core",
                          import_graph_errors(["HierarchicalLaminates.Core"], root))


class GitIgnoreChecks(unittest.TestCase):
    def test_local_runtime_directories_and_symlinks_are_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = base / "proofs"
            root.mkdir()
            external = base / "runtime"
            external.mkdir()
            ignore = Path(__file__).resolve().parents[1] / ".gitignore"
            (root / ".gitignore").write_bytes(ignore.read_bytes())
            subprocess.run(["git", "init", "--quiet"], cwd=root, check=True)
            for name in (".tools", ".lake"):
                path = root / name
                for symlink in (False, True):
                    if symlink:
                        path.symlink_to(external, target_is_directory=True)
                    else:
                        path.mkdir()
                    ignored = subprocess.run(["git", "check-ignore", "--quiet", name], cwd=root)
                    self.assertEqual(ignored.returncode, 0, (name, symlink))
                    status = subprocess.run(
                        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=root,
                        check=True, text=True, stdout=subprocess.PIPE).stdout
                    self.assertNotIn(name, status)
                    if symlink:
                        path.unlink()
                    else:
                        path.rmdir()


class StandaloneSnapshotChecks(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory) / "proofs"
        (root / "HierarchicalLaminates").mkdir(parents=True)
        (root / "bin").mkdir()
        for name in ("HierarchicalLaminates.lean", "lakefile.toml", "lake-manifest.json",
                     "lean-toolchain", "dependency-lock.json", "bin/lake", ".gitignore",
                     "verify.py", "README.md", "SETUP.md", "LICENSE", "CITATION.bib"):
            (root / name).write_text("fixture\n")
        (root / "docs/companion").mkdir(parents=True)
        (root / "docs/companion/proof-exercises.pdf").write_bytes(b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\nfixture\n")
        (root / "HierarchicalLaminates/Core.lean").write_text("theorem test : True := True.intro\n")
        return root

    def test_snapshot_uses_only_repository_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            snapshot = current_snapshot(root)
            self.assertEqual(set(snapshot), set(SNAPSHOT_KEYS))
            self.assertEqual(set(snapshot["source_sha256"]), {"HierarchicalLaminates/Core.lean"})
            self.assertIn("LICENSE", snapshot["configuration_sha256"])
            self.assertIn("CITATION.bib", snapshot["configuration_sha256"])
            pdf = "docs/companion/proof-exercises.pdf"
            self.assertEqual(snapshot["configuration_sha256"][pdf],
                             hashlib.sha256((root / pdf).read_bytes()).hexdigest())
            self.assertTrue(all(not Path(name).is_absolute()
                                for name in snapshot["configuration_sha256"]))
            before = deepcopy(snapshot)
            (root.parent / "unrelated-private-file.txt").write_text("private\n")
            self.assertEqual(current_snapshot(root), before)
            (root / "LICENSE").write_text("updated license\n")
            self.assertNotEqual(current_snapshot(root), before)
            before = current_snapshot(root)
            (root / "CITATION.bib").write_text("updated citation\n")
            self.assertNotEqual(current_snapshot(root), before)
            before = current_snapshot(root)
            (root / pdf).write_bytes((root / pdf).read_bytes() + b"changed\n")
            self.assertNotEqual(current_snapshot(root), before)
            before = current_snapshot(root)
            (root / "README.md").write_text("updated instructions\n")
            self.assertNotEqual(current_snapshot(root), before)

    def test_configuration_cannot_link_outside_the_repository(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            outside = root.parent / "outside.txt"
            outside.write_text("external\n")
            (root / "README.md").unlink()
            (root / "README.md").symlink_to(outside)
            with self.assertRaises(ValueError):
                current_snapshot(root)


class EnvironmentChecks(unittest.TestCase):
    def test_compiler_version_must_equal_the_pin(self):
        pin = "leanprover/lean4:v4.36.0-rc1"
        self.assertEqual(check_compiler_version("Lean (version 4.36.0-rc1, arm64)", pin),
                         "4.36.0-rc1")
        for output in ["Lean (version 4.35.0, arm64)",
                       "Lean (version 4.36.0-rc10, arm64)", "unknown"]:
            with self.assertRaises(RuntimeError):
                check_compiler_version(output, pin)

    def test_dependency_revision_and_tracked_sources_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.run(["git", *args], cwd=root, check=True,
                                      text=True, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT).stdout.strip()
            git("init", "--quiet")
            (root / "Source.lean").write_text("theorem test : True := True.intro\n")
            git("add", "Source.lean")
            git("-c", "user.name=Artifact test", "-c", "user.email=artifact@example.invalid",
                "commit", "--quiet", "-m", "Pinned fixture")
            revision = git("rev-parse", "HEAD")
            self.assertTrue(check_git_pin(root, revision)["tracked_sources_clean"])
            with self.assertRaises(RuntimeError):
                check_git_pin(root, "0" * 40)
            (root / "Source.lean").write_text("axiom changed : False\n")
            with self.assertRaises(RuntimeError):
                check_git_pin(root, revision)


if __name__ == "__main__":
    unittest.main()
