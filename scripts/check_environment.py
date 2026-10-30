#!/usr/bin/env python3
"""Check the installed compiler and dependency sources against the lock."""

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {' '.join(map(str, command))}\n"
                           + result.stdout)
    return result.stdout.strip()


def check_compiler_version(output, pin):
    expected = pin.rsplit(":v", 1)[1]
    match = re.search(r"\bversion\s+([^,\s)]+)", output)
    if match is None or match[1] != expected:
        raise RuntimeError(f"Compiler differs from pinned Lean {expected}: {output}")
    return match[1]


def check_git_pin(path, revision):
    """Require the exact commit and unmodified dependency sources."""
    path = Path(path)
    if not path.is_dir():
        raise RuntimeError("Missing pinned dependency: " + str(path))
    actual = run(["git", "rev-parse", "HEAD"], path)
    if actual != revision:
        raise RuntimeError(f"Dependency revision differs at {path}: {actual}")
    tracked = run(["git", "status", "--porcelain", "--untracked-files=no"], path)
    if tracked:
        raise RuntimeError("Edited tracked dependency files preserved: " + str(path))
    untracked = run(["git", "ls-files", "--others", "--exclude-standard"], path).splitlines()
    source_suffixes = {".lean", ".toml", ".json", ".py", ".sh"}
    unexpected = [name for name in untracked if Path(name).suffix in source_suffixes]
    if unexpected:
        raise RuntimeError(f"Untracked dependency source files preserved at {path}: {unexpected}")
    return {"revision": actual, "tracked_sources_clean": True}


def check_standard_dependencies(root, lock):
    mathlib = root / lock["mathlib"]["local_path"]
    checked = {"mathlib": check_git_pin(mathlib, lock["mathlib"]["revision"])}
    manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    expected = lock["transitive_packages"]
    entries = {entry["name"]: entry for entry in manifest["packages"]}
    if set(entries) != set(expected):
        raise RuntimeError("Mathlib's supporting package set differs from the dependency lock")
    for name, pinned in sorted(expected.items()):
        entry = entries[name]
        if entry.get("type") != "git" or entry.get("rev") != pinned["revision"]:
            raise RuntimeError("Mathlib's supporting dependency pin differs: " + name)
        checked[name] = check_git_pin(root / pinned["local_path"], pinned["revision"])
    return checked


def main():
    lock_path = ROOT / "dependency-lock.json"
    lock = json.loads(lock_path.read_text())
    if (ROOT / "lean-toolchain").read_text().strip() != lock["lean"]:
        raise RuntimeError("lean-toolchain differs from dependency-lock.json")
    local_runtime = (ROOT / ".tools/elan/bin/lake").is_file()
    if local_runtime:
        # The offline bootstrap checks archive checksums and pinned source files.
        result = subprocess.run([sys.executable, str(ROOT / "scripts/bootstrap.py"), "--offline"],
                                cwd=ROOT)
        if result.returncode:
            return result.returncode
        mode = "isolated-local"
        dependencies = {"verification": "offline bootstrap checked pinned archives and sources"}
    else:
        if shutil.which("lake") is None or shutil.which("git") is None:
            raise RuntimeError("Standard setup requires lake and git on PATH; see SETUP.md")
        mode = "standard-installed"
        dependencies = check_standard_dependencies(ROOT, lock)
    version_output = run([str(ROOT / "bin/lake"), "env", "lean", "--version"])
    version = check_compiler_version(version_output, lock["lean"])
    report = {
        "mode": mode,
        "lean_version": version,
        "lean_version_output": version_output,
        "dependency_lock_sha256": hashlib.sha256(lock_path.read_bytes()).hexdigest(),
        "dependencies": dependencies,
        "network_used": False,
        "global_configuration_changed": False,
    }
    logs = ROOT / "verification/logs"
    logs.mkdir(parents=True, exist_ok=True)
    (logs / "environment.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {mode} environment: Lean {version}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
