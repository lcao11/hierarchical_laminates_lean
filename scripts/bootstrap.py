#!/usr/bin/env python3
"""Install or verify the pinned project-local macOS arm64 environment."""

import argparse
from datetime import datetime, timezone
import json
import os
import platform
import subprocess
import sys
import tarfile

from fetch_dependencies import fetch_dependencies
from materialize_dependencies import materialize_dependencies
from setup_common import ROOT, checked_archive, extract_source, link_source, run, sha256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="Verify the cached setup without network access")
    parser.add_argument("--cache", action="store_true", help="Also fetch compiled mathlib imports")
    args = parser.parse_args()
    if args.offline and args.cache:
        parser.error("--offline and --cache cannot be combined")
    if platform.system() != "Darwin" or platform.machine() != "arm64":
        parser.error("This bootstrap is pinned to macOS arm64; see SETUP.md for other platforms")
    if sys.version_info < (3, 12):
        parser.error("Python 3.12 or newer is required for safe source archive extraction")
    lock = json.loads((ROOT / "dependency-lock.json").read_text())
    if (ROOT / "lean-toolchain").read_text().strip() != lock["lean"]:
        raise RuntimeError("lean-toolchain differs from dependency-lock.json")
    downloads = ROOT / ".tools/downloads"
    downloads.mkdir(parents=True, exist_ok=True)
    elan = lock["elan_installer"]
    installer_archive = checked_archive(elan["url"], elan["sha256"], downloads / "elan.tar.gz", args.offline)
    compiler = lock["compiler_archive"]
    compiler_archive = downloads / compiler["url"].rsplit("/", 1)[1]
    if not compiler_archive.exists() and not args.offline:
        subprocess.run([sys.executable, str(ROOT / "scripts/download_toolchain.py")], check=True)
    checked_archive(compiler["url"], compiler["sha256"], compiler_archive, args.offline)
    if compiler_archive.stat().st_size != compiler["size"]:
        raise RuntimeError("Compiler archive size differs from the pin")

    elan_root = ROOT / ".tools/elan"
    env = dict(os.environ, ELAN_HOME=str(elan_root))
    if not (elan_root / "bin/elan").exists():
        installer_dir = downloads / "elan-installer"
        installer_dir.mkdir(exist_ok=True)
        with tarfile.open(installer_archive) as tar:
            tar.extractall(installer_dir, filter="data")
        subprocess.run([str(installer_dir / "elan-init"), "-y", "--no-modify-path",
                        "--default-toolchain", "none"], env=env, check=True)
    elan_version = run([str(elan_root / "bin/elan"), "--version"], ROOT, env=env).stdout.strip()
    if not elan_version.startswith("elan " + elan["version"].removeprefix("v") + " "):
        raise RuntimeError("Existing local elan version differs from its pin; preserved")
    toolchain_name = compiler_archive.name.removesuffix(".tar.zst")
    toolchain = ROOT / ".tools/toolchain" / toolchain_name
    if not toolchain.exists():
        toolchain.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["tar", "-xf", str(compiler_archive), "-C", str(toolchain.parent)], check=True)
    if not (toolchain / "bin/lean").is_file():
        raise RuntimeError("Extracted compiler binary missing")
    elan_link = elan_root / "toolchains" / lock["lean"].replace("/", "--").replace(":", "---")
    if elan_link.exists() or elan_link.is_symlink():
        if elan_link.resolve() != toolchain.resolve():
            raise RuntimeError("Existing local toolchain link differs; preserved")
    else:
        subprocess.run([str(elan_root / "bin/elan"), "toolchain", "link", lock["lean"],
                        str(toolchain)], env=env, check=True)

    mathlib = lock["mathlib"]
    archive = checked_archive(mathlib["archive_url"], mathlib["archive_sha256"],
                              downloads / "mathlib-source.tar.gz", args.offline)
    source = extract_source(archive, ROOT / ".tools/sources")
    link_source(ROOT / mathlib["local_path"], source)
    fetch_dependencies(args.offline)
    materialize_dependencies(args.offline)
    if args.cache:
        subprocess.run([sys.executable, str(ROOT / "scripts/get_cache.py")], check=True)
    version = run([str(ROOT / "bin/lake"), "env", "lean", "--version"], ROOT).stdout.strip()
    if "version " + lock["lean"].split(":v", 1)[1] + "," not in version:
        raise RuntimeError("Installed compiler reports a different version")
    report = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "status": "Pinned local environment verified",
        "offline": args.offline,
        "dependency_lock_sha256": sha256(ROOT / "dependency-lock.json"),
        "compiler_archive_sha256": compiler["sha256"],
        "lean_version": version,
        "elan_version": elan_version,
        "mathlib_revision": mathlib["revision"],
        "supporting_packages_verified": sorted(lock["transitive_packages"]),
        "global_profile_or_toolchain_changed": False,
    }
    (ROOT / "verification/logs").mkdir(parents=True, exist_ok=True)
    (ROOT / "verification/logs/bootstrap.json").write_text(json.dumps(report, indent=2) + "\n")
    print(version)
    print("Pinned project-local environment verified")


if __name__ == "__main__":
    main()
