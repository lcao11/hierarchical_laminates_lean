#!/usr/bin/env python3
"""Fetch pinned mathlib artifacts for the imports used by the proof modules."""

from pathlib import Path
import re
import subprocess


root = Path(__file__).resolve().parents[1]
targets = sorted({match.group(1)
    for path in (root / "HierarchicalLaminates").rglob("*.lean")
    for match in re.finditer(r"^(?:public\s+)?import\s+(Mathlib\.[\w.]+)",
                             path.read_text(), re.MULTILINE)})
(root / "verification/logs").mkdir(parents=True, exist_ok=True)
(root / "verification/logs/cache_targets.txt").write_text("\n".join(targets) + "\n")
print(f"Preparing compiled cache for {len(targets)} selected imports", flush=True)
with (root / "verification/logs/cache.log").open("w") as log:
    result = subprocess.run([str(root / "bin/lake"), "exe", "cache", "get", *targets],
                            cwd=root, stdout=log, stderr=subprocess.STDOUT)
print(f"Cache preparation exit code: {result.returncode}; see verification/logs/cache.log", flush=True)
raise SystemExit(result.returncode)
