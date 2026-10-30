#!/usr/bin/env python3
"""Download the official pinned compiler in checked, resumable byte ranges."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time


root = Path(__file__).resolve().parents[1]
download_dir = root / ".tools" / "downloads"
lock = json.loads((root / "dependency-lock.json").read_text())["compiler_archive"]
asset = {"name": lock["url"].rsplit("/", 1)[1], "size": lock["size"],
         "browser_download_url": lock["url"], "digest": "sha256:" + lock["sha256"]}
size = asset["size"]
destination = download_dir / asset["name"]
if destination.exists():
    with destination.open("rb") as existing:
        observed = hashlib.file_digest(existing, "sha256").hexdigest()
    if observed != lock["sha256"] or destination.stat().st_size != size:
        raise RuntimeError("Existing compiler archive checksum mismatch; preserved")
    print("Pinned compiler archive already verified", flush=True)
    raise SystemExit(0)
chunk_size = 16 * 1024 * 1024
parts = download_dir / "compiler-parts"
parts.mkdir(exist_ok=True)


def fetch(start):
    end = min(start + chunk_size, size) - 1
    part = parts / f"{start:012d}.part"
    expected = end - start + 1
    if part.exists() and part.stat().st_size == expected:
        return start
    failures = 0
    while not part.exists() or part.stat().st_size < expected:
        present = part.stat().st_size if part.exists() else 0
        begin = start + present
        request_end = min(end, begin + 4 * 1024 * 1024 - 1)
        temporary = parts / f"{start:012d}.next"
        headers = parts / f"{start:012d}.headers"
        temporary.unlink(missing_ok=True)
        url = asset["browser_download_url"] + f"?hierarchical_laminates_range={begin}"
        result = subprocess.run([
            "curl", "--fail", "--location", "--silent", "--show-error",
            "--connect-timeout", "20", "--max-time", "120",
            "--range", f"{begin}-{request_end}", "--dump-header", str(headers),
            "--output", str(temporary), url,
        ], capture_output=True, text=True)
        matches = re.findall(r"content-range:\s*bytes\s+(\d+)-(\d+)/(\d+)",
                             headers.read_text().lower() if headers.exists() else "")
        valid = matches and int(matches[-1][0]) == begin and int(matches[-1][2]) == size
        received = temporary.stat().st_size if temporary.exists() else 0
        if valid and 0 < received <= request_end - begin + 1:
            with part.open("ab") as out:
                out.write(temporary.read_bytes())
            temporary.unlink()
            failures = 0
        else:
            failures += 1
            if failures >= 12:
                raise RuntimeError(f"Compiler range {begin} repeatedly failed: {result.stderr}")
            time.sleep(1)
    if part.stat().st_size != expected:
        raise RuntimeError(f"Wrong byte count for compiler chunk {start}")
    return start


starts = list(range(0, size, chunk_size))
with ThreadPoolExecutor(max_workers=8) as pool:
    for count, result in enumerate(as_completed([pool.submit(fetch, s) for s in starts]), 1):
        result.result()
        print(f"Compiler download: {count}/{len(starts)} checked chunks", flush=True)

assembled = destination.with_name(destination.name + ".assembling")
digest = hashlib.sha256()
with assembled.open("wb") as out:
    for start in starts:
        with (parts / f"{start:012d}.part").open("rb") as part:
            while block := part.read(1024 * 1024):
                digest.update(block)
                out.write(block)
if assembled.stat().st_size != size:
    raise RuntimeError("Assembled compiler byte count mismatch")
observed = "sha256:" + digest.hexdigest()
if observed != asset["digest"]:
    raise RuntimeError("Compiler archive digest mismatch")
assembled.replace(destination)
print(f"Compiler archive complete: {size} bytes, {observed}", flush=True)
