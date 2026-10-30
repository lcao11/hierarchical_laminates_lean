#!/usr/bin/env python3
"""Test archive checksums and preservation of edited sources and package links."""

from pathlib import Path
import hashlib
import io
import tarfile
import tempfile

from setup_common import checked_archive, extract_source, link_source


def expect_refusal(action):
    try:
        action()
    except RuntimeError:
        return
    raise AssertionError("Setup accepted an unexpected dependency state")


with tempfile.TemporaryDirectory(prefix="hierarchical-laminates-setup-check-") as temporary:
    work = Path(temporary)
    archive = work / "fixture.tar.gz"
    original = b"pinned source\n"
    with tarfile.open(archive, "w:gz") as tar:
        info = tarfile.TarInfo("fixture/source.txt")
        info.size = len(original)
        tar.addfile(info, io.BytesIO(original))
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    checked_archive("https://invalid.example/unused", digest, archive, offline=True)
    before = archive.read_bytes()
    expect_refusal(lambda: checked_archive("https://invalid.example/unused", "0" * 64,
                                           archive, offline=True))
    assert archive.read_bytes() == before
    source = extract_source(archive, work / "sources")
    edited = b"local edits must survive\n"
    (source / "source.txt").write_bytes(edited)
    expect_refusal(lambda: extract_source(archive, work / "sources"))
    assert (source / "source.txt").read_bytes() == edited
    package = work / "packages/fixture"
    link_source(package, source)
    other = work / "other"
    other.mkdir()
    expect_refusal(lambda: link_source(package, other))
    assert package.resolve() == source.resolve()
print("PASS: checksum refusal, edit preservation, and unexpected-link preservation")
