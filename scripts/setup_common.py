"""Checked local setup operations shared by the bootstrap commands."""

from pathlib import Path
import hashlib
import os
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def checked_archive(url, expected, path, offline=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        if offline:
            raise RuntimeError(f"Offline setup needs the cached archive: {path.name}")
        temporary = path.with_name(path.name + ".partial")
        subprocess.run([
            "curl", "--fail", "--location", "--silent", "--show-error",
            "--retry", "3", "--retry-all-errors", "--connect-timeout", "20",
            "--max-time", "600", url, "--output", str(temporary),
        ], check=True)
        if sha256(temporary) != expected:
            raise RuntimeError(f"Downloaded archive checksum mismatch: {path.name}")
        temporary.replace(path)
    if sha256(path) != expected:
        raise RuntimeError(f"Cached archive checksum mismatch: {path.name}")
    return path


def extract_source(archive, sources):
    """Extract a new checked source archive, or verify existing files in place."""
    sources = Path(sources)
    sources.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        prefixes = {Path(member.name).parts[0] for member in members}
        if len(prefixes) != 1:
            raise RuntimeError(f"Expected one archive root: {archive}")
        prefix = prefixes.pop()
        if prefix in {"", ".", ".."} or "/" in prefix:
            raise RuntimeError("Unsafe source archive root")
        destination = sources / prefix
        if not destination.exists():
            tar.extractall(sources, filter="data")
        else:
            for member in members:
                relative = Path(member.name).relative_to(prefix)
                if ".." in relative.parts:
                    raise RuntimeError("Unsafe source archive path")
                current = destination / relative
                if member.isfile():
                    if not current.is_file() or current.is_symlink():
                        raise RuntimeError(f"Existing dependency file missing or replaced: {current}")
                    with tar.extractfile(member) as original:
                        expected = hashlib.file_digest(original, "sha256").hexdigest()
                    if sha256(current) != expected:
                        raise RuntimeError(f"Existing dependency has edits; preserved: {current}")
                elif member.issym():
                    if not current.is_symlink() or os.readlink(current) != member.linkname:
                        raise RuntimeError(f"Existing dependency symlink differs; preserved: {current}")
    return destination


def link_source(package, source):
    package, source = Path(package), Path(source)
    package.parent.mkdir(parents=True, exist_ok=True)
    if package.is_symlink():
        if package.resolve() != source.resolve():
            raise RuntimeError(f"Unexpected package link; preserved: {package}")
    elif package.exists():
        raise RuntimeError(f"Expected an isolated package symlink; preserved: {package}")
    else:
        package.symlink_to(os.path.relpath(source, package.parent), target_is_directory=True)


def run(args, cwd, check=True, env=None):
    return subprocess.run(args, cwd=cwd, check=check, env=env,
                          capture_output=True, text=True, timeout=240)
