#!/usr/bin/env python3
"""Verify and fetch mathlib's exact locked supporting source archives."""

from concurrent.futures import ThreadPoolExecutor
import argparse
import json
from urllib.parse import urlparse

from setup_common import ROOT, checked_archive, extract_source, link_source


def fetch_dependencies(offline=False):
    mathlib = ROOT / '.lake/packages/mathlib'
    manifest = json.loads((mathlib / 'lake-manifest.json').read_text())
    lock = json.loads((ROOT / 'dependency-lock.json').read_text())

    def fetch(entry):
        if entry['type'] != 'git' or entry.get('subDir') is not None:
            raise RuntimeError('Unsupported dependency manifest entry')
        pinned = lock['transitive_packages'][entry['name']]
        revision = entry['rev']
        parsed = urlparse(entry['url'])
        repository = parsed.path.removesuffix('.git').strip('/')
        url = f'https://codeload.github.com/{repository}/tar.gz/{revision}'
        if (parsed.scheme, parsed.netloc) != ('https', 'github.com') or \
                revision != pinned['revision'] or url != pinned['archive_url']:
            raise RuntimeError(f"Dependency manifest differs from the lock: {entry['name']}")
        archive = checked_archive(url, pinned['archive_sha256'],
            ROOT / '.tools/downloads' / f"{entry['name']}-{revision}.tar.gz", offline)
        destination = extract_source(archive, ROOT / '.tools/sources')
        link_source(ROOT / pinned['local_path'], destination)
        if not (ROOT / pinned['local_path'] / entry['configFile']).is_file():
            raise RuntimeError(f"Dependency configuration missing: {entry['name']}")
        print(f"Locked dependency source verified: {entry['name']}", flush=True)

    if {entry['name'] for entry in manifest['packages']} != set(lock['transitive_packages']):
        raise RuntimeError('Supporting package set differs from dependency-lock.json')
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(fetch, manifest['packages']))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true')
    fetch_dependencies(parser.parse_args().offline)
