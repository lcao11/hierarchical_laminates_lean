#!/usr/bin/env python3
"""Prepare and verify Git metadata for pinned supporting dependencies."""

from concurrent.futures import ThreadPoolExecutor
import argparse
import json

from setup_common import ROOT, run


def materialize_dependencies(offline=False):
    entries = json.loads((ROOT / '.lake/packages/mathlib/lake-manifest.json').read_text())['packages']

    def materialize(entry):
        path = ROOT / '.lake/packages' / entry['name']
        if not path.is_symlink() or not path.resolve().is_relative_to((ROOT / '.tools/sources').resolve()):
            raise RuntimeError(f'Expected an isolated downloaded source: {path}')
        new = not (path / '.git').exists()
        if new:
            run(['git', 'init', '--quiet'], path)
            run(['git', 'remote', 'add', 'origin', entry['url']], path)
        else:
            head = run(['git', 'rev-parse', 'HEAD'], path, check=False)
            if head.returncode == 0 and head.stdout.strip() != entry['rev']:
                raise RuntimeError(f'Unexpected dependency revision; preserved: {path}')
            dirty = run(['git', 'status', '--porcelain', '--untracked-files=no'], path)
            if dirty.stdout.strip():
                raise RuntimeError(f'Edited dependency preserved: {path}')
        found = run(['git', 'cat-file', '-e', entry['rev'] + '^{commit}'], path, check=False)
        if found.returncode:
            if offline:
                raise RuntimeError(f"Offline setup needs pinned Git metadata: {entry['name']}")
            run(['git', '-c', 'http.lowSpeedLimit=1000', '-c', 'http.lowSpeedTime=45',
                 'fetch', '--depth', '1', 'origin', entry['rev']], path)
        if new or run(['git', 'rev-parse', 'HEAD'], path, check=False).returncode:
            # Set the pinned Git index while preserving the dependency source tree.
            run(['git', 'reset', '--mixed', entry['rev']], path)
        if run(['git', 'diff', '--exit-code', 'HEAD', '--'], path, check=False).returncode:
            raise RuntimeError(f'Dependency source differs from its pin; preserved: {path}')
        actual = run(['git', 'rev-parse', 'HEAD'], path).stdout.strip()
        if actual != entry['rev']:
            raise RuntimeError(f"Dependency revision mismatch: {entry['name']}")
        print(f"Pinned dependency revision verified: {entry['name']}", flush=True)

    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(materialize, entries))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true')
    materialize_dependencies(parser.parse_args().offline)
