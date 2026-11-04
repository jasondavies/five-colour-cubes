#!/usr/bin/env python3
"""Install the exact bundled project dependencies without private GitHub access."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('colour_cubes_core',)


def main():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    for name in NAMES:
        entry = packages[name]
        bundle = ROOT / 'dependencies' / f'{name}.bundle'
        if not bundle.is_file():
            raise SystemExit('Bundled dependencies are supplied in the review archive; see README.md.')
        destination = ROOT / '.lake/packages' / name
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git', 'init', '--quiet', str(destination)], check=True)
            # Git bundles do not carry a shallow boundary. Install the boundary
            # explicitly before fetching the pinned commit and all its tree objects.
            (destination / '.git/shallow').write_text(entry['rev'] + '\n')
            subprocess.run(['git', '-C', str(destination), 'fetch', '--quiet', str(bundle),
                            'refs/heads/snapshot'], check=True)
            subprocess.run(['git', '-C', str(destination), 'checkout', '--quiet', '--detach', entry['rev']], check=True)
            subprocess.run(['git', '-C', str(destination), 'remote', 'add', 'origin', entry['url']], check=True)
        actual = subprocess.check_output(['git', '-C', str(destination), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != entry['rev']:
            raise SystemExit(f'Existing dependency has wrong revision: {name}')
        subprocess.run(['git', '-C', str(destination), 'diff', '--quiet', 'HEAD'], check=True)
        print(f'{name}: {actual}')
    print('Pinned project dependencies installed. Fetch public mathlib dependencies with lake exe cache get.')


if __name__ == '__main__':
    main()
