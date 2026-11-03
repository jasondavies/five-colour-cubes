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
            subprocess.run(['git', 'clone', '--quiet', '--no-checkout', str(bundle), str(destination)], check=True)
            subprocess.run(['git', '-C', str(destination), 'checkout', '--quiet', '--detach', entry['rev']], check=True)
            subprocess.run(['git', '-C', str(destination), 'remote', 'set-url', 'origin', entry['url']], check=True)
        actual = subprocess.check_output(['git', '-C', str(destination), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != entry['rev']:
            raise SystemExit(f'Existing dependency has wrong revision: {name}')
        subprocess.run(['git', '-C', str(destination), 'diff', '--quiet', 'HEAD'], check=True)
        print(f'{name}: {actual}')
    print('Pinned project dependencies installed. Fetch public mathlib dependencies with lake exe cache get.')


if __name__ == '__main__':
    main()
