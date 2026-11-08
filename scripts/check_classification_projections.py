#!/usr/bin/env python3
"""Independently replay the projected classification exclusions in C++."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from classification_projection import ROOT, load_projections


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=2)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('workers must be positive')
    originals = [list(map(int,l.split())) for l in
                 (ROOT/'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    with tempfile.TemporaryDirectory(prefix='classification-projections-') as temp:
        work = Path(temp)
        projections, cases = load_projections(originals, work)
        for entry, _, path in projections.values():
            shutil.copyfile(path, work/f"case-{entry['index']}.q5p")
        result = work/'replay.json'
        subprocess.run([str(ROOT/'build/check_five_colour_certificate'),
                        str(ROOT/'data/five-colour-geometry.txt'), str(cases),
                        str(work/'case-'), str(result), str(args.workers)], check=True)
        rows = json.loads(result.read_text())
        expected = {e['index']:e for e,_,_ in projections.values()}
        if len(rows) != len(expected) or {r['case'] for r in rows} != expected.keys():
            raise ValueError('incomplete native projection replay')
        for row in rows:
            entry = expected[row['case']]
            if (row['accepted'] is not True or row['commands'] != entry['new_instructions']
                    or row['bytes'] != entry['certificate_bytes']):
                raise ValueError('native projection replay mismatch')
        print(f'Accepted {len(rows)} projected exclusions; {sum(r["commands"] for r in rows):,} instructions.')


if __name__ == '__main__':
    main()
