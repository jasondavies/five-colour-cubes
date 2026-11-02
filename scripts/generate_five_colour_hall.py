#!/usr/bin/env python3
"""Emit untrusted Hall-table transposes and kernel-check declarations.

Lean checks the transpose against the physical incidence matrix, then checks
all 19,125 packed neighbourhood masks and deficiency bounds against this model.
The arithmetic weights are checked separately by PackedCalibration.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def vector(values):
    return '![' + ','.join(values) + ']'


def generate(root, check=False):
    def emit(name, text):
        path = root / 'FiveColour' / name
        if check:
            if not path.is_file() or path.read_text() != text:
                raise SystemExit(f'Generated file differs: {path.relative_to(root)}')
        else:
            path.write_text(text)

    lines = (root / 'data/five-colour-geometry.txt').read_text().splitlines()
    rows = [list(map(int, line.split())) for line in lines[76:]]
    if int(lines[0]) != 75 or len(rows) != 75 or any(len(r) != 75 for r in rows):
        raise ValueError('Expected a 75 by 75 incidence matrix')
    if any(not 0 <= mask < 256 for row in rows for mask in row):
        raise ValueError('Expected eight-bit incidence masks')
    sources = [vector([str(sum(1 << i for i, m in enumerate(row) if m & (1 << k)))
                       for k in range(8)]) for row in rows]
    emit('PackedHallData.lean', '''module
public import FiveColour.Incidence
@[expose] public section
namespace FiveColour.Packed

/-- For each target corner, a bit mask of compatible source varieties. -/
def cornerSources : Fin 75 → Fin 8 → Nat :=
  ''' + vector(sources) + '''

end FiveColour.Packed
''')
    for group in range(8):
        proofs = ''.join(f'lemma hall_signatures_{t} : actualSignatures {t} = expectedSignatures {t} := by decide +kernel\n'
                         for t in range(group * 10, min(group * 10 + 10, 75)))
        emit(f'PackedHallChecks{group}.lean', '''module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
''' + proofs + 'end FiveColour.Packed\n')
    emit('PackedHallChecks.lean', 'module\n' +
         ''.join(f'public import FiveColour.PackedHallChecks{g}\n' for g in range(8)) + '''@[expose] public section
namespace FiveColour.Packed

theorem hall_signatures (t : Fin 75) : actualSignatures t = expectedSignatures t := by
  fin_cases t
''' + ''.join(f'  · exact hall_signatures_{t}\n' for t in range(75)) + 'end FiveColour.Packed\n')
    print(('Checked' if check else 'Generated') + ' Hall transpose and 75 packed-row checks.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true', help='Compare generated files without writing')
    args = parser.parse_args()
    generate(args.root, args.check)
