#!/usr/bin/env python3
"""Generate kernel-checked packed Hall data and calibration lemmas.

This is a serializer, not a trusted proof checker. Generated numerical claims
are checked by Lean; PackedVerified.check_sound supplies their meaning.
"""
import argparse
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'data'
DEST = ROOT / 'FiveColour'
BASE = 1024
WEIGHTS = [BASE ** (74 - i) for i in range(75)]
HEADER = '''module
public import FiveColour.PackedCore
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
'''


def cut(indices, rhs):
    return f'⟨{sum(1 << i for i in indices)}, {sum(WEIGHTS[i] for i in indices)}, {rhs}⟩'


def write_data(rows):
    text = HEADER
    for target, row in enumerate(rows):
        cuts = [cut([i for i, mask in enumerate(row) if mask & d], d.bit_count() - 1)
                for d in range(1, 256)]
        text += f'def cutRow{target} : Array Cut := #[' + ','.join(cuts) + ']\n'
    text += 'def cuts : Array (Array Cut) := #[' + ','.join(f'cutRow{i}' for i in range(75)) + ']\n'
    (DEST / 'PackedData.lean').write_text(text + 'end FiveColour.Packed\n')
    for group in range(8):
        text = HEADER.replace('FiveColour.PackedCore', 'FiveColour.PackedData\npublic import FiveColour.PackedSemantics')
        for i in range(group * 10, min(group * 10 + 10, 75)):
            text += f'theorem cutRow{i}_weights : cutRow{i}.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel\n'
        (DEST / f'PackedCalibration{group}.lean').write_text(text + 'end FiveColour.Packed\n')
    text = 'module\n' + ''.join(f'public import FiveColour.PackedCalibration{i}\n' for i in range(8))
    text += '''@[expose] public section
namespace FiveColour.Packed
set_option maxRecDepth 100000

theorem cuts_weights : cuts.toList.all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true := by
'''
    text += '  change [' + ','.join(f'cutRow{i}' for i in range(75)) + '].all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true\n'
    text += '  simp only [List.all_cons, List.all_nil, Bool.and_self, ' + ','.join(f'cutRow{i}_weights' for i in range(75)) + ']\n'
    text += '''
theorem cuts_valid (r : Fin 75) : ∀ c ∈ (cuts[r.val]!).toList, c.Valid := by
  apply list_valid_of_weights
  apply List.all_eq_true.mp cuts_weights
  have hsize : cuts.size = 75 := by decide +kernel
  have hr : r.val < cuts.size := by omega
  simpa only [getElem!_pos cuts r.val hr] using Array.getElem_mem_toList hr
end FiveColour.Packed
'''
    (DEST / 'PackedCalibration.lean').write_text(text)


def main():
    global DEST
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = [list(map(int, line.split())) for line in
            (RESULTS / 'five-colour-geometry.txt').read_text().splitlines()[76:]]
    if len(rows) != 75 or any(len(row) != 75 for row in rows):
        raise ValueError('expected 75 by 75 incidence table')
    if args.check:
        with tempfile.TemporaryDirectory(prefix='q5-packed-') as temp:
            DEST = Path(temp)
            write_data(rows)
            for p in DEST.iterdir():
                if p.read_bytes() != (ROOT / 'FiveColour' / p.name).read_bytes():
                    raise SystemExit(f'Generated file differs: {p.name}')
        print('Packed Hall data and calibration sources match regeneration.')
    else:
        write_data(rows)


if __name__ == '__main__':
    main()
