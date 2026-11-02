#!/usr/bin/env python3
"""Serialize actual Q5P2 headers and kernel checks against the physical root model.

The proof bodies remain in their existing replay modules. This generator checks
no proof by itself: Lean verifies each encoding and the decoded constraint fields.
"""
import argparse
from pathlib import Path
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def generate(root, check=False):
    def emit(name, text):
        path = root / 'FiveColour' / name
        if check:
            if not path.is_file() or path.read_text() != text:
                raise SystemExit(f'Generated file differs: {path.relative_to(root)}')
        else:
            path.write_text(text)

    lines = (root / 'data/q5-threshold-cases-size15.txt').read_text().splitlines()
    ledger = [list(map(int, line.split())) for line in lines[1:]]
    assert int(lines[0]) == len(ledger) == 357
    headers = {}
    with tarfile.open(root / 'data/q5-certificates.tar.gz') as archive:
        for member in archive:
            match = re.fullmatch(r'case-(\d+)\.q5p', member.name)
            if not member.isfile() or match is None:
                raise ValueError(f'Unexpected archive member: {member.name}')
            case = int(match[1])
            if case in headers or not 0 <= case < 357:
                raise ValueError(f'Duplicate or invalid case: {case}')
            raw = archive.extractfile(member).read(160)
            if raw != b'Q5P2' + bytes(ledger[case]):
                raise ValueError(f'Archive header disagrees with ledger: {case}')
            kind, m, _, goal, anchor, budget, *rest = list(raw[4:])
            assert kind in (0, 1) and anchor == (3, 0)[kind] and goal == 15
            lower, upper = [0]*75, rest[:75]
            assert upper[anchor] == 0
            lower[anchor] = upper[anchor] = m
            assert all(0 <= v <= 7 for v in lower+upper)
            bad = rest[75:]
            assert len(bad) == 75 and all(b in (0, 1) for b in bad)
            encode = lambda xs: sum(v << (10*i) for i, v in enumerate(xs))
            mask = sum(b << i for i, b in enumerate(bad))
            weight = sum(b << (10*(74-i)) for i, b in enumerate(bad))
            headers[case] = (encode(lower), encode(upper), mask, weight, budget)
    assert len(headers) == 357
    data = '#[' + ',\n  '.join('⟨' + ','.join(map(str, headers[r])) + '⟩' for r in range(357)) + ']'
    emit('ArchiveData.lean', '''module
public import FiveColour.ArchiveCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Archive
open Physical

/-- Headers in case-number order, checked against the integer model below. -/
def headers : Array Header :=
  ''' + data + '''

def root (r : Fin 357) : Box := ⟨headers[r.val]!.lower, headers[r.val]!.upper⟩

def budgetCut (r : Fin 357) : Cut :=
  ⟨headers[r.val]!.badMask, headers[r.val]!.badWeight, headers[r.val]!.budget⟩

/-- Exactly the ordering and fields used by the archived replay modules. -/
def families (r : Fin 357) (t : Fin 78) : List Cut :=
  if t.val = 0 then [⟨0, 0, 0⟩]
  else if t.val = 1 then [⟨2^75-1, allWeight, 15⟩]
  else if t.val = 2 then [budgetCut r]
  else (cuts[t.val-3]!).toList

/-- Semantics of the header. Cut weights are calibrated by the replay checker;
only masks and right-hand sides enter the decoded integer problem. -/
def HeaderValid (r : Fin 357) : Prop :=
  (root r).lower = encode (rootLower r) ∧
    (root r).upper = encode (rootUpper (rootCapacity r)) ∧
    (budgetCut r).mask = (rootCapacity r).badMask ∧
    (budgetCut r).rhs = (rootCapacity r).budget

instance (r : Fin 357) : Decidable (HeaderValid r) := by
  unfold HeaderValid
  infer_instance

end FiveColour.Packed.Archive
''')
    for group in range(8):
        checks = ''.join(f'lemma header_valid_{r} : HeaderValid {r} := by decide +kernel\n'
                         for r in range(group*45, min(group*45+45, 357)))
        emit(f'ArchiveChecks{group}.lean', '''module
public import FiveColour.ArchiveData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Archive
''' + checks + 'end FiveColour.Packed.Archive\n')
    emit('ArchiveChecks.lean', 'module\n' +
         ''.join(f'public import FiveColour.ArchiveChecks{g}\n' for g in range(8)) + '''@[expose] public section
namespace FiveColour.Packed.Archive

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem header_valid (r : Fin 357) : HeaderValid r := by
  fin_cases r
''' + ''.join(f'  · exact header_valid_{r}\n' for r in range(357)) +
         'end FiveColour.Packed.Archive\n')
    print(('Checked' if check else 'Generated') + ' all 357 archived headers and their encoding/model checks.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generate(args.root, args.check)
