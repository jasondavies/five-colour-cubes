#!/usr/bin/env python3
"""Emit untrusted pair witnesses and the upper bounds of the 357 archived roots.

Lean checks each witness against verified incidence and each root cap against
its class bound, Hall budget and pair bound. This does not establish case coverage.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def array(xs):
    return '#[' + ','.join(map(str, xs)) + ']'


def generate(root, check=False):
    def emit(name, text):
        path = root / 'FiveColour' / name
        if check:
            if not path.is_file() or path.read_text() != text:
                raise SystemExit(f'Generated file differs: {path.relative_to(root)}')
        else:
            path.write_text(text)

    geometry = (root / 'data/five-colour-geometry.txt').read_text().splitlines()
    masks = [list(map(int, s.split())) for s in geometry[76:]]
    assert len(masks) == 75 and all(len(r) == 75 for r in masks)
    witnesses = []
    for anchor in (3, 0):
        for m in range(8):
            for i in range(75):
                witness = 0
                if i != anchor:
                    for a in range(m, 0, -1):
                        targets = [t for t, row in enumerate(masks)
                                   if row[anchor] | row[i] == 255
                                   and a <= row[anchor].bit_count()
                                   and 8-a <= row[i].bit_count()]
                        if targets:
                            witness = 8*targets[0]+a
                            break
                witnesses.append(witness)
    emit('PairCapacityData.lean', '''module
public import FiveColour.PairCapacityDefs
@[expose] public section
namespace FiveColour.Physical

/-- Each entry encodes target * 8 + anchor copies; zero means no tightening. -/
def pairWitnessData : Array Nat :=
  ''' + array(witnesses) + '''

def pairWitness (kind : Fin 2) (m : Fin 8) (i : Fin 75) : Nat :=
  pairWitnessData[(kind.val * 8 + m.val) * 75 + i.val]!

def pairSplit (kind : Fin 2) (m : Fin 8) (i : Fin 75) : Fin 8 :=
  ⟨pairWitness kind m i % 8, Nat.mod_lt _ (by decide)⟩

def pairTarget (kind : Fin 2) (m : Fin 8) (i : Fin 75) : Fin 75 :=
  ⟨pairWitness kind m i / 8 % 75, Nat.mod_lt _ (by decide)⟩

def pairCap (kind : Fin 2) (m : Fin 8) (i : Fin 75) : Nat :=
  7 - (pairSplit kind m i).val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pair_witnesses_valid : ∀ (kind : Fin 2) (m : Fin 8) (i : Fin 75),
    (pairSplit kind m i).val ≠ 0 →
      (pairSplit kind m i).val ≤ m.val ∧ canonicalAnchor kind ≠ i ∧
        PairMaskCriterion (canonicalAnchor kind) i (pairTarget kind m i)
          (pairSplit kind m i).val := by
  decide +kernel

end FiveColour.Physical
''')
    lines = (root / 'data/q5-threshold-cases-size15.txt').read_text().splitlines()
    rows = [list(map(int, s.split())) for s in lines[1:]]
    assert int(lines[0]) == len(rows) == 357 and all(len(r) == 156 for r in rows)
    records = []
    for kind, m, cover, goal, anchor, budget, *rest in rows:
        assert kind in (0, 1) and 1 <= m <= 7 and goal == 15 and anchor == (3, 0)[kind]
        upper, bad = rest[:75], rest[75:]
        assert upper[anchor] == 0 and all(b in (0, 1) for b in bad)
        records.append('⟨' + ','.join([str(kind), str(m), str(cover), str(budget),
                                      array(upper), str(sum(b << i for i, b in enumerate(bad)))]) + '⟩')
    emit('RootCapacityData.lean', '''module
public import FiveColour.RootCapacityDefs
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- Exact root metadata and upper vectors from the archived case ledger.
The anchor's raw zero is a sentinel, replaced by m in rootUpper. -/
def rootCapacityData : Array RootCapacity :=
  ''' + array(records) + '''

def rootCapacity (r : Fin 357) : RootCapacity := rootCapacityData[r.val]!

end FiveColour.Physical
''')
    for group in range(8):
        checks = ''.join(f'lemma root_caps_match_{r} : ∀ i : Fin 75,\n'
                         f'    rootUpper (rootCapacity {r}) i = combinedCap (rootCapacity {r}) i := by\n'
                         '  decide +kernel\n'
                         for r in range(group*45, min(group*45+45, 357)))
        emit(f'RootCapacityChecks{group}.lean', '''module
public import FiveColour.RootCapacityData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical
''' + checks + 'end FiveColour.Physical\n')
    emit('RootCapacityChecks.lean', 'module\n' +
         ''.join(f'public import FiveColour.RootCapacityChecks{g}\n' for g in range(8)) + '''@[expose] public section
namespace FiveColour.Physical

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_caps_match (r : Fin 357) (i : Fin 75) :
    rootUpper (rootCapacity r) i = combinedCap (rootCapacity r) i := by
  fin_cases r
''' + ''.join(f'  · exact root_caps_match_{r} i\n' for r in range(357)) +
         'end FiveColour.Physical\n')
    print(('Checked' if check else 'Generated') + ' 1,200 pair witnesses and 357 root upper vectors.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generate(args.root, args.check)
