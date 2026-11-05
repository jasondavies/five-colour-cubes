#!/usr/bin/env python3
"""Emit untrusted catalogue witnesses, each checked by Lean's kernel.

Only 75 * 24 rotations are needed. The 5^6 raw face assignments are split
into 125 blocks of 125, avoiding a large monolithic kernel computation.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from cube_geometry import ROT, corners


def vector(xs):
    return '![' + ','.join(xs) + ']'


def generate(root, check=False):
    def emit(path, content):
        if check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f'Generated file differs: {path.relative_to(root)}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)

    lines = (root / 'data/five-colour-geometry.txt').read_text().splitlines()
    count = int(lines[0])
    if count != 75:
        raise ValueError('Expected 75 catalogue representatives')
    cubes = [tuple(map(int, line.split())) for line in lines[1:76]]
    witnesses = {}
    for i, cube in enumerate(cubes):
        for r, rotation in enumerate(ROT):
            raw = tuple(cube[f] for f in rotation)
            if raw in witnesses:
                raise ValueError('Duplicate rotation variety or nontrivial stabiliser')
            witnesses[raw] = (i, r)
    if len(witnesses) != 1800:
        raise ValueError('Expected 1800 five-colour face assignments')
    rows = []
    for b in range(125):
        row = []
        for k in range(125):
            raw = tuple(n // 5**f % 5 for n in (k, b) for f in range(3))
            if (len(set(raw)) == 5) != (raw in witnesses):
                raise ValueError('Catalogue is incomplete')
            i, r = witnesses.get(raw, (0, 0))
            row.append(f'({i},{r})')
        rows.append(vector(row))
    out = root / 'FiveColour/CatalogueData.lean'
    emit(out, '''module
public import FiveColour.Problem
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- The 75 representatives, in the search data's order; faces are +x,-x,+y,-y,+z,-z. -/
def catalogue : Fin 75 → Cube :=
  ''' + vector([vector(map(str, c)) for c in cubes]) + '''

/-- Six base-five digits, in two blocks of three. -/
def rawCube (b k : Fin 125) : Cube :=
  fun f => ⟨(if f.val < 3 then k.val / 5^f.val else b.val / 5^(f.val-3)) % 5,
    Nat.mod_lt _ (by decide)⟩

/-- Candidate representative and proper rotation; invalid palettes use a dummy entry. -/
def rawWitness : Fin 125 → Fin 125 → Fin 75 × Fin 24 :=
  ''' + vector(rows) + '''

/-- This proposition checks the witness against all six physical faces. -/
def RawCheck (b : Fin 125) : Prop := ∀ k, UsesAllColours (rawCube b k) →
  ∀ f, rawCube b k f = catalogue (rawWitness b k).1 (ColourCubes.rotations (rawWitness b k).2 f)

instance (b : Fin 125) : Decidable (RawCheck b) := by
  unfold RawCheck UsesAllColours
  infer_instance
end FiveColour.Physical
''')
    # Five independent kernel tasks, with 25 small proof terms apiece.
    directory = root / 'FiveColour/CatalogueChecks'
    for group in range(5):
        proofs = '\n'.join(f'lemma raw_check_{b} : RawCheck {b} := by decide +kernel'
                           for b in range(25*group, 25*(group+1)))
        emit(directory / f'Block{group}.lean', '''module
public import FiveColour.CatalogueData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical
''' + proofs + '\nend FiveColour.Physical\n')
    emit(root / 'FiveColour/CatalogueChecks.lean', 'module\npublic import Mathlib.Tactic.FinCases\n' +
        ''.join(f'public import FiveColour.CatalogueChecks.Block{g}\n' for g in range(5)) +
        '\n@[expose] public section\nnamespace FiveColour.Physical\n' +
        'theorem raw_checks (b : Fin 125) : RawCheck b := by\n  fin_cases b\n' +
        ''.join(f'  · exact raw_check_{b}\n' for b in range(125)) +
        'end FiveColour.Physical\n')
    packed_keys = [sum((25*a + 5*b + c) * 128**k
                       for k, (a,b,c) in enumerate(corners(cube))) for cube in cubes]
    emit(root / 'FiveColour/CornerKeyData.lean', """module
public import FiveColour.CornerKeys
@[expose] public section
namespace FiveColour.Physical

/-- Eight cyclic corner keys, packed in base 128 (each key is below 125). -/
def packedCornerKeys : Fin 75 → Nat :=
  """ + vector(map(str, packed_keys)) + """

def catalogueCornerKey (i : Fin 75) (k : Fin 8) : Nat :=
  packedCornerKeys i / 128^k.val % 128

end FiveColour.Physical
""")
    lower = [(0,0,1,2,3,4), (0,1,2,3,2,4), (0,3,1,2,4,1)]
    lower_corners = [set(corners(cube)) for cube in lower]
    cuts = []
    for cube in cubes:
        tc = corners(cube)
        masks = [sum(1 << k for k, c in enumerate(tc) if c in cs) for cs in lower_corners]
        cuts.append(next(d for d in range(1, 256)
                         if sum(n for n, m in zip((4, 5, 5), masks) if d & m) < d.bit_count()))
    emit(root / 'FiveColour/LowerData.lean', """module
public import FiveColour.CatalogueData
@[expose] public section
namespace FiveColour.Physical

/-- One explicit deficient corner set for each target; bit k denotes corner k. -/
def lowerCutMask : Fin 75 → Nat :=
  """ + vector(map(str, cuts)) + """

def lowerCut (t : Fin 75) : Finset (Fin 8) :=
  Finset.univ.filter fun k => (lowerCutMask t).testBit k.val

end FiveColour.Physical
""")
    print(('Checked' if check else 'Generated') + ' catalogue witnesses and lower-bound cuts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true', help='Compare generated files without writing')
    args = parser.parse_args()
    generate(args.root, args.check)
