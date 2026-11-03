#!/usr/bin/env python3
"""Generate small, untrusted colour-permutation witnesses for the two anchor classes."""
import argparse
import itertools
from pathlib import Path
from cube_geometry import ROT

ROOT = Path(__file__).resolve().parents[1]


def vector(xs):
    return '![' + ','.join(xs) + ']'


def generate(root, check=False):
    lines = (root / 'data/five-colour-geometry.txt').read_text().splitlines()
    cubes = [tuple(map(int, s.split())) for s in lines[1:76]]
    if int(lines[0]) != 75 or len(cubes) != 75:
        raise ValueError('Expected 75 varieties')
    perms, inverses, rotations = [], [], []
    for cube in cubes:
        opposite = any(cube[2*j] == cube[2*j+1] for j in range(3))
        anchor = cubes[0 if opposite else 3]
        witness = next((p, r) for p in itertools.permutations(range(5)) for r, rot in enumerate(ROT)
                       if tuple(p[c] for c in cube) == tuple(anchor[f] for f in rot))
        p, r = witness
        perms.append(vector(map(str, p)))
        inverses.append(vector(str(p.index(a)) for a in range(5)))
        rotations.append(str(r))
    text = '''module
public import FiveColour.AnchorKinds
@[expose] public section
namespace FiveColour.Physical

/-- Candidate colour permutations and their inverses, verified below. -/
def normalisationColour : Fin 75 → Fin 5 → Fin 5 :=
  ''' + vector(perms) + '''

def normalisationColourInverse : Fin 75 → Fin 5 → Fin 5 :=
  ''' + vector(inverses) + '''

def normalisationRotation : Fin 75 → Fin 24 :=
  ''' + vector(rotations) + '''

lemma normalisation_inverse : ∀ (i : Fin 75) (a : Fin 5),
    normalisationColourInverse i (normalisationColour i a) = a ∧
      normalisationColour i (normalisationColourInverse i a) = a := by
  decide +kernel

def normalisingColour (i : Fin 75) : Equiv.Perm (Fin 5) where
  toFun := normalisationColour i
  invFun := normalisationColourInverse i
  left_inv a := (normalisation_inverse i a).1
  right_inv a := (normalisation_inverse i a).2

/-- Face-by-face witnesses, checked against proper rotations rather than corner incidence. -/
lemma normalisation_faces : ∀ (i : Fin 75) (f : Fin 6),
    recolour (normalisingColour i) (catalogue i) f =
      catalogue (anchorFor i) (ColourCubes.rotations (normalisationRotation i) f) := by
  decide +kernel

end FiveColour.Physical
'''
    path = root / 'FiveColour/NormalisationData.lean'
    if check:
        if not path.is_file() or path.read_text() != text:
            raise SystemExit('Generated file differs: FiveColour/NormalisationData.lean')
    else:
        path.write_text(text)
    print(('Checked' if check else 'Generated') + ' 75 colour-permutation and rotation witnesses.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true', help='Compare generated data without writing')
    args = parser.parse_args()
    generate(args.root, args.check)
