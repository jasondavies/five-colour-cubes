#!/usr/bin/env python3
"""Generate untrusted finite witnesses mapping anchor covers to exported roots.

The costly proof checks are split into eight modules. Lean validates the
physical symmetry actions, mask transport, and lookup in the actual case ledger.
"""
import argparse
import itertools
from pathlib import Path
from cube_geometry import ROT, canonical

ROOT = Path(__file__).resolve().parents[1]


def vector(xs):
    return '![' + ','.join(map(str, xs)) + ']'


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

    lines = (root / 'data/five-colour-geometry.txt').read_text().splitlines()
    cubes = [tuple(map(int, s.split())) for s in lines[1:76]]
    masks = [list(map(int, s.split())) for s in lines[76:]]
    assert len(cubes) == len(masks) == 75
    index = {c: i for i, c in enumerate(cubes)}
    anchors = (3, 0)

    def apply(p, mirror, cube):
        c = tuple(p[a] for a in cube)
        return (c[1], c[0], *c[2:]) if mirror else c

    symmetries, actions, rotations = [], [], []
    for p in itertools.permutations(range(5)):
        for mirror in (False, True):
            if not any(canonical(apply(p, mirror, cubes[a])) == cubes[a] for a in anchors):
                continue
            action, rotation = [], []
            for cube in cubes:
                c = apply(p, mirror, cube)
                i = index[canonical(c)]
                r = next(r for r, perm in enumerate(ROT) if c == tuple(cubes[i][f] for f in perm))
                action.append(i)
                rotation.append(r)
            symmetries.append((p, mirror))
            actions.append(action)
            rotations.append(rotation)
    count = len(symmetries)
    groups = [[g for g, action in enumerate(actions) if action[a] == a] for a in anchors]

    def transport(g, mask):
        return sum(1 << actions[g][i] for i in range(75) if mask >> i & 1)

    bad_masks = [[sum(1 << i for i in range(75) if i != a and masks[a][i] & (255 ^ d))
                  for d in range(256)] for a in anchors]
    reps, transforms = [], []
    for kind in range(2):
        chosen, kind_reps, kind_transforms = {}, [], []
        for d, bad in enumerate(bad_masks[kind]):
            key = min(transport(g, bad) for g in groups[kind]), d.bit_count()
            representative = chosen.setdefault(key, d)
            g = next(g for g in groups[kind] if transport(g, bad) == bad_masks[kind][representative])
            kind_reps.append(representative)
            kind_transforms.append(g)
        reps.append(kind_reps)
        transforms.append(kind_transforms)

    rows = [list(map(int, s.split())) for s in
            (root / 'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    assert len(rows) == 357 and all(len(r) == 156 for r in rows)
    lookup = {(r[0], r[1], r[2]): j for j, r in enumerate(rows)}
    root_indices, eligible = [], 0
    for kind in range(2):
        for m in range(8):
            for d in range(256):
                if m == 0 or d.bit_count()+m > 7 or (kind, m, d) == (0, 1, 252):
                    root_indices.append(0)
                    continue
                r = lookup[kind, m, reps[kind][d]]
                row = rows[r]
                assert row[5]+d.bit_count()+m == 7
                assert sum(b << i for i, b in enumerate(row[81:])) == bad_masks[kind][reps[kind][d]]
                root_indices.append(r)
                eligible += 1

    emit('StabiliserData.lean', f'''module
public import FiveColour.CoverMasks
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- A sufficient list of global symmetries; completeness of this list is not assumed. -/
def stabiliserColour : Fin {count} → Fin 5 → Fin 5 :=
  ''' + vector(vector(p) for p, _ in symmetries) + f'''

def stabiliserColourInverse : Fin {count} → Fin 5 → Fin 5 :=
  ''' + vector(vector(p.index(a) for a in range(5)) for p, _ in symmetries) + f'''

def stabiliserMirror : Fin {count} → Bool :=
  ''' + vector(str(b).lower() for _, b in symmetries) + f'''

def stabiliserAction : Fin {count} → Fin 75 → Fin 75 :=
  ''' + vector(vector(a) for a in actions) + f'''

def stabiliserRotation : Fin {count} → Fin 75 → Fin 24 :=
  ''' + vector(vector(r) for r in rotations) + f'''

lemma stabiliser_inverse : ∀ (g : Fin {count}) (a : Fin 5),
    stabiliserColourInverse g (stabiliserColour g a) = a ∧
      stabiliserColour g (stabiliserColourInverse g a) = a := by decide +kernel

def stabiliserSymmetry (g : Fin {count}) : PuzzleSymmetry where
  colour := {{
    toFun := stabiliserColour g
    invFun := stabiliserColourInverse g
    left_inv a := (stabiliser_inverse g a).1
    right_inv a := (stabiliser_inverse g a).2 }}
  mirror := stabiliserMirror g

/-- Every proposed action is witnessed face by face by proper cube rotations. -/
lemma stabiliser_faces (g : Fin {count}) : ∀ (i : Fin 75) (f : Fin 6),
    (stabiliserSymmetry g).apply (catalogue i) f =
      catalogue (stabiliserAction g i) (MacMahon.rotations (stabiliserRotation g i) f) := by
  fin_cases g <;> decide +kernel

lemma stabiliser_variety (g : Fin {count}) (i : Fin 75) :
    varietyEquiv (stabiliserSymmetry g) i = stabiliserAction g i := by
  change catalogueIndex ((stabiliserSymmetry g).apply (catalogue i)) = _
  rw [funext (stabiliser_faces g i)]
  exact catalogue_index_rotations _ _

end FiveColour.Physical
''')
    emit('CoverData.lean', '''module
public import FiveColour.StabiliserData
public import FiveColour.RootCapacityData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- Representatives and transport witnesses for all 256 corner masks of each anchor. -/
def coverRepresentativeData : Array Nat :=
  ''' + array(sum(reps, [])) + '''

def coverTransformData : Array Nat :=
  ''' + array(sum(transforms, [])) + '''

def coverRootData : Array Nat :=
  ''' + array(root_indices) + '''

def coverRepresentative (kind : Fin 2) (d : Fin 256) : Fin 256 :=
  ⟨coverRepresentativeData[kind.val*256+d.val]! % 256, Nat.mod_lt _ (by decide)⟩

''' + f'''def coverTransform (kind : Fin 2) (d : Fin 256) : Fin {count} :=
  ⟨coverTransformData[kind.val*256+d.val]! % {count}, Nat.mod_lt _ (by decide)⟩
''' + '''
def coverRoot (kind : Fin 2) (m : Fin 8) (d : Fin 256) : Fin 357 :=
  ⟨coverRootData[(kind.val*8+m.val)*256+d.val]! % 357, Nat.mod_lt _ (by decide)⟩

def coverBlock (b : Fin 8) (d : Fin 32) : Fin 256 := ⟨32*b.val+d.val, by omega⟩

def CoverOrbitValid (kind : Fin 2) (d : Fin 256) : Prop :=
  stabiliserAction (coverTransform kind d) (canonicalAnchor kind) = canonicalAnchor kind ∧
    (cornerSet (coverRepresentative kind d).val).card = (cornerSet d.val).card ∧
    transportMask (stabiliserAction (coverTransform kind d)) (coverBadMask kind d) =
      coverBadMask kind (coverRepresentative kind d)

instance (kind : Fin 2) (d : Fin 256) : Decidable (CoverOrbitValid kind d) := by
  unfold CoverOrbitValid
  infer_instance

def CoverRootValid (kind : Fin 2) (m : Fin 8) (d : Fin 256) : Prop :=
  let r := rootCapacity (coverRoot kind m d)
  r.kind = kind ∧ r.copies = m ∧ r.cover = (coverRepresentative kind d).val ∧
    r.budget + (cornerSet d.val).card + m.val = 7 ∧
    r.badMask = coverBadMask kind (coverRepresentative kind d)

instance (kind : Fin 2) (m : Fin 8) (d : Fin 256) : Decidable (CoverRootValid kind m d) := by
  unfold CoverRootValid
  infer_instance

end FiveColour.Physical
''')
    for b in range(8):
        checks = ''.join(f'''lemma cover_orbit_{kind}_{b} : ∀ d : Fin 32,
    CoverOrbitValid {kind} (coverBlock {b} d) := by decide +kernel

lemma cover_root_{kind}_{b} : ∀ d : Fin 256,
    CoverEligible {kind} {b} d → CoverRootValid {kind} {b} d := by decide +kernel

''' for kind in range(2))
        emit(f'CoverChecks{b}.lean', '''module
public import FiveColour.CoverData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical
''' + checks + 'end FiveColour.Physical\n')
    emit('CoverChecks.lean', 'module\n' +
         ''.join(f'public import FiveColour.CoverChecks{b}\n' for b in range(8)) + '''@[expose] public section
namespace FiveColour.Physical

lemma cover_orbit_block (kind : Fin 2) (b : Fin 8) (d : Fin 32) :
    CoverOrbitValid kind (coverBlock b d) := by
  fin_cases kind <;> fin_cases b
''' + ''.join(f'  · exact cover_orbit_{kind}_{b} d\n' for kind in range(2) for b in range(8)) + '''
theorem cover_orbit_valid (kind : Fin 2) (d : Fin 256) : CoverOrbitValid kind d := by
  let b : Fin 8 := ⟨d.val / 32, by omega⟩
  let e : Fin 32 := ⟨d.val % 32, Nat.mod_lt _ (by decide)⟩
  have he : coverBlock b e = d := by apply Fin.ext; simp [coverBlock, b, e, Nat.div_add_mod]
  rw [← he]
  exact cover_orbit_block kind b e

theorem cover_root_valid (kind : Fin 2) (m : Fin 8) (d : Fin 256)
    (h : CoverEligible kind m d) : CoverRootValid kind m d := by
  fin_cases kind <;> fin_cases m
''' + ''.join(f'  · exact cover_root_{kind}_{m} d h\n' for kind in range(2) for m in range(8)) +
         'end FiveColour.Physical\n')
    print(('Checked' if check else 'Generated') +
          f' {count} physical symmetries, 512 cover transports and {eligible} eligible root lookups.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generate(args.root, args.check)
