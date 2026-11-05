"""Shared production witness helpers; independent auditors do not import these."""
import itertools

from cube_geometry import ROT, canonical


def match_copies(masks, sources):
    """Return one distinct physical-copy index per corner, or None."""
    owned = [-1] * len(sources)

    def augment(corner, seen):
        for copy, source in enumerate(sources):
            if copy in seen or not masks[source] & (1 << corner):
                continue
            seen.add(copy)
            if owned[copy] < 0 or augment(owned[copy], seen):
                owned[copy] = corner
                return True
        return False

    if not all(augment(corner, set()) for corner in range(8)):
        return None
    return [owned.index(corner) for corner in range(8)]


def ordered_anchor_symmetries(cubes, anchors):
    """The stable numeric symmetry order used by coverage and triple witnesses."""
    index = {canonical(c): i for i, c in enumerate(cubes)}

    def apply(p, mirror, cube):
        c = tuple(p[a] for a in cube)
        return (c[1], c[0], *c[2:]) if mirror else c

    symmetries, actions, rotations = [], [], []
    for p in itertools.permutations(range(5)):
        for mirror in (False, True):
            if not any(canonical(apply(p, mirror, cubes[a])) == canonical(cubes[a]) for a in anchors):
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
    return symmetries, actions, rotations
