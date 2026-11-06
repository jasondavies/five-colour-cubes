#!/usr/bin/env python3
"""Independently reconstruct and verify a 15-cube universal collection.

Uses no repository Python modules. Proper rotations and physical corner fits
are regenerated from determinant-positive signed coordinate permutations.
The repository catalogue/masks are compared with that reconstruction.

This is an executable mathematical check, not a Lean proof or kernel replay.
Sources are reused across targets; each individual target uses eight distinct
physical copies. Interior face colours are unrestricted.
"""

from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import hashlib
import json
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parity(seq):
    return (-1) ** sum(seq[i] > seq[j]
                       for i in range(len(seq))
                       for j in range(i + 1, len(seq)))


def physical_rotations():
    normals = ((1, 0, 0), (-1, 0, 0), (0, 1, 0),
               (0, -1, 0), (0, 0, 1), (0, 0, -1))
    normal_index = {v: i for i, v in enumerate(normals)}
    result = []
    for axis in permutations(range(3)):
        for signs in product((-1, 1), repeat=3):
            if parity(axis) * signs[0] * signs[1] * signs[2] != 1:
                continue
            face_permutation = [None] * 6
            for source_face, vector in enumerate(normals):
                rotated = [0] * 3
                for j in range(3):
                    rotated[axis[j]] = signs[j] * vector[j]
                target_face = normal_index[tuple(rotated)]
                face_permutation[target_face] = source_face
            result.append(tuple(face_permutation))
    result = sorted(set(result))
    require(len(result) == 24, "Expected the 24 proper rotations")
    return result


CORNER_SIGNS = list(product((0, 1), repeat=3))
CORNER_FACES = [tuple(2 * axis + signs[axis] for axis in range(3))
                for signs in CORNER_SIGNS]


def cyclic_triple(triple):
    return min(triple, triple[1:] + triple[:1], triple[2:] + triple[:2])


def oriented_corners(cube):
    answer = []
    for signs, faces in zip(CORNER_SIGNS, CORNER_FACES):
        colours = tuple(cube[f] for f in faces)
        if sum(signs) % 2:
            colours = (colours[0], colours[2], colours[1])
        answer.append(cyclic_triple(colours))
    return answer


def corner_arc(corner):
    a, b = sorted(set(range(5)) - set(corner))
    return (a, b) if parity((a, b, *corner)) == 1 else (b, a)


def matching(row, sources):
    """Independent augmenting-path matching; return copy index per position."""
    corner_at_copy = [-1] * len(sources)

    def augment(corner, seen):
        for copy, source in enumerate(sources):
            if copy in seen or not (row[source] & (1 << corner)):
                continue
            seen.add(copy)
            old = corner_at_copy[copy]
            if old == -1 or augment(old, seen):
                corner_at_copy[copy] = corner
                return True
        return False

    for corner in range(8):
        if not augment(corner, set()):
            return None
    return [corner_at_copy.index(corner) for corner in range(8)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path,
                        default=None)
    args = parser.parse_args()
    if args.output is None:
        args.output = args.repo / 'build/checks/universal.json'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    geometry_file = args.repo / 'data/five-colour-geometry.txt'
    rows = [list(map(int, line.split())) for line in geometry_file.read_text().splitlines()]
    require(rows[0] == [75] and len(rows) == 151, 'Unexpected geometry format')
    cubes = [tuple(row) for row in rows[1:76]]
    retained_masks = rows[76:]
    require(all(len(c) == 6 for c in cubes), 'Incorrect face tuples')
    require(all(len(row) == 75 for row in retained_masks), 'Incorrect mask dimensions')
    rotations = physical_rotations()

    def rotated(cube, rotation):
        return tuple(cube[f] for f in rotation)

    def canonical(cube):
        return min(rotated(cube, rotation) for rotation in rotations)

    all_labelled = {cube for repeat in range(5)
                    for cube in permutations((*range(5), repeat))}
    require(len(all_labelled) == 1800, 'Wrong labelled-colouring count')
    reconstructed = sorted({canonical(c) for c in all_labelled})
    require(reconstructed == cubes, 'Physical rotation catalogue differs')
    oriented = [[rotated(cube, rotation) for rotation in rotations] for cube in cubes]

    physical_masks = []
    for target in cubes:
        row = []
        for source_orientations in oriented:
            mask = 0
            for position, faces in enumerate(CORNER_FACES):
                if any(all(source[f] == target[f] for f in faces)
                       for source in source_orientations):
                    mask |= 1 << position
            row.append(mask)
        physical_masks.append(row)
    require(physical_masks == retained_masks, 'Direct physical corner fits differ from retained masks')

    sources = []
    parameters = []
    opposite = []
    for index, cube in enumerate(cubes):
        repeat = next(colour for colour in range(5) if cube.count(colour) == 2)
        is_opposite = any(cube[2 * axis] == cube[2 * axis + 1] for axis in range(3))
        opposite.append(is_opposite)
        if is_opposite:
            continue
        corners = oriented_corners(cube)
        arcs = {corner_arc(c) for c in corners if len(set(c)) == 3}
        tails = {a for a, b in arcs}
        if len(tails) != 2:
            continue
        require(arcs == {(a, b) for a in tails for b in range(5) if b not in tails},
                'Positive adjacent variety is not its claimed cut')
        if (repeat + 1) % 5 in tails:
            sources.append(index)
            parameters.append({'index': index, 'faces': cube, 'repeat': repeat,
                               'pair': sorted(tails), 'sign': 'positive'})
    require(len(sources) == 15 and len(set(sources)) == 15, 'Expected fifteen distinct varieties')
    require(Counter(p['repeat'] for p in parameters) == Counter({r: 3 for r in range(5)}),
            'Expected three sources of each repeated colour')

    for repeat in range(5):
        hub = (repeat + 1) % 5
        expected = {tuple(sorted((hub, leaf)))
                    for leaf in range(5) if leaf not in (repeat, hub)}
        actual = {tuple(p['pair']) for p in parameters if p['repeat'] == repeat}
        require(actual == expected, 'Repeated-colour pairs are not the required star')
    weights = Counter(tuple(p['pair']) for p in parameters)
    require(set(weights) == set(combinations(range(5), 2)), 'Every pair must occur')
    require(set(weights.values()) == {1, 2}, 'Pair multiplicities must be one or two')
    degrees = [sum(w for pair, w in weights.items() if colour in pair) for colour in range(5)]
    require(degrees == [6] * 5, 'Each vertex must have weighted degree six')

    # Check the advertised production data against this independent geometry.
    dictionary = json.loads((args.repo / 'data/five-colour-universal.json').read_text())
    require(dictionary['face_order'] == ['+x','-x','+y','-y','+z','-z'], 'Face order differs')
    seeds = dictionary['seeds']
    require(len(seeds) == 3 and all(len(c) == 6 for c in seeds), 'Need three six-face seeds')
    advertised = dictionary['source_indices']
    derived = [cubes.index(canonical(tuple((c+r)%5 for c in seed)))
               for r in range(5) for seed in seeds]
    require(advertised == derived and sorted(advertised) == sources,
            'Advertised seeds or source indices differ from the cyclic-star construction')
    retained = dictionary['placements']
    require(len(retained) == 75, 'Need one matching per target')
    for t, placement in enumerate(retained):
        require(len(placement) == 8 and len(set(placement)) == 8 and
                all(type(i) is int and 0 <= i < 15 for i in placement),
                'Invalid physical-copy assignment')
        require(all(physical_masks[t][advertised[i]] & (1 << k)
                    for k,i in enumerate(placement)), 'Advertised placement does not fit')

    target_records = []
    tri_min_neighbours = {k: 16 for k in range(1, 9)}
    all_min_slack = 15
    for target_index, target in enumerate(cubes):
        row = physical_masks[target_index]
        assignment = matching(row, sources)
        require(assignment is not None, f'Unsolved target {target_index}')
        require(len(set(assignment)) == 8, 'Matching reuses a physical copy')
        placements = []
        for position, copy in enumerate(assignment):
            source = sources[copy]
            faces = CORNER_FACES[position]
            rotation_index = next(i for i, turned in enumerate(oriented[source])
                                  if all(turned[f] == target[f] for f in faces))
            placements.append({'corner': position, 'copy': copy, 'source': source,
                               'face_permutation': rotations[rotation_index]})
        tri_mask = sum(1 << position for position, corner in enumerate(oriented_corners(target))
                       if len(set(corner)) == 3)
        counts = []
        min_slack = 15
        for subset in range(1, 256):
            neighbours = sum(bool(row[source] & subset) for source in sources)
            count = subset.bit_count()
            require(neighbours >= count, f'Hall violation at target {target_index}, subset {subset}')
            counts.append(neighbours)
            min_slack = min(min_slack, neighbours - count)
            if subset & ~tri_mask == 0:
                tri_min_neighbours[count] = min(tri_min_neighbours[count], neighbours)
                required = 4 if count == 1 else 6 if count <= 4 else 8
                require(neighbours >= required, 'Structural tricolour bound failed')
        all_min_slack = min(all_min_slack, min_slack)
        target_records.append({'target_index': target_index, 'faces': target,
                               'kind': 'opposite' if opposite[target_index] else 'adjacent',
                               'placements': placements, 'minimum_Hall_slack': min_slack,
                               'neighbour_counts_for_subsets_1_to_255': counts})

    result = {
        'status': 'all checks passed; not a Lean formalization',
        'construction': 'For each r modulo 5, choose the three positive varieties with repeat r and pair {r+1,p}, p not in {r,r+1}.',
        'geometry_sha256': hashlib.sha256(geometry_file.read_bytes()).hexdigest(),
        'proper_rotations': len(rotations), 'labelled_face_colourings': len(all_labelled),
        'varieties': len(cubes), 'opposite_varieties': sum(opposite),
        'adjacent_varieties': 75 - sum(opposite),
        'physical_corner_masks_match_repository': True,
        'pool_size': len(sources), 'distinct_source_varieties': len(set(sources)),
        'source_indices': sources, 'source_parameters': parameters,
        'pair_weights': [{'pair': pair, 'weight': weight} for pair, weight in sorted(weights.items())],
        'weighted_degrees': degrees,
        'minimum_tricolour_neighbours_by_subset_size': tri_min_neighbours,
        'all_target_Hall_sets_checked': 75 * 255,
        'physical_placements_checked': 75 * 8,
        'minimum_Hall_slack': all_min_slack,
        'targets': target_records,
        'elapsed_seconds': time.monotonic() - start,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('targets', 'source_parameters', 'pair_weights')}, indent=2))
    print(args.output)


if __name__ == '__main__':
    main()
