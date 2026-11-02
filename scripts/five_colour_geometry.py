#!/usr/bin/env python3
"""Export five-colour incidence data for the compiled obstruction search."""
import itertools
from pathlib import Path
from cube_geometry import canonical, corners


def main():
    cubes = sorted({canonical(c) for c in itertools.product(range(5), repeat=6)
                    if len(set(c)) == 5})
    assert len(cubes) == 75
    corner_sets = [set(corners(c)) for c in cubes]
    lines = [str(len(cubes))]
    lines += [' '.join(map(str, c)) for c in cubes]
    # Rows are targets, columns sources; bit k means source fits target slot k.
    for target in cubes:
        tc = corners(target)
        lines.append(' '.join(str(sum(1 << k for k, c in enumerate(tc) if c in cs))
                              for cs in corner_sets))
    out = Path('data/five-colour-geometry.txt')
    out.write_text('\n'.join(lines) + '\n')
    print(out)


if __name__ == '__main__':
    main()
