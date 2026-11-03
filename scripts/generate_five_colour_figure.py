#!/usr/bin/env python3
"""Draw both lower-bound obstructions as TikZ (paper) and SVG (README).

The fourteen-cube corner obstruction is read from `FiveColour/Problem.lean`
and checked against its fixture. The uniform cuboid obstruction U+(τ+5)V+(τ+6)W
is read from `FiveColour/BoxLowerBound.lean` and the catalogue, and checked
against the faces stated in `paper/boxes.tex`. Corner types come from the
determinant-positive rotation model in `cube_geometry.py`. The private corner
and edge counts drawn are recomputed and checked to exceed the available
copies. With --check, the committed outputs must equal freshly generated ones.
"""
from html import escape
import json
import math
from pathlib import Path
import re
import sys

from cube_geometry import corners, require

ROOT = Path(__file__).resolve().parents[1]
OUTPUTS = ('obstruction-figure.tex', 'obstruction-figure.svg',
           'uniform-obstruction.tex', 'uniform-obstruction.svg')
# Okabe-Ito colours: distinguishable with colour-blindness, and dark digits stay
# legible on each. Digits carry the colour identity in greyscale.
COLOURS = ('E69F00', '56B4E9', '009E73', 'F0E442', 'CC79A7')
# Shared corners are drawn as this fraction of full colour over white.
FADE = 0.3
# (column, row) -> face index in the order +x,-x,+y,-y,+z,-z. Seen from outside
# with +z up, +y lies to the right of +x. Swapping sides would draw the mirror.
NET = {(1, 0): 4, (0, 1): 3, (1, 1): 0, (2, 1): 2, (3, 1): 1, (1, 2): 5}


def obstruction():
    """Return [(name, faces, copies)], read from Lean and checked against the fixture."""
    source = (ROOT / 'FiveColour/Problem.lean').read_text(encoding='utf-8')
    cubes = {name: tuple(map(int, faces.split(','))) for name, faces in
             re.findall(r'^def cube([ABC]) : Cube := !\[([0-9,]+)\]$', source, re.M)}
    family = re.search(r'def lowerFamily \(i : Fin (\d+)\) : Cube :=\s*'
                       r'if i\.val < (\d+) then cubeA else if i\.val < (\d+) then cubeB '
                       r'else cubeC', source)
    require(sorted(cubes) == ['A', 'B', 'C'] and family, 'lowerFamily not found')
    size, a, b = map(int, family.groups())
    result = [('A', cubes['A'], a), ('B', cubes['B'], b - a), ('C', cubes['C'], size - b)]
    fixture = json.loads((ROOT / 'data/q5-three-variety-obstruction.json').read_text(encoding='utf-8'))
    require(fixture['size'] == size == 14, 'Unexpected obstruction size')
    require([(tuple(e['faces']), e['count']) for e in fixture['collection']]
            == [(faces, copies) for _, faces, copies in result], 'Fixture differs from lowerFamily')
    return result


def private_split(varieties):
    """Split each variety's corner positions into private and shared types."""
    rows = []
    for name, faces, copies in varieties:
        others = {t for other, f, _ in varieties if other != name for t in corners(f)}
        types = corners(faces)
        private = sorted(t for t in types if t not in others)
        shared = sorted(t for t in types if t in others)
        require(len(private) > copies, f'{name} has too few private corners to fail')
        rows.append((name, faces, copies, private, shared))
    require([len(r[3]) for r in rows] == [5, 6, 6], 'Unexpected private corner counts')
    return rows


def word(values):
    return ''.join(map(str, values))


def number(value):
    return f'{value:.3f}'.rstrip('0').rstrip('.')


class Drawing:
    """One vector scene, emitted as either SVG or TikZ."""
    def __init__(self, width, height):
        self.width, self.height = width, height
        self.items = []

    def polygon(self, points, fill, stroke='#222', width=1.2, fade=False):
        self.items.append(('polygon', points, fill, stroke, width, fade))

    def line(self, points, stroke='#ccc', width=1.2):
        self.items.append(('line', points, stroke, width))

    def text(self, x, y, value, size=18, bold=False, anchor='middle', colour='#111'):
        self.items.append(('text', x, y, str(value), size, bold, anchor, colour))

    def svg(self, title, description):
        out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.width}" '
               f'height="{self.height}" viewBox="0 0 {self.width} {self.height}" '
               'role="img" aria-labelledby="title description">',
               f'<title id="title">{escape(title)}</title>',
               f'<desc id="description">{escape(description)}</desc>',
               '<rect width="100%" height="100%" fill="white"/>',
               '<g font-family="Helvetica,Arial,sans-serif" stroke-linejoin="round">']
        for kind, *args in self.items:
            if kind == 'text':
                x, y, value, size, bold, anchor, colour = args
                weight = 'bold' if bold else 'normal'
                out.append(f'<text x="{number(x)}" y="{number(y)}" font-size="{size}" '
                           f'font-weight="{weight}" text-anchor="{anchor}" fill="{colour}" '
                           f'dy="0.35em">{escape(value)}</text>')
            elif kind == 'polygon':
                points, fill, stroke, width, fade = args
                points = ' '.join(f'{number(x)},{number(y)}' for x, y in points)
                opacity = f' fill-opacity="{FADE}"' if fade else ''
                out.append(f'<polygon points="{points}" fill="{fill}"{opacity} '
                           f'stroke="{stroke}" stroke-width="{width}"/>')
            else:
                points, stroke, width = args
                points = ' '.join(f'{number(x)},{number(y)}' for x, y in points)
                out.append(f'<polyline points="{points}" fill="none" stroke="{stroke}" '
                           f'stroke-width="{width}"/>')
        return '\n'.join(out + ['</g>', '</svg>']) + '\n'

    def tikz(self):
        # 158 mm fits the paper's 160 mm text block. Font sizes scale with geometry.
        scale = 158 / self.width
        point_scale = scale * 72.27 / 25.4
        colours = {'#111': 'black!93', '#222': 'black!87', '#666': 'black!60', '#eee': 'black!7',
                   '#999': 'black!40', '#ccc': 'black!20',
                   **{f'#{c}': f'cube{i}' for i, c in enumerate(COLOURS)}}
        def point(p):
            return f'({number(p[0])},{number(p[1])})'
        out = ['% Generated by scripts/generate_five_colour_figure.py; do not edit.']
        out += [f'\\definecolor{{cube{i}}}{{HTML}}{{{c}}}' for i, c in enumerate(COLOURS)]
        out.append(f'\\begin{{tikzpicture}}[x={number(scale)}mm,y=-{number(scale)}mm]')
        out.append(f'\\path[use as bounding box] (0,0) rectangle ({self.width},{self.height});')
        for kind, *args in self.items:
            if kind == 'text':
                x, y, value, size, bold, anchor, colour = args
                value = (value.replace('×', r'\(\times\)').replace('≥', r'\(\ge\)')
                         .replace('τ', r'\(\tau\)'))
                anchor = {'middle': 'center', 'start': 'west', 'end': 'east'}[anchor]
                # Standard Computer Modern sizes avoid font substitution warnings.
                size = min((8, 9, 10, 10.95, 12), key=lambda s: abs(s - size * point_scale))
                font = rf'\sffamily\fontsize{{{number(size)}}}{{{number(size * 1.2)}}}\selectfont'
                if bold:
                    font += r'\bfseries'
                out.append(f'\\node[anchor={anchor},inner sep=0pt,outer sep=0pt,'
                           f'text={colours[colour]},font={{{font}}}] at {point((x, y))} {{{value}}};')
            elif kind == 'polygon':
                points, fill, stroke, width, fade = args
                fill = colours[fill] + (f'!{round(100 * FADE)}' if fade else '')
                path = ' -- '.join(point(p) for p in points) + ' -- cycle'
                out.append(f'\\draw[fill={fill},draw={colours[stroke]},line join=round,'
                           f'line width={number(width * point_scale)}pt] {path};')
            else:
                points, stroke, width = args
                path = ' -- '.join(point(p) for p in points)
                out.append(f'\\draw[draw={colours[stroke]},line width={number(width * point_scale)}pt] {path};')
        return '\n'.join(out + ['\\end{tikzpicture}']) + '\n'


def net(d, cube, x, y, unit):
    for (col, row), face in NET.items():
        left, top = x + col * unit, y + row * unit
        d.polygon([(left, top), (left + unit, top), (left + unit, top + unit), (left, top + unit)],
                  f'#{COLOURS[cube[face]]}')
        d.text(left + unit / 2, top + unit / 2, cube[face], size=17)


def corner(d, triple, x, y, unit, fade):
    """Three outside faces around a vertex; left, right, top read counterclockwise."""
    side = math.sqrt(3) * unit / 2
    polygons = (
        [(0, 0), (-side, -unit / 2), (-side, unit / 2), (0, unit)],
        [(0, 0), (0, unit), (side, unit / 2), (side, -unit / 2)],
        [(0, 0), (side, -unit / 2), (0, -unit), (-side, -unit / 2)],
    )
    ink = '#666' if fade else '#111'
    for colour, points in zip(triple, polygons):
        d.polygon([(x + px, y + py) for px, py in points], f'#{COLOURS[colour]}',
                  stroke='#999' if fade else '#222', fade=fade)
        d.text(x + sum(px for px, _ in points) / 4, y + sum(py for _, py in points) / 4,
               colour, size=15, colour=ink)
    d.text(x, y + unit + 15, word(triple), size=16, colour=ink)


def illustration(rows, notes):
    """The paper caption replaces the notes in the TikZ version."""
    d = Drawing(800, 512 if notes else 470)
    d.text(72, 22, 'Collection', size=17, bold=True)
    d.text(372, 22, 'Corner types of each variety', size=17, bold=True)
    d.text(604, 22, 'Why it fails', size=17, bold=True, anchor='start')
    for i, (name, faces, copies, private, shared) in enumerate(rows):
        top = 46 + 140 * i
        d.line([(16, top - 6), (784, top - 6)])
        net(d, faces, 24, top + 8, 24)
        d.text(72, top + 102, f'{copies} × {name}', size=18, bold=True)
        d.text(72, top + 124, word(faces), size=16)
        for j, triple in enumerate(private + shared):
            corner(d, triple, 180 + 54 * j, top + 50, 20, fade=j >= len(private))
        # Bracket the private corners, which only this variety can fill.
        left, right = 180 - 22, 180 + 54 * (len(private) - 1) + 22
        d.line([(left, top + 98), (left, top + 104), (right, top + 104), (right, top + 98)],
               stroke='#222', width=1.4)
        d.text((left + right) / 2, top + 122, f'{len(private)} private', size=16, bold=True)
        d.text(604, top + 40, f'{len(private)} corners need {name};', size=17, anchor='start')
        d.text(604, top + 66, f'only {copies} copies.', size=17, bold=True, anchor='start')
    d.line([(16, 466), (784, 466)])
    for y, note in ((482, 'Corners are read counterclockwise from outside. Faded types also '
                          'occur on another variety.'),
                    (500, 'Each net folds away from you; its centre face is +x. '
                          'The paper shows that only A, B and C can be targets.')):
        if notes:
            d.text(16, y, note, size=14, anchor='start', colour='#666')
    return d


def uniform_obstruction():
    """Return [(name, faces, copies label, pool)] for U+(τ+5)V+(τ+6)W."""
    data = (ROOT / 'FiveColour/CatalogueData.lean').read_text(encoding='utf-8')
    body = re.search(r'def catalogue : Fin 75 → Cube :=\s*!\[(.*?)\]\n', data, re.S).group(1)
    catalogue = [tuple(map(int, c.split(','))) for c in re.findall(r'!\[([0-9,]+)\]', body)]
    require(len(catalogue) == 75, 'Catalogue not found')
    lean = (ROOT / 'FiveColour/BoxLowerBound.lean').read_text(encoding='utf-8')
    source = re.search(r'def boxLowerSource .*?\n\n', lean, re.S).group(0)
    pools = re.search(r'lowerPool_card .*?= !\[1,S\+6,S\+6\] j', lean, re.S)
    indices = list(map(int, re.findall(r'catalogue (\d+)', source)))
    require(len(indices) == 3 and pools and 'Fin 1 ⊕ (Fin (S+5) ⊕ Fin (S+6))' in lean,
            'boxLowerSource not found')
    paper = (ROOT / 'paper/boxes.tex').read_text(encoding='utf-8')
    stated = dict(re.findall(r'([UVW])=\(([0-9,]+)\)', paper))
    names = 'UVW'
    require([tuple(map(int, stated[n].split(','))) for n in names]
            == [catalogue[i] for i in indices], 'Paper U,V,W differ from boxLowerSource')
    copies = ('1', '(τ+5)', '(τ+6)')
    # The cubes each target may use (U alone, U or V, W alone) and their numbers,
    # as in lowerPool_card.
    pools = (('U', '1'), ('UV', 'τ+6'), ('W', 'τ+6'))
    return [(n, catalogue[i], c, p) for n, i, c, p in zip(names, indices, copies, pools)]


def edge_types(cube):
    """Unordered colours on each geometric edge, keyed by the edge's axis."""
    return [(3 - f // 2 - g // 2, tuple(sorted((cube[f], cube[g]))))
            for f in range(0, 6) for g in range(f + 1, 6) if f // 2 != g // 2]


def uniform_split(varieties):
    """Corner and edge types of each target that only its pool supplies."""
    rows = []
    for name, faces, copies, pool in varieties:
        outside = [f for other, f, _, _ in varieties if other not in pool[0]]
        corner_types = {t for f in outside for t in corners(f)}
        edge_pairs = {t for f in outside for _, t in edge_types(f)}
        types = corners(faces)
        require(len(set(types)) == 8, f'{name} has repeated corner types')
        private = sorted(t for t in types if t not in corner_types)
        shared = sorted(t for t in types if t in corner_types)
        edges = sorted((axis, t) for axis, t in edge_types(faces) if t not in edge_pairs)
        if name == 'U':
            edges = []  # Two private corners already exceed the single copy.
        else:
            # One edge per axis gives τ = a+b+c-6 positions in every orientation.
            require([axis for axis, _ in edges] == [0, 1, 2], f'{name} edge pattern changed')
        rows.append((name, faces, copies, pool, private, shared, [t for _, t in edges]))
    require([(len(r[4]), r[6]) for r in rows]
            == [(2, []), (7, [(1, 4), (1, 4), (1, 1)]), (7, [(3, 4), (3, 3), (3, 4)])],
            'Unexpected private corner or edge counts')
    edges_in_paper = re.findall(r'these are \$(\d\d),(\d\d),(\d\d)\$',
                                (ROOT / 'paper/boxes.tex').read_text(encoding='utf-8'))
    edges_in_paper += re.findall(r'now\s+\$(\d\d),(\d\d),(\d\d)\$',
                                 (ROOT / 'paper/boxes.tex').read_text(encoding='utf-8'))
    require([[tuple(map(int, e)) for e in group] for group in edges_in_paper]
            == [rows[1][6], rows[2][6]], 'Paper private edge types differ')
    return rows


def edge(d, pair, x, y, unit):
    """Two faces meeting along a vertical edge, under a neutral top face."""
    side = math.sqrt(3) * unit / 2
    label, y = y + unit + 15, y + unit / 2  # Centre the glyph on the corner row.
    d.polygon([(x, y - unit / 2), (x + side, y - unit), (x, y - 3 * unit / 2),
               (x - side, y - unit)], '#eee', stroke='#999')
    polygons = ([(0, -unit / 2), (-side, -unit), (-side, 0), (0, unit / 2)],
                [(0, -unit / 2), (0, unit / 2), (side, 0), (side, -unit)])
    for colour, points in zip(pair, polygons):
        d.polygon([(x + px, y + py) for px, py in points], f'#{COLOURS[colour]}')
        d.text(x + sum(px for px, _ in points) / 4, y + sum(py for _, py in points) / 4,
               colour, size=15)
    d.text(x, label, word(pair), size=16)


def bracket(d, left, right, y, label):
    d.line([(left, y - 6), (left, y), (right, y), (right, y - 6)], stroke='#222', width=1.4)
    d.text((left + right) / 2, y + 18, label, size=16, bold=True)


def uniform_illustration(rows, notes):
    d = Drawing(900, 512 if notes else 470)
    step, first, edge_x, why = 48, 180, 576, 716
    d.text(72, 22, 'Collection', size=17, bold=True)
    d.text(first + 3.5 * step, 22, 'Corner types of each target', size=17, bold=True)
    d.text(edge_x + step, 22, 'Edge types', size=17, bold=True)
    d.text(why, 22, 'Why it fails', size=17, bold=True, anchor='start')
    for i, (name, faces, copies, pool, private, shared, edges) in enumerate(rows):
        top = 46 + 140 * i
        d.line([(16, top - 6), (884, top - 6)])
        net(d, faces, 24, top + 8, 24)
        d.text(72, top + 102, f'{copies} × {name}', size=18, bold=True)
        d.text(72, top + 124, word(faces), size=16)
        for j, triple in enumerate(private + shared):
            corner(d, triple, first + step * j, top + 50, 20, fade=j >= len(private))
        bracket(d, first - 22, first + step * (len(private) - 1) + 22, top + 104,
                f'{len(private)} private')
        for j, pair in enumerate(edges):
            edge(d, pair, edge_x + step * j, top + 50, 20)
        if edges:
            bracket(d, edge_x - 22, edge_x + step * (len(edges) - 1) + 22, top + 104,
                    'one per axis')
        users, available = pool
        users = ' or '.join(users)
        lines = (f'{len(private)} + τ positions' if edges else f'{len(private)} corners',
                 f'need {users};',
                 f"only {available} {'copy' if available == '1' else 'copies'}.")
        for k, line in enumerate(lines):
            d.text(why, top + 30 + 24 * k, line, size=17, bold=k == 2, anchor='start')
    d.line([(16, 466), (884, 466)])
    for y, note in ((482, 'τ = a+b+c−6 counts the noncorner positions on one edge in each direction. '
                          'Faded corners also occur outside the pool.'),
                    (500, 'Only U, V and W can be targets. For a+b+c = 8 there are sixteen cubes, '
                          'so 2×2×4 and 2×3×3 frames need seventeen.')):
        if notes:
            d.text(16, y, note, size=14, anchor='start', colour='#666')
    return d


TITLE = 'Why four A, five B and five C cubes cannot build a five-colour target'
DESCRIPTION = ('The only possible targets are A, B and C themselves. Target A has five corner '
               'types that occur on no other variety, so it needs five A cubes, but only four '
               'are available. Targets B and C each have six private corner types but only '
               'five copies.')


UNIFORM_TITLE = 'Why U, τ+5 copies of V and τ+6 copies of W cannot build an a×b×c frame'
UNIFORM_DESCRIPTION = ('Here τ = a+b+c-6. Only U, V and W can be targets. Target U has two '
                       'corner types that only U supplies, but there is one U. Targets V and W '
                       'each have seven private corner types and one private edge type per '
                       'axis, so τ+7 positions need a cube from a pool of only τ+6.')


def render(directory):
    rows = private_split(obstruction())
    uniform = uniform_split(uniform_obstruction())
    return {directory / OUTPUTS[0]: illustration(rows, notes=False).tikz(),
            directory / OUTPUTS[1]: illustration(rows, notes=True).svg(TITLE, DESCRIPTION),
            directory / OUTPUTS[2]: uniform_illustration(uniform, notes=False).tikz(),
            directory / OUTPUTS[3]: uniform_illustration(uniform, notes=True).svg(
                UNIFORM_TITLE, UNIFORM_DESCRIPTION)}


def main():
    if sys.argv[1:] == ['--check']:
        for path, text in render(ROOT / 'paper').items():
            require(path.read_text(encoding='utf-8') == text, f'{path.name} is stale; run make figure')
        print('Obstruction figures match Lean, the paper, fixtures and corner geometry.')
        return
    require(len(sys.argv) <= 2, 'usage: generate_five_colour_figure.py [--check | DIRECTORY]')
    directory = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT / 'paper'
    for path, text in render(directory).items():
        path.write_text(text, encoding='utf-8')


if __name__ == '__main__':
    main()
