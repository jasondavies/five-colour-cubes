#!/usr/bin/env python3
"""Draw the fourteen-cube obstruction as TikZ (paper) and SVG (README).

Varieties and multiplicities are read from `FiveColour/Problem.lean` and
checked against the obstruction fixture. Corner types come from the
determinant-positive rotation model in `cube_geometry.py`, and the private-corner
counts shown in the figure are checked to exceed the available copies. With
--check, the committed outputs must equal freshly generated ones.
"""
from html import escape
import json
import math
from pathlib import Path
import re
import sys

from cube_geometry import corners, require

ROOT = Path(__file__).resolve().parents[1]
OUTPUTS = ('obstruction-figure.tex', 'obstruction-figure.svg')
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
        colours = {'#111': 'black!93', '#222': 'black!87', '#666': 'black!60',
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
                value = value.replace('×', r'\(\times\)').replace('≥', r'\(\ge\)')
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


TITLE = 'Why four A, five B and five C cubes cannot build a five-colour target'
DESCRIPTION = ('The only possible targets are A, B and C themselves. Target A has five corner '
               'types that occur on no other variety, so it needs five A cubes, but only four '
               'are available. Targets B and C each have six private corner types but only '
               'five copies.')


def render(directory):
    rows = private_split(obstruction())
    return {directory / OUTPUTS[0]: illustration(rows, notes=False).tikz(),
            directory / OUTPUTS[1]: illustration(rows, notes=True).svg(TITLE, DESCRIPTION)}


def main():
    if sys.argv[1:] == ['--check']:
        for path, text in render(ROOT / 'paper').items():
            require(path.read_text(encoding='utf-8') == text, f'{path.name} is stale; run make figure')
        print('Obstruction figure matches Lean, fixture and corner geometry.')
        return
    require(len(sys.argv) <= 2, 'usage: generate_five_colour_figure.py [--check | DIRECTORY]')
    directory = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT / 'paper'
    for path, text in render(directory).items():
        path.write_text(text, encoding='utf-8')


if __name__ == '__main__':
    main()
