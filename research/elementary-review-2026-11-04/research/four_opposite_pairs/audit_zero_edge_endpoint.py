"""Verify the small tables in one-double-zero-edge-endpoint.md."""
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CORNERS, CUTS


def arc(s):
    return ('t', int(s[0]), int(s[1]))


rectangles = [
    ('01', '24', ['14', '02', '12', '04']),
    ('02', '14', ['24', '01', '21', '04']),
    ('04', '12', ['02', '01', '41', '42']),
    ('12', '04', ['20', '10', '14', '24']),
    ('13', '04', ['14', '10', '34', '30']),
    ('14', '02', ['42', '10', '12', '40']),
    ('23', '04', ['24', '20', '34', '30']),
    ('24', '01', ['41', '20', '21', '40']),
]
for poles, columns, words in rectangles:
    positions = {('t', int(a), int(b)) for a in poles for b in columns}
    assert positions == set(map(arc, words))
    assert all(arc(c) in CORNERS[s] for c, s in zip(words, [71, 71, 61, 63]))

bad = {4, 5, 18, 19}
target = CORNERS[71]
reserved = {arc('01'), arc('02')}
first_claims = {
    '01': [4], '02': [4],
    '14': [0, 4, 11, 17], '24': [2, 4, 13, 15],
}
for edge, expected in first_claims.items():
    permitted = reserved | {arc(edge), arc(edge[::-1])}
    actual = [j for j, c in enumerate(CUTS) if c & target <= permitted]
    assert actual == expected
    assert sum(3 if j in bad else 1 for j in actual) < 10

E = set(map(arc, ['01', '10', '02', '20']))
second_claims = {
    '01': [2, 11, 13, 18, 19],
    '02': [0, 15, 17, 18, 19],
    '10': [3, 10, 12, 18, 19],
    '20': [1, 14, 16, 18, 19],
}
for corner, expected in second_claims.items():
    actual = [j for j, c in enumerate(CUTS) if c & E <= {arc(corner)}]
    assert actual == expected
    assert sum(3 if j in bad else 1 for j in actual) == 9

report = {'status': 'passed', 'rectangle_witnesses': len(rectangles),
          'residual_family_rows': len(first_claims) + len(second_claims),
          'proof_dependency': 'none; check of displayed tables'}
Path(__file__).with_name('zero-edge-endpoint-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
