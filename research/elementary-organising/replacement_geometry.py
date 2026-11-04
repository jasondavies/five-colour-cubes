from itertools import combinations, combinations_with_replacement
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'elementary-review-2026-11-04/research/root'))
from cut_model import CUTS, CORNERS, CLASSES, OPP
arcs = [('t', a, b) for a in range(5) for b in range(5) if a != b]
def mask(s):
    return sum(1 << arcs.index(c) for c in s if c[0] == 't')
cuts = list(map(mask, CUTS))
ops = list(map(mask, CORNERS[60:]))
