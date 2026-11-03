#!/usr/bin/env python3
"""Regenerate the small signed-corner tables; Lean checks them against physical incidence."""
import argparse
from pathlib import Path
import re
r = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
C=[tuple(map(int,x.split(','))) for x in re.findall(r'!\[([0-4, ]+)\]',(r/'FiveColour/CatalogueData.lean').read_text())]
family=[list(map(int,x.split(','))) for x in re.findall(r'!\[([0-9,]+)\]',(r/'FiveColour/RingData.lean').read_text().split('def cornerMap')[0])]
pairs=[(a,b) for a in range(5) for b in range(a+1,5)]
def cyclic(x):return min(x,x[1:]+x[:1],x[2:]+x[:2])
def corners(c):
 out=[]
 for a in range(2):
  for b in range(2):
   for d in range(2):
    x=(c[a],c[2+b],c[4+d])
    if (a+b+d)%2:x=x[0],x[2],x[1]
    out.append(cyclic(x))
 return out
keys=list(map(corners,C))
positive=[(0,2,3),(1,3,2),(0,4,2),(1,2,4),(0,3,4),(1,4,3)]
bits=[];slots=[]
for pi,(a,b) in enumerate(pairs):
 perm=[a,b]+[c for c in range(5) if c!=a and c!=b]
 bitSigns=[];slotSigns=[]
 for sign in range(2):
  want=[cyclic(tuple(perm[x] for x in (c if not sign else (c[0],c[2],c[1])))) for c in positive]
  bitSigns.append([sum(1<<j for j,x in enumerate(want) if x in kk) for kk in keys])
  slotSigns.append([[keys[s].index(x) if x in keys[s] else 0 for x in want] for s in family[pi]])
 bits.append(bitSigns);slots.append(slotSigns)
def vec(x):return '!['+','.join(vec(v) if isinstance(v,list) else str(v) for v in x)+']'
s='''module
public import FiveColour.RingEleven
@[expose] public section
namespace FiveColour.Physical.Projection
/-- Six common corner types, grouped in pairs by their two ring colours.
Sign 0 is positive, sign 1 negative. All data are checked in ProjectionGeometry. -/
'''
s+='def bits : Fin 10 → Fin 2 → Fin 75 → ℕ := '+vec(bits)+'\n'
s+='def cornerSlot : Fin 10 → Fin 2 → Fin 9 → Fin 6 → Fin 8 := '+vec(slots)+'\n'
s+='''def side (sign : Fin 2) (t : Fin 9) : Prop := 3 + 3*sign.val ≤ t.val ∧ t.val < 6 + 3*sign.val
instance (sign : Fin 2) : DecidablePred (side sign) := by intro t; unfold side; infer_instance
def other (sign : Fin 2) : Fin 2 := 1-sign
abbrev Half (r : Fin 3) := {j : Fin 6 // j.val / 2 ≠ r.val}
def target (r : Fin 3) : Fin 9 := ![2,1,0] r
def present (sign : Fin 2) (t : Fin 9) (j : Fin 6) : Prop :=
  side sign t ∨ (t.val < 3 ∧ j.val / 2 ≠ 2-t.val)
instance (sign : Fin 2) (t : Fin 9) : DecidablePred (present sign t) := by
  intro j; unfold present; infer_instance
def Fits (p : Fin 10) (sign : Fin 2) (w : Fin 75) (j : Fin 6) : Prop :=
  (bits p sign w).testBit j.val = true
instance (p : Fin 10) (sign : Fin 2) (w : Fin 75) : DecidablePred (Fits p sign w) := by
  intro j; unfold Fits; infer_instance
def count (p : Fin 10) (sign : Fin 2) (w : Fin 75) := (Finset.univ.filter (Fits p sign w)).card
end FiveColour.Physical.Projection
'''
target = r / 'FiveColour/ProjectionData.lean'
if args.check:
    if target.read_text() != s:
        raise SystemExit('ProjectionData.lean differs from regenerated signed-corner tables')
    print('Signed-corner tables match (10 families, 2 signs, 75 varieties).')
else:
    target.write_text(s)

