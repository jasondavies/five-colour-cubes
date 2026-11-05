#!/usr/bin/env python3
"""Explicit witnesses for the 5,402 normalised three-variety candidates.

Every positive record is an injection from eight corners to fourteen physical
copies. Every negative record gives a global symmetry of one of five examples.
The Lean checker verifies both possibilities, rather than trusting enumeration.
"""
import argparse,itertools,json
from pathlib import Path
from cube_geometry import ROT,canonical
ROOT=Path(__file__).resolve().parents[1]

def render():
    lines=(ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
    faces=[tuple(map(int,x.split())) for x in lines[1:76]]
    fits=[list(map(int,x.split())) for x in lines[76:]]
    lookup={canonical(f):i for i,f in enumerate(faces)}
    bs=[faces.index(f) for f in [(0,1,2,3,2,4),(0,1,2,3,3,4),(0,1,2,4,3,4)]]
    cs=[faces.index(f) for f in [(0,3,1,2,4,1),(0,3,1,2,4,2),(0,3,1,4,4,2)]]
    reps=[(bs[0],cs[0]),(bs[0],cs[2]),(bs[1],cs[0]),(bs[1],cs[1]),(bs[2],cs[1])]
    actions=[]
    for p in itertools.permutations(range(5)):
        if lookup[canonical(tuple(p[x] for x in faces[0]))]!=0:continue
        for mirror in [False,True]:
            def act(f):
                q=tuple(p[x] for x in f)
                if mirror:q=(q[1],q[0],*q[2:])
                return lookup[canonical(q)]
            actions.append([act(f) for f in faces])
    assert len(actions)==16
    orbit={}
    for j,(b,c) in enumerate(reps):
        for g,act in enumerate(actions):
            x,y=act[b],act[c]
            key=(min(x,y),max(x,y))
            if key in orbit:assert orbit[key][0]==j
            orbit[key]=(j,g,x>y)
    assert len(orbit)==56
    def match(a,b,c,t):
        sources=[a]*4+[b]*5+[c]*5;owned=[-1]*14
        def aug(k,seen):
            for i,s in enumerate(sources):
                if i in seen or not (fits[t][s]>>k)&1:continue
                seen.add(i)
                if owned[i]<0 or aug(owned[i],seen):owned[i]=k;return True
            return False
        if not all(aug(k,set()) for k in range(8)):return None
        return [owned.index(k) for k in range(8)]
    vec=lambda xs:'!['+','.join(map(str,xs))+']'
    pre='module\npublic import FiveColour.ExtremalTriples\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace FiveColour.Physical\n'
    text=pre+'\ndef extremalB : Fin 5 → Fin 75 := '+vec(b for b,c in reps)+'\ndef extremalC : Fin 5 → Fin 75 := '+vec(c for b,c in reps)+'''\n
def tripleAnchor : Fin 2 → Fin 75 := ![0,3]

inductive TripleReduction where
  | solve (placement : TriplePlacement)
  | orbit (representative : Fin 5) (symmetry : Fin 16) (swap : Bool)
  deriving Inhabited

def TripleReduction.Valid (a b c : Fin 75) : TripleReduction → Prop
  | .solve w => w.Valid a b c
  | .orbit j g swap => a = 0 ∧
      b = stabiliserAction g (if swap then extremalC j else extremalB j) ∧
      c = stabiliserAction g (if swap then extremalB j else extremalC j)
instance instDecidableTripleReductionValid (a b c : Fin 75) (w : TripleReduction) : Decidable (w.Valid a b c) := by
  cases w <;> unfold TripleReduction.Valid <;> infer_instance
'''
    tables=[];positive=0
    for a in [0,3]:
        rows=[]
        for b in range(75):
            row=[]
            for c in range(75):
                if b>=c or a in (b,c):w='.solve ⟨0,'+vec([0]*8)+'⟩'
                elif a==0 and (b,c) in orbit:
                    j,g,swap=orbit[b,c];w=f'.orbit {j} {g} {str(swap).lower()}'
                else:
                    for t in dict.fromkeys([a,b,c]+list(range(75))):
                        result=match(a,b,c,t)
                        if result is not None:break
                    assert result is not None,(a,b,c)
                    positive+=1;w=f'.solve ⟨{t},{vec(result)}⟩'
                row.append('('+w+')')
            rows.append(vec(row))
        tables.append(vec(rows))
    assert positive==5346
    text+='\ndef tripleReduction : Fin 2 → Fin 75 → Fin 75 → TripleReduction :=\n'+vec(tables)+'\n'
    cuts=[]
    for b,c in reps:
        row=[]
        for t in range(75):
            mask=next(d for d in range(1,256) if
                sum(n for s,n in [(0,4),(b,5),(c,5)] if fits[t][s]&d)<d.bit_count())
            row.append(mask)
        cuts.append(vec(row))
    text+='\ndef extremalDeficit : Fin 5 → Fin 75 → ℕ :=\n'+vec(cuts)+'\nend FiveColour.Physical\n'
    output={'FiveColour/ExtremalTripleData.lean':text}
    for kind in range(2):
        for block in range(3):
            text=pre.replace('FiveColour.ExtremalTriples','FiveColour.ExtremalTripleData')
            for b in range(block*25,(block+1)*25):
                text+=f'''\nlemma triple_reduction_{kind}_{b} : ∀ c : Fin 75,
    {b} < c → tripleAnchor {kind} ≠ {b} → tripleAnchor {kind} ≠ c →
      (tripleReduction {kind} {b} c).Valid (tripleAnchor {kind}) {b} c := by decide +kernel
'''
            output[f'FiveColour/ExtremalTripleChecks{kind}{block}.lean']=text+'\nend FiveColour.Physical\n'
    text='module\n'+''.join(f'public import FiveColour.ExtremalTripleChecks{k}{g}\n' for k in range(2) for g in range(3))+'''@[expose] public section
namespace FiveColour.Physical

theorem triple_reductions_valid (kind : Fin 2) (b c : Fin 75)
    (hbc : b < c) (hab : tripleAnchor kind ≠ b) (hac : tripleAnchor kind ≠ c) :
    (tripleReduction kind b c).Valid (tripleAnchor kind) b c := by
  fin_cases kind <;> fin_cases b
'''+''.join(f'  · exact triple_reduction_{k}_{b} c hbc hab hac\n' for k in range(2) for b in range(75))+'end FiveColour.Physical\n'
    output['FiveColour/ExtremalTripleChecks.lean']=text
    parts=[(x,y,5-x-y) for x in range(6) for y in range(6-x)]
    family_cuts=[]
    for x in parts:
        rows=[]
        for y in parts:
            if x[0]*y[1] or x[2]*y[2]: rows.append(vec([0]*75));continue
            inventory=[(0,4)]+list(zip(bs+cs,x+y))
            rows.append(vec(next(d for d in range(1,256) if sum(n for i,n in inventory if fits[t][i]&d)<d.bit_count()) for t in range(75)))
        family_cuts.append(vec(rows))
    text=pre.replace('FiveColour.ExtremalTriples','FiveColour.ExtremalFamily')
    text+='\ndef generalizedDeficit : Fin 21 → Fin 21 → Fin 75 → ℕ :=\n'+vec(family_cuts)+'\n'
    text+='\nlemma generalized_deficits (i : Fin 21) : ∀ j : Fin 21,\n    disjointRepeats (extremalDistribution i) (extremalDistribution j) → ∀ t : Fin 75,\n    generalizedDeficit i j t < 256 ∧\n    (generalizedMaskNeighbours (extremalDistribution i) (extremalDistribution j) t\n      (generalizedDeficit i j t)).card < (cornerSet (generalizedDeficit i j t)).card := by\n  fin_cases i <;> decide +kernel\n\nend FiveColour.Physical\n'
    output['FiveColour/ExtremalFamilyData.lean']=text
    dictionary={'face_order':['+x','-x','+y','-y','+z','-z'],
        'symmetry':'Common colour permutation and simultaneous reflection; proper rotations identify varieties.',
        'anchor':{'catalogue_index':0,'faces':faces[0],'singleton_pairs':[[1,2],[3,4]]},
        'B':{str(r):{'catalogue_index':i,'faces':faces[i],'cut':[0,1]} for r,i in zip([2,3,4],bs)},
        'C':{str(r):{'catalogue_index':i,'faces':faces[i],'cut':[1,2,4]} for r,i in zip([1,2,4],cs)},
        'classes':[{'class':j+1,'repeated_colours':rs,'multiplicities':[4,5,5],'labelled_orbit_size':size}
            for j,(rs,size) in enumerate(zip([(2,1),(2,4),(3,1),(3,2),(4,2)],[240,120,120,240,120]))]}
    output['data/five-colour-extremal.json']=json.dumps(dictionary,indent=2)+'\n'
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
    for name,data in render().items():
        path=ROOT/name
        if a.check:
            if path.read_text()!=data:raise SystemExit(f'{name} differs from regeneration')
        else:path.write_text(data)
    print('Checked 5,402 normalised candidates: 5,346 placements and 56 orbit witnesses.')
if __name__=='__main__':main()
