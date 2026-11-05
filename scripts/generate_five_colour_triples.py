#!/usr/bin/env python3
"""Sixty residual witnesses after own-target and disjoint-pair reductions.

Every positive record names a target whose coverage and private-position
bounds certify a matching of distinct physical copies. Every negative record gives a global symmetry of one of five examples.
The Lean checker verifies both possibilities, rather than trusting enumeration.
"""
import argparse,json
from pathlib import Path
from cube_witnesses import allocation, match_copies, ordered_anchor_symmetries
ROOT=Path(__file__).resolve().parents[1]

def render():
    lines=(ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
    faces=[tuple(map(int,x.split())) for x in lines[1:76]]
    fits=[list(map(int,x.split())) for x in lines[76:]]
    bs=[faces.index(f) for f in [(0,1,2,3,2,4),(0,1,2,3,3,4),(0,1,2,4,3,4)]]
    cs=[faces.index(f) for f in [(0,3,1,2,4,1),(0,3,1,2,4,2),(0,3,1,4,4,2)]]
    representative_specs=[(2,1,240),(2,4,120),(3,1,120),(3,2,240),(4,2,120)]
    b_by_repeat=dict(zip([2,3,4],bs));c_by_repeat=dict(zip([1,2,4],cs))
    reps=[(b_by_repeat[r],c_by_repeat[s]) for r,s,_ in representative_specs]
    _,actions,_=ordered_anchor_symmetries(faces,(3,0))
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
        return match_copies(fits[t],[a]*4+[b]*5+[c]*5)
    vec=lambda xs:'!['+','.join(map(str,xs))+']'
    pre='module\npublic import FiveColour.ExtremalVarieties\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace FiveColour.Physical\n'
    varieties=pre.replace('FiveColour.ExtremalVarieties','FiveColour.ExtremalTriples')
    varieties+='\ndef extremalB : Fin 5 → Fin 75 := '+vec(b for b,c in reps)+'\ndef extremalC : Fin 5 → Fin 75 := '+vec(c for b,c in reps)
    varieties+='\ndef extremalBGroup : Fin 3 → Fin 75 := '+vec(bs)+'\ndef extremalCGroup : Fin 3 → Fin 75 := '+vec(cs)+'\nend FiveColour.Physical\n'
    text=pre+'\n'+'''
def tripleAnchor : Fin 2 → Fin 75 := ![0,3]

inductive TripleReduction where
  | solve (target : Fin 75)
  | orbit (representative : Fin 5) (symmetry : Fin 16) (swap : Bool)
  deriving Inhabited, DecidableEq

def TripleReduction.Valid (a b c : Fin 75) : TripleReduction → Prop
  | .solve t => TripleCriterion a b c t
  | .orbit j g swap => a = 0 ∧
      b = stabiliserAction g (if swap then extremalC j else extremalB j) ∧
      c = stabiliserAction g (if swap then extremalB j else extremalC j)
instance instDecidableTripleReductionValid (a b c : Fin 75) (w : TripleReduction) : Decidable (w.Valid a b c) := by
  cases w <;> unfold TripleReduction.Valid <;> infer_instance
'''
    def criterion(a,b,c,t):
        x,y,z=(fits[t][i] for i in (a,b,c))
        return ((x|y|z)==255 and (x & ~(y|z)).bit_count()<=4 and
                (y & ~(x|z)).bit_count()<=5 and (z & ~(x|y)).bit_count()<=5)
    records=[];counts=[]
    for kind,a in enumerate([0,3]):
        own=disjoint=residual=0
        for b in range(75):
            for c in range(b+1,75):
                if a in (b,c):continue
                if any(criterion(a,b,c,t) for t in (a,b,c)):
                    own+=1;continue
                if any(fits[i][j]==0 for i,j in [(a,b),(a,c),(b,c)]):
                    disjoint+=1;continue
                residual+=1
                if a==0 and (b,c) in orbit:
                    j,g,swap=orbit[b,c];w=f'.orbit {j} {g} {str(swap).lower()}'
                else:
                    assert (a,b,c) in [(0,20,55),(0,21,68),(0,37,45),(0,40,60)]
                    assert criterion(a,b,c,1) and match(a,b,c,1) is not None
                    w='.solve 1'
                records.append(f'⟨{kind},{b},{c},{w}⟩')
        counts.append((own,disjoint,residual))
    assert counts==[(2641,0,60),(2502,199,0)],counts
    text += """
/-- The own-target and disjoint-pair arguments leave this finite remainder. -/
def TripleResidual (kind : Fin 2) (b c : Fin 75) : Prop :=
  tripleAnchor kind ≠ b ∧ tripleAnchor kind ≠ c ∧ b < c ∧
  ¬ TripleCriterion (tripleAnchor kind) b c (tripleAnchor kind) ∧
  ¬ TripleCriterion (tripleAnchor kind) b c b ∧
  ¬ TripleCriterion (tripleAnchor kind) b c c ∧
  Replay.fits (tripleAnchor kind) b ≠ 0 ∧
  Replay.fits (tripleAnchor kind) c ≠ 0 ∧ Replay.fits b c ≠ 0
instance (kind : Fin 2) (b c : Fin 75) : Decidable (TripleResidual kind b c) := by
  unfold TripleResidual; infer_instance

structure TripleResidualRecord where
  kind : Fin 2
  b : Fin 75
  c : Fin 75
  reduction : TripleReduction
  deriving DecidableEq
"""
    text+='\ndef tripleResiduals : List TripleResidualRecord := [\n'+',\n'.join(records)+']\n'
    text+="""
lemma triple_residuals_valid : ∀ w ∈ tripleResiduals,
    w.reduction.Valid (tripleAnchor w.kind) w.b w.c := by decide +kernel

end FiveColour.Physical
"""
    text=text.replace('public import FiveColour.ExtremalVarieties',
                      'public import FiveColour.ExtremalVarieties\npublic import FiveColour.StabiliserData')
    output={'FiveColour/ExtremalTripleData.lean':text, 'FiveColour/ExtremalVarieties.lean':varieties}
    for kind in range(2):
        for block in range(3):
            text=pre.replace('FiveColour.ExtremalVarieties','FiveColour.ExtremalTripleData')
            for b in range(block*25,(block+1)*25):
                text+=f"""\nlemma triple_residual_cover_{kind}_{b} : ∀ c : Fin 75,
    TripleResidual {kind} {b} c → ∃ w ∈ tripleResiduals,
      w.kind = {kind} ∧ w.b = {b} ∧ w.c = c := by decide +kernel
"""
            output[f'FiveColour/ExtremalTripleChecks{kind}{block}.lean']=text+'\nend FiveColour.Physical\n'
    text='module\n'+''.join(f'public import FiveColour.ExtremalTripleChecks{k}{g}\n' for k in range(2) for g in range(3))+"""@[expose] public section
namespace FiveColour.Physical

theorem triple_residuals_cover (kind : Fin 2) (b c : Fin 75)
    (h : TripleResidual kind b c) :
    ∃ w ∈ tripleResiduals, w.kind = kind ∧ w.b = b ∧ w.c = c := by
  fin_cases kind <;> fin_cases b
"""+''.join(f'  · exact triple_residual_cover_{k}_{b} c h\n' for k in range(2) for b in range(75))+'end FiveColour.Physical\n'
    output['FiveColour/ExtremalTripleChecks.lean']=text
    patterns=[([0,1,2],[0]),([0,1],[0,2]),([1,2],[0,1]),([1],[0,1,2])]
    cuts=[]
    for left,right in patterns:
        row=[]
        for t in range(75):
            bm=0;cm=0
            for i in left:bm |= fits[t][bs[i]]
            for i in right:cm |= fits[t][cs[i]]
            row.append(next(d for d in range(1,256) if sum(n for m,n in [(fits[t][0],4),(bm,5),(cm,5)] if m&d)<d.bit_count()))
        cuts.append(vec(row))
    text=pre.replace('FiveColour.ExtremalVarieties','FiveColour.ExtremalFamily')
    text+='\ndef uniformDeficit : Fin 4 → Fin 75 → ℕ :=\n'+vec(cuts)+'\n'
    text+='''
lemma uniform_deficits (p : Fin 4) : ∀ t : Fin 75,
    uniformDeficit p t < 256 ∧
    (uniformNeighbours p t (uniformDeficit p t)).card < (cornerSet (uniformDeficit p t)).card := by
  fin_cases p <;> decide +kernel
end FiveColour.Physical
'''
    placements=[]
    for bi,ci in [(0,1),(2,2)]:
        masks=[[fits[t][0],fits[t][bs[bi]],fits[t][bs[0]] & fits[t][bs[1]] & fits[t][bs[2]],fits[t][cs[ci]],0,0,0,0] for t in range(75)]
        t,tags=allocation(masks,(4,1,4,1,0,0,0,0))
        placements.append(f'⟨{t},{vec(tags)}⟩')
    fragment='\ndef familyCompletion : Fin 2 → CornerAllocation := '+vec(placements)+'''
lemma family_completion_capacity : ∀ (r : Fin 2) (g : Fin 8),
    (Finset.univ.filter fun k => (familyCompletion r).group k = g).card ≤ completionCapacity g := by
  decide +kernel

lemma family_completion_fits : ∀ (r : Fin 2) (k : Fin 8) (s : Fin 75),
    completionAllowed r ((familyCompletion r).group k) s →
      (Replay.fits (familyCompletion r).target s).testBit k.val = true := by
  decide +kernel
'''
    text=text.replace('end FiveColour.Physical', fragment+'\nend FiveColour.Physical')
    output['FiveColour/ExtremalFamilyData.lean']=text
    dictionary={'face_order':['+x','-x','+y','-y','+z','-z'],
        'symmetry':'Common colour permutation and simultaneous reflection; proper rotations identify varieties.',
        'anchor':{'catalogue_index':0,'faces':faces[0],'singleton_pairs':[[1,2],[3,4]]},
        'B':{str(r):{'catalogue_index':i,'faces':faces[i],'cut':[0,1]} for r,i in zip([2,3,4],bs)},
        'C':{str(r):{'catalogue_index':i,'faces':faces[i],'cut':[1,2,4]} for r,i in zip([1,2,4],cs)},
        'classes':[{'class':j+1,'repeated_colours':[r,s],'multiplicities':[4,5,5],'labelled_orbit_size':size}
            for j,(r,s,size) in enumerate(representative_specs)]}
    output['data/five-colour-extremal.json']=json.dumps(dictionary,indent=2)+'\n'
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
    for name,data in render().items():
        path=ROOT/name
        if a.check:
            if path.read_text()!=data:raise SystemExit(f'{name} differs from regeneration')
        else:path.write_text(data)
    print('Checked 5,402 candidates: 5,143 own targets, 199 disjoint pairs, 4 residual targets and 56 orbit witnesses.')
if __name__=='__main__':main()
