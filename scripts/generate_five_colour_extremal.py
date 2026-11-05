#!/usr/bin/env python3
"""Generate explicit corner allocations for the local multiplicity proof.

No interval certificates or fifteen-cube theorem are used. The four disjoint
cut classes and at most three singleton-intersection varieties compress the
six-anchor case to populated weak compositions with at most three disjoint
sources. Four disjoint sources use the separate lemma first.
Every emitted allocation, inventory coverage and group mask is kernel checked.
"""
import argparse
from pathlib import Path
from cube_geometry import corners
from cube_witnesses import match_copies

ROOT=Path(__file__).resolve().parents[1]

def compositions(g,n):
    if not g:
        if not n: yield ()
    else:
        for a in range(n+1):
            for tail in compositions(g-1,n-a): yield (a,)+tail

def allocation(masks,cap):
    for t,row in enumerate(masks):
        copies=[g for g,n in enumerate(cap) for _ in range(n)]
        matched=match_copies(row,copies)
        if matched is not None:
            return t,[copies[i] for i in matched]
    raise ValueError(('No local allocation',cap))

def render():
    lines=(ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
    faces=[tuple(map(int,x.split())) for x in lines[1:76]]
    fits=[list(map(int,x.split())) for x in lines[76:]]
    tri=[tuple(sorted(c for c in corners(f) if len(set(c))==3)) for f in faces]
    dis=[i for i in range(75) if fits[3][i]==0]
    cuts=sorted(set(tri[i] for i in dis))
    assert len(cuts)==4
    ds=[[i for i in dis if tri[i]==cut] for cut in cuts]
    groups=[];masks=[]
    for k in range(8):
        singles=[i for i in range(75) if fits[3][i]==1<<k]
        assert len(singles)<=3
        gs=[[3]]+ds+[[i] for i in singles]+[[] for _ in range(3-len(singles))]
        groups.append(gs)
        table=[]
        for t in range(75):
            row=[]
            for group in gs:
                v=255
                for i in group:v &= fits[t][i]
                row.append(v)
            table.append(row)
        masks.append(table)
    vec=lambda xs:'!['+','.join(map(str,xs))+']'
    pre='module\npublic import FiveColour.ExtremalMatching\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace FiveColour.Physical\n'
    text=pre+'\n/-- Anchor, four disjoint cut classes, and up to three singleton varieties. -/\ndef sixGroup : Fin 8 → Fin 75 → Option (Fin 8) :=\n'+vec(vec('some '+str(next(g for g,xs in enumerate(gs) if i in xs)) if any(i in xs for xs in gs) else 'none' for i in range(75)) for gs in groups)+'\n'
    text+='\ndef sixMasks : Fin 8 → Fin 75 → Fin 8 → ℕ :=\n'+vec(vec(vec(row) for row in table) for table in masks)+'\n'
    text+='''
def singletonCount : Fin 8 → ℕ := ![0,0,2,2,2,2,3,3]

def populatedCounts (k : Fin 8) (v : Fin 7 → ℕ) : Prop :=
  ∀ g, 4 + singletonCount k ≤ g.val → v g = 0
instance (k : Fin 8) (v : Fin 7 → ℕ) : Decidable (populatedCounts k v) := by
  unfold populatedCounts; infer_instance

def disjointCount (v : Fin 7 → ℕ) : ℕ := v 0 + v 1 + v 2 + v 3

def sixCompositionDomain (k : Fin 8) : List (Fin 7 → ℕ) :=
  (sourceCompositions 7 8).filter fun v => populatedCounts k v ∧ disjointCount v ≤ 3

def disjointCompositionDomain : List (Fin 7 → ℕ) :=
  (sourceCompositions 7 4).filter fun v => populatedCounts 0 v

structure LocalInventory where
  counts : Fin 7 → ℕ
  placement : CornerAllocation

def LocalInventory.Valid (k : Fin 8) (anchor : ℕ) (w : LocalInventory) : Prop :=
  w.placement.Valid (sixMasks k) (Fin.cons anchor w.counts)
instance instDecidableLocalInventoryValid (k : Fin 8) (a : ℕ) (w : LocalInventory) : Decidable (w.Valid k a) := by
  unfold LocalInventory.Valid
  infer_instance

end FiveColour.Physical
'''
    output={'FiveColour/ExtremalLocalData.lean':text}
    for k in range(8):
        pre=f'module\npublic import FiveColour.ExtremalLocalData\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace FiveColour.Physical\n'
        rows=[]
        for counts in compositions(7,8):
            if sum(counts[:4]) > 3 or any(counts[4+len([g for g in groups[k][5:] if g]):]): continue
            t,tags=allocation(masks[k],(6,)+counts)
            rows.append(f'⟨{vec(counts)},⟨{t},{vec(tags)}⟩⟩')
        assert len(rows)==[0,0,231,231,231,231,889,889][k]
        text=pre+f'\ndef sixInventories{k} : List LocalInventory := [\n'+',\n'.join(rows)+']\n'
        text+=f'''\ntheorem six_inventories_cover_{k} :
    sixInventories{k}.map LocalInventory.counts = sixCompositionDomain {k} := by decide +kernel

theorem six_inventories_valid_{k} :
    ∀ w ∈ sixInventories{k}, w.Valid {k} 6 := by decide +kernel

theorem six_masks_valid_{k} : ∀ (t i : Fin 75) (g : Fin 8),
    sixGroup {k} i = some g → ∀ q : Fin 8, (sixMasks {k} t g).testBit q.val = true →
        (Replay.fits t i).testBit q.val = true := by decide +kernel

end FiveColour.Physical
'''
        output[f'FiveColour/ExtremalSixChecks{k}.lean']=text
    rows=[]
    for counts in compositions(7,4):
        if any(counts[4:]): continue
        t,tags=allocation(masks[0],(4,)+counts)
        rows.append(f'⟨{vec(counts)},⟨{t},{vec(tags)}⟩⟩')
    assert len(rows)==35
    text=pre+'\ndef disjointInventories : List LocalInventory := [\n'+',\n'.join(rows)+']\n'
    text+='''
theorem disjoint_inventories_cover :
    disjointInventories.map LocalInventory.counts = disjointCompositionDomain := by decide +kernel

theorem disjoint_inventories_valid :
    ∀ w ∈ disjointInventories, w.Valid 0 4 := by decide +kernel
end FiveColour.Physical
'''
    output['FiveColour/ExtremalDisjointChecks.lean']=text
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
    for name,data in render().items():
        path=ROOT/name
        if a.check:
            if path.read_text()!=data:raise SystemExit(f'{name} differs from regeneration')
        else:path.write_text(data)
    print('Local multiplicity allocations regenerated and checked.' if a.check else 'Generated local multiplicity allocations.')
if __name__=='__main__':main()
