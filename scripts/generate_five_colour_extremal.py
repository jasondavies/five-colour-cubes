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
from cube_witnesses import allocation

ROOT=Path(__file__).resolve().parents[1]

def compositions(g,n):
    if not g:
        if not n: yield ()
    else:
        for a in range(n+1):
            for tail in compositions(g-1,n-a): yield (a,)+tail

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
    text=pre+'\ndef disjointGroup : Fin 75 → Option (Fin 4) :=\n'+vec('some '+str(next(g for g,xs in enumerate(ds) if i in xs)) if i in dis else 'none' for i in range(75))+'\n'
    text+='\ndef singletonVariety : Fin 8 → Fin 3 → Option (Fin 75) :=\n'+vec(vec('some '+str(xs[0]) if xs else 'none' for xs in gs[5:]) for gs in groups)+'\n'
    text+='\ndef disjointMasks : Fin 75 → Fin 4 → ℕ :=\n'+vec(vec(row[1:5]) for row in masks[0])+'\n'
    text+="""
/-- The anchor and four disjoint pools are shared by all eight corner cases. -/
def sixGroup (k : Fin 8) (i : Fin 75) : Option (Fin 8) :=
  if i = 3 then some 0 else
  match disjointGroup i with
  | some g => some ⟨g.val+1, by omega⟩
  | none => if singletonVariety k 0 = some i then some 5 else
      if singletonVariety k 1 = some i then some 6 else
      if singletonVariety k 2 = some i then some 7 else none

def sixMasks (k : Fin 8) (t : Fin 75) : Fin 8 → ℕ :=
  ![Replay.fits t 3, disjointMasks t 0, disjointMasks t 1,
    disjointMasks t 2, disjointMasks t 3,
    (singletonVariety k 0).elim 255 (Replay.fits t),
    (singletonVariety k 1).elim 255 (Replay.fits t),
    (singletonVariety k 2).elim 255 (Replay.fits t)]
"""
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
