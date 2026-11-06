#!/usr/bin/env python3
"""Generate finite classification witnesses; every numerical assertion is checked by Lean."""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
from cube_geometry import ROT, canonical
from generate_five_colour_chunks import packed
ROOT=Path(__file__).resolve().parents[1]

def vec(xs):return '!['+','.join(map(str,xs))+']'
def arr(xs):return '#['+','.join(map(str,xs))+']'
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
 def write(name,text):
  path=ROOT/'FiveColour'/name
  if args.check:
   if not path.is_file() or path.read_text()!=text:raise SystemExit(f'Generated file differs: {path}')
  else:path.write_text(text)
 info=json.loads((ROOT/'data/five-colour-classification.json').read_text())
 lines=(ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
 cubes=[tuple(map(int,s.split())) for s in lines[1:76]];idx={canonical(c):i for i,c in enumerate(cubes)}
 perms=list(itertools.permutations(range(5)));syms=[(p,b) for p in perms for b in [False,True]]
 actions=[];rotations=[]
 for p,b in syms:
  act=[];rs=[]
  for c in cubes:
   d=tuple(p[x] for x in c);d=(d[1],d[0],*d[2:]) if b else d
   j=idx[canonical(d)];act.append(j);rs.append(next(k for k,r in enumerate(ROT) if d==tuple(cubes[j][f] for f in r)))
  actions.append(act);rotations.append(rs)
 reps=[r['varieties'] for r in info['representatives']];terminals=info['terminals']
 witnesses=[]
 for v in terminals:
  found=next((j,g) for j,w in enumerate(reps) for g,act in enumerate(actions) if sorted(act[i] for i in v)==sorted(w))
  witnesses.append(found)
 def code(v):return sum(16**i for i in v)
 prefix='module\npublic import FiveColour.Inventory\npublic import FiveColour.PackedSemantics\n@[expose] public section\nnamespace FiveColour.Physical.Classification\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 text=prefix
 text+='def representativeVariety : Fin 56 → Fin 14 → Fin 75 := '+vec(vec(v) for v in reps)+'\n'
 text+='def terminalVariety : Fin 81 → Fin 14 → Fin 75 := '+vec(vec(v) for v in terminals)+'\n'
 text+='def terminalPacked : Fin 81 → Nat := '+vec(packed([Counter(v)[i] for i in range(75)]) for v in terminals)+'\n'
 text+='def terminalClass : Fin 81 → Fin 56 := '+vec(j for j,g in witnesses)+'\n'
 text+='def terminalSymmetry : Fin 81 → Fin 240 := '+vec(g for j,g in witnesses)+'\n'
 text+='def hallDeficit : Fin 56 → Fin 75 → Nat := '+vec(vec(r['hall_masks']) for r in info['representatives'])+'\n'
 text+='def representativeCode : Fin 56 → Nat := '+vec(code(v) for v in reps)+'\n'
 text+='def orbitCodes : Array (Array Nat) := '+arr(arr(code([a[i] for i in v]) for a in actions) for v in reps)+'\n'
 text+='def orbitCode (j : Fin 56) (g : Fin 240) : Nat := (orbitCodes[j.val]!)[g.val]!\n'
 text+='def rootIndex : Fin 349 → Fin 357 := '+vec(r['original_root'] for r in info['roots'])+'\n'
 text+='def rootTerminals : Fin 349 → List (Fin 81) := '+vec('['+','.join(map(str,r['terminals']))+']' for r in info['roots'])+'\n'
 text+='end FiveColour.Physical.Classification\n';write('ClassificationData.lean',text)
 text=prefix.replace('public import FiveColour.PackedSemantics','public import Mathlib.Tactic.FinCases')
 for name,data,ty in [('colourData',[p for p,b in syms],'Fin 5'),('inverseData',[[p.index(i) for i in range(5)] for p,b in syms],'Fin 5'),('actionData',actions,'Fin 75'),('rotationData',rotations,'Fin 24')]:
  text+=f'def {name} : Array (Array ({ty})) := '+arr(arr(v) for v in data)+'\n'
 text+='def colour (g : Fin 240) (a : Fin 5) : Fin 5 := (colourData[g.val]!)[a.val]!\n'
 text+='def inverseColour (g : Fin 240) (a : Fin 5) : Fin 5 := (inverseData[g.val]!)[a.val]!\n'
 text+='def action (g : Fin 240) (i : Fin 75) : Fin 75 := (actionData[g.val]!)[i.val]!\n'
 text+='def rotation (g : Fin 240) (i : Fin 75) : Fin 24 := (rotationData[g.val]!)[i.val]!\n'
 text+='def mirror (g : Fin 240) : Bool := g.val % 2 == 1\n'
 text+='''lemma inverse_check : ∀ (g : Fin 240) (a : Fin 5),
    inverseColour g (colour g a) = a ∧ colour g (inverseColour g a) = a := by decide +kernel

def symmetry (g : Fin 240) : PuzzleSymmetry where
  colour := {
    toFun := colour g
    invFun := inverseColour g
    left_inv a := (inverse_check g a).1
    right_inv a := (inverse_check g a).2 }
  mirror := mirror g

lemma faces (g : Fin 240) : ∀ (i : Fin 75) (f : Fin 6),
    (symmetry g).apply (catalogue i) f =
      catalogue (action g i) (ColourCubes.rotations (rotation g i) f) := by
  fin_cases g <;> decide +kernel

lemma action_eq (g : Fin 240) (i : Fin 75) : varietyEquiv (symmetry g) i = action g i := by
  change catalogueIndex ((symmetry g).apply (catalogue i)) = action g i
  rw [funext (faces g i)]
  exact catalogue_index_rotations _ _

def permutationDigit (p : Fin 5 → Fin 5) (i : Fin 5) : ℕ :=
  (Finset.univ.filter fun j : Fin 5 => i < j ∧ p j < p i).card

def permutationRank (p : Fin 5 → Fin 5) : ℕ :=
  24 * permutationDigit p 0 + 6 * permutationDigit p 1 + 2 * permutationDigit p 2 + permutationDigit p 3

lemma permutationRank_lt (p : Fin 5 → Fin 5) : permutationRank p < 120 := by
  have h (i : Fin 5) : permutationDigit p i ≤ (Finset.univ.filter fun j : Fin 5 => i < j).card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have e0 : (Finset.univ.filter fun j : Fin 5 => (0 : Fin 5) < j).card = 4 := by decide
  have e1 : (Finset.univ.filter fun j : Fin 5 => (1 : Fin 5) < j).card = 3 := by decide
  have e2 : (Finset.univ.filter fun j : Fin 5 => (2 : Fin 5) < j).card = 2 := by decide
  have e3 : (Finset.univ.filter fun j : Fin 5 => (3 : Fin 5) < j).card = 1 := by decide
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  unfold permutationRank
  omega

def symmetryIndex (p : Fin 5 → Fin 5) (b : Bool) : Fin 240 :=
  ⟨2 * permutationRank p + (if b then 1 else 0), by have := permutationRank_lt p; split <;> omega⟩

lemma complete_check : ∀ (p : Fin 5 → Fin 5) (b : Bool), Function.Injective p →
    colour (symmetryIndex p b) = p ∧ mirror (symmetryIndex p b) = b := by decide +kernel

lemma complete (s : PuzzleSymmetry) : ∃ g, symmetry g = s := by
  obtain ⟨hc,hm⟩ := complete_check s.colour s.mirror s.colour.injective
  refine ⟨symmetryIndex s.colour s.mirror, ?_⟩
  have he : (symmetry (symmetryIndex s.colour s.mirror)).colour = s.colour := Equiv.ext (congrFun hc)
  have hb : (symmetry (symmetryIndex s.colour s.mirror)).mirror = s.mirror := hm
  cases s with
  | mk p b => cases hs : symmetry (symmetryIndex p b) with
    | mk q d =>
      rw [hs] at he hb
      exact congrArg₂ PuzzleSymmetry.mk he hb
end FiveColour.Physical.Classification
'''
 write('ClassificationSymmetries.lean',text)
 print('Generated 56 representatives, 81 terminal witnesses and all 240 global symmetries.')
if __name__=='__main__':main()
