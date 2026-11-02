#!/usr/bin/env python3
"""Generate actual Hall-certificate replay examples (not the full physical theorem)."""
import argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cases',type=int,nargs='+',default=[79,165,207])
    a=p.parse_args()
    rows=[list(map(int,r.split())) for r in (OUT/'five-colour-geometry.txt').read_text().splitlines()[76:]]
    dst=ROOT/'FiveColour'
    matrix=',\n  '.join('#['+','.join(map(str,r))+']' for r in rows)
    (dst/'Incidence.lean').write_text('''module
public import FiveColour.BoxCertificates
@[expose] public section
namespace FiveColour.Replay
open Certificate
/-- Search incidence data; the physical bridge is not yet formalised here. -/
def incidence : Array (Array Nat) := #[
  '''+matrix+''']
def fits (t i : Fin 75) : Nat := (incidence[t.val]!)[i.val]!
def hallCuts (t : Fin 75) : List (Cut 75) :=
  (List.range 255).map fun d =>
    { neighbours := Finset.univ.filter (fun i => (fits t i).land (d+1) ≠ 0)
      rhs := (((List.range 8).filter (fun k => (d+1).testBit k)).length : Int) - 1 }
end FiveColour.Replay
''')
    for case in a.cases:
        data=(OUT/f'q5-certificates/case-{case}.q5p').read_bytes()
        assert data[:4]==b'Q5P2'
        kind,m,cover,goal,anchor,budget=data[4:10]
        caps=list(data[10:85]);bad=list(data[85:160]);lo=[0]*75
        lo[anchor]=caps[anchor]=m
        pos=160
        def read():
            nonlocal pos
            op=data[pos];pos+=1
            if op==0:
                reason=data[pos];pos+=1
                return '.mass' if reason==0 else f'(.close {reason+1})'
            if op==1:
                i,v=data[pos:pos+2];pos+=2
                left=read();right=read()
                return f'(.split {i} {v} {left} {right})'
            assert op==2
            reason=data[pos];pos+=1
            rest=read()
            if reason==0:return f'(.step 1 (.step 0 {rest}))'
            return f'(.step {reason+1} {rest})'
        proof=read();assert pos==len(data)
        vec=lambda v:'!['+','.join(map(str,v))+']'
        text=f'''module
public import FiveColour.Incidence
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Replay.Case{case}
open Certificate
open scoped BigOperators
def root : Box 75 := {{ lower := {vec(lo)}, upper := {vec(caps)} }}
def bad : Finset (Fin 75) := {{{','.join(str(i) for i,b in enumerate(bad) if b)}}}
def problem : Problem 75 78 where
  goal := {goal}
  alternatives r :=
    if r.val = 0 then [{{ neighbours := ∅, rhs := 0 }}]
    else if r.val = 1 then [{{ neighbours := Finset.univ, rhs := {goal} }}]
    else if r.val = 2 then [{{ neighbours := bad, rhs := {budget} }}]
    else hallCuts ⟨r.val - 3, by omega⟩
def proof : Proof 75 78 := {proof}
theorem accepted : check problem root proof = true := by decide +kernel
theorem excludes : ∀ x, root.Contains x → ¬ problem.Admissible x :=
  check_sound problem proof root accepted
end FiveColour.Replay.Case{case}
'''
        (dst/f'Case{case}.lean').write_text(text)
    print('Generated replay examples:',a.cases)


if __name__=='__main__':main()
