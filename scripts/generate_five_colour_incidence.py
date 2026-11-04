#!/usr/bin/env python3
"""Regenerate the physical incidence input; Lean proves its correctness."""
import argparse
from pathlib import Path
import tempfile
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'


def generate(destination):
    rows=[list(map(int,r.split())) for r in (OUT/'five-colour-geometry.txt').read_text().splitlines()[76:]]
    dst=destination
    matrix=',\n  '.join('#['+','.join(map(str,r))+']' for r in rows)
    (dst/'Incidence.lean').write_text('''module
public import FiveColour.BoxCertificates
@[expose] public section
namespace FiveColour.Replay
open Certificate
/-- Search incidence data; physical correctness is proved in PhysicalIncidence.lean. -/
def incidence : Array (Array Nat) := #[
  '''+matrix+''']
def fits (t i : Fin 75) : Nat := (incidence[t.val]!)[i.val]!
def hallCuts (t : Fin 75) : List (Cut 75) :=
  (List.range 255).map fun d =>
    { neighbours := Finset.univ.filter (fun i => (fits t i).land (d+1) ≠ 0)
      rhs := (((List.range 8).filter (fun k => (d+1).testBit k)).length : Int) - 1 }
end FiveColour.Replay
''')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='q5-incidence-') as temp:
            generate(Path(temp))
            if (Path(temp)/'Incidence.lean').read_bytes() != (ROOT/'FiveColour/Incidence.lean').read_bytes():
                raise SystemExit('Incidence.lean differs from regeneration')
        print('Incidence source matches regeneration.')
    else:
        generate(ROOT/'FiveColour')


if __name__=='__main__':main()
