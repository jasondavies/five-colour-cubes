#!/usr/bin/env python3
"""Generate kernel-checked packed Hall data and selected Q5P2 replay modules.

This is a serializer, not a trusted proof checker. Generated numerical claims
are checked by Lean; PackedVerified.check_sound supplies their meaning.
"""
import argparse
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'data'
DEST = ROOT / 'FiveColour'
BASE = 1024
WEIGHTS = [BASE ** (74 - i) for i in range(75)]
HEADER = '''module
public import FiveColour.PackedCore
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
'''


def cut(indices, rhs):
    return f'⟨{sum(1 << i for i in indices)}, {sum(WEIGHTS[i] for i in indices)}, {rhs}⟩'


def write_data(rows):
    text = HEADER
    for target, row in enumerate(rows):
        cuts = [cut([i for i, mask in enumerate(row) if mask & d], d.bit_count() - 1)
                for d in range(1, 256)]
        text += f'def cutRow{target} : Array Cut := #[' + ','.join(cuts) + ']\n'
    text += 'def cuts : Array (Array Cut) := #[' + ','.join(f'cutRow{i}' for i in range(75)) + ']\n'
    (DEST / 'PackedData.lean').write_text(text + 'end FiveColour.Packed\n')
    for group in range(8):
        text = HEADER.replace('FiveColour.PackedCore', 'FiveColour.PackedData\npublic import FiveColour.PackedSemantics')
        for i in range(group * 10, min(group * 10 + 10, 75)):
            text += f'theorem cutRow{i}_weights : cutRow{i}.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel\n'
        (DEST / f'PackedCalibration{group}.lean').write_text(text + 'end FiveColour.Packed\n')
    text = 'module\n' + ''.join(f'public import FiveColour.PackedCalibration{i}\n' for i in range(8))
    text += '''@[expose] public section
namespace FiveColour.Packed
set_option maxRecDepth 100000

theorem cuts_weights : cuts.toList.all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true := by
'''
    text += '  change [' + ','.join(f'cutRow{i}' for i in range(75)) + '].all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true\n'
    text += '  simp only [List.all_cons, List.all_nil, Bool.and_self, ' + ','.join(f'cutRow{i}_weights' for i in range(75)) + ']\n'
    text += '''
theorem cuts_valid (r : Fin 75) : ∀ c ∈ (cuts[r.val]!).toList, c.Valid := by
  apply list_valid_of_weights
  apply List.all_eq_true.mp cuts_weights
  have hsize : cuts.size = 75 := by decide +kernel
  have hr : r.val < cuts.size := by omega
  simpa only [getElem!_pos cuts r.val hr] using Array.getElem_mem_toList hr
end FiveColour.Packed
'''
    (DEST / 'PackedCalibration.lean').write_text(text)


def read_proof(raw):
    """Translate the prefix stream without Python recursion or quadratic strings."""
    position, pending, commands = 160, [1], 0
    pieces = []
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            pieces.append(item)
            continue
        if position >= len(raw):
            raise ValueError('truncated proof')
        op = raw[position]
        position += 1
        commands += 1
        if op == 0:
            r = raw[position]
            position += 1
            if r > 76:
                raise ValueError('invalid reason')
            pieces.append('.mass' if r == 0 else f'(.close {r + 1})')
        elif op == 1:
            i, v = raw[position:position + 2]
            position += 2
            if i >= 75 or v >= 7:
                raise ValueError('invalid split')
            pieces.append(f'(.split {i} {v} ')
            pending.extend([')', 1, ' ', 1])
        elif op == 2:
            r = raw[position]
            position += 1
            if r > 76:
                raise ValueError('invalid reason')
            pieces.append('(.step 1 (.step 0 ' if r == 0 else f'(.step {r + 1} ')
            pending.extend(['))' if r == 0 else ')', 1])
        else:
            raise ValueError(f'invalid opcode {op}')
    if position != len(raw):
        raise ValueError('trailing proof bytes')
    return ''.join(pieces), commands


def write_case(case, row, raw):
    if len(row) != 156 or raw[:160] != b'Q5P2' + bytes(row):
        raise ValueError(f'case {case}: header mismatch')
    _, multiplicity, _, goal, anchor, budget, *rest = row
    lower, upper = [0] * 75, rest[:75]
    lower[anchor] = upper[anchor] = multiplicity
    encode = lambda counts: sum(v * BASE ** i for i, v in enumerate(counts))
    proof, count = read_proof(raw)
    text = f'''module
public import FiveColour.PackedCalibration
public import FiveColour.PackedVerified
@[expose] public section
namespace FiveColour.Packed.Replay{case}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def root : Box := ⟨{encode(lower)},{encode(upper)}⟩
def families (r : Fin 78) : List Cut :=
  if r.val=0 then [{cut([], 0)}]
  else if r.val=1 then [{cut(list(range(75)), goal)}]
  else if r.val=2 then [{cut([i for i, b in enumerate(rest[75:]) if b], budget)}]
  else (cuts[r.val-3]!).toList
-- Generated from the archived Q5P2 certificate; checked by the Lean kernel.
def proof : Certificate.Proof 75 78 := {proof}
theorem accepted : Verified.check {goal} families root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

theorem excludes : ∀ x, root.model.Contains x → ¬ (Verified.problem {goal} families).Admissible x :=
  Verified.check_sound {goal} families families_valid proof root root_valid accepted
end FiveColour.Packed.Replay{case}
'''
    (DEST / f'PackedCase{case}.lean').write_text(text)
    print(f'case {case}: {count} certificate commands')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', type=int, nargs='+', default=[79, 165, 207, 78, 326])
    args = parser.parse_args()
    rows = [list(map(int, line.split())) for line in
            (RESULTS / 'five-colour-geometry.txt').read_text().splitlines()[76:]]
    if len(rows) != 75 or any(len(row) != 75 for row in rows):
        raise ValueError('expected 75 by 75 incidence table')
    cases = [list(map(int, line.split())) for line in
             (RESULTS / 'q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    if any(case < 0 or case >= len(cases) for case in args.cases):
        parser.error('case index out of range')
    write_data(rows)
    # Read only the named members; no filesystem extraction is needed.
    with tarfile.open(RESULTS / 'q5-certificates.tar.gz', 'r:gz') as archive:
        members = {Path(member.name).name: member for member in archive.getmembers() if member.isfile()}
        for case in args.cases:
            with archive.extractfile(members[f'case-{case}.q5p']) as stream:
                write_case(case, cases[case], stream.read())


if __name__ == '__main__':
    main()
