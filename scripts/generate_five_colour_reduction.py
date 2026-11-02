#!/usr/bin/env python3
"""Generate redundant-root witnesses and direct budget contradictions.

Python proposes only finite data. Lean checks all containments, arithmetic
closures, cardinalities and transport into the existing 357-root interface.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def generate(root, check=False):
    lines = (root / 'data/q5-threshold-cases-size15.txt').read_text().splitlines()
    rows = [list(map(int, line.split())) for line in lines[1:]]
    assert len(rows) == int(lines[0]) == 357
    assert all(len(r) == 156 and r[6+r[4]] == r[81+r[4]] == 0 for r in rows)

    def contains(parent, child):
        p, c = rows[parent], rows[child]
        return (p[:2] == c[:2] and p[3:5] == c[3:5] and p[5] >= c[5]
                and all(a <= b for a, b in zip(p[81:], c[81:]))
                and all(a >= b for a, b in zip(p[6:81], c[6:81])))

    def strict(parent, child):
        p, c = rows[parent], rows[child]
        return contains(parent, child) and (p[5] > c[5] or p[81:] != c[81:])

    retained = [i for i in range(357) if not any(strict(j, i) for j in range(357))]
    representative = [i if i in retained else next(j for j in retained if contains(j, i))
                      for i in range(357)]
    pairs = [(i, p) for i, p in enumerate(representative) if i != p]
    arithmetic = [i for i in retained if rows[i][1] + rows[i][5] + sum(
        c for c, b in zip(rows[i][6:81], rows[i][81:]) if not b) < rows[i][3]]
    replay = [i for i in retained if i not in arithmetic]
    assert (len(pairs), len(retained), len(arithmetic), len(replay)) == (49, 308, 29, 279)

    def emit(name, text):
        path = root / name
        if check:
            if not path.is_file() or path.read_text() != text:
                raise SystemExit(f'Generated file differs: {name}')
        else:
            path.write_text(text)

    emit('data/q5-root-reduction.json', json.dumps(dict(
        containing_retained_root=representative, retained_case_ids=retained,
        arithmetic_case_ids=arithmetic, replay_case_ids=replay), indent=2)+'\n')

    preamble = '''module
public import FiveColour.RootContainment
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

'''
    text = preamble + '''/-- Every nontrivial change is one of the 49 containment witnesses below.
Original case numbers and archive headers remain unchanged. -/
def rootRepresentative (r : Fin 357) : Fin 357 :=
'''
    text += ''.join(f'  if r = {i} then {p} else\n' for i, p in pairs) + '  r\n\n'
    text += '''def retainedRoots : Finset (Fin 357) :=
  Finset.univ.filter fun r => rootRepresentative r = r

/-- Retained roots whose budget and upper box already contradict total 15. -/
def arithmeticRoots : Finset (Fin 357) :=
  {''' + ', '.join(map(str, arithmetic)) + '''}

/-- Only these 279 roots require further exclusion proofs. -/
def replayRoots : Finset (Fin 357) := retainedRoots \\ arithmeticRoots

lemma representative_mem (r : Fin 357) : rootRepresentative r ∈ retainedRoots := by
  have h : ∀ s : Fin 357, rootRepresentative s ∈ retainedRoots := by decide +kernel
  exact h r

lemma retainedRoots_card : retainedRoots.card = 308 := by decide +kernel
lemma arithmeticRoots_card : arithmeticRoots.card = 29 := by decide +kernel
lemma arithmeticRoots_subset : arithmeticRoots ⊆ retainedRoots := by decide +kernel
lemma replayRoots_card : replayRoots.card = 279 := by decide +kernel

'''
    text += ''.join(f'lemma root_contains_{i} : RootContains {p} {i} := by decide +kernel\n'
                    for i, p in pairs)
    text += '''
/-- The full box and admissibility transport has a checked witness for every root. -/
theorem representative_contains (r : Fin 357) : RootContains (rootRepresentative r) r := by
  fin_cases r
'''
    text += ''.join(f'  · exact root_contains_{i}\n' if i != representative[i]
                    else f'  · exact RootContains.refl {i}\n' for i in range(357))
    text += '\n'
    text += ''.join(f'''lemma impossible_budget_{i} :
    ¬ (⟨rootBad (rootCapacity {i}), (rootCapacity {i}).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity {i})) 15 := by decide +kernel
''' for i in arithmetic)
    text += '''
/-- These 29 exclusions use only the initial budget capacity bound, not a certificate. -/
theorem arithmetic_root_excluded (r : Fin 357) (hr : r ∈ arithmeticRoots) :
    ∀ x, (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x := by
  simp only [arithmeticRoots, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with ''' + ' | '.join(['rfl'] * len(arithmetic)) + '\n'
    text += ''.join(f'  · exact root_excluded_of_impossible_budget {i} impossible_budget_{i}\n'
                    for i in arithmetic)
    text += '\nend FiveColour.Physical\n'
    emit('FiveColour/RootReductionChecks.lean', text)
    print('Root reduction: 49 containments, 308 retained, 29 arithmetic, 279 replay roots.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generate(ROOT, args.check)
