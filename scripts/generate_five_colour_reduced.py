"""Serialize root-specific Hall weakenings and their kernel-checked witnesses.

Drop impossible alternatives, subtract fixed coordinates, and merge equal
residual neighbourhoods using the largest RHS, then discard alternatives
subsumed by a weaker retained alternative. None of this Python arithmetic
is trusted: PackedPruning checks coverage and calibrates every replacement.
"""
import re
from collections import Counter
from generate_five_colour_packed import cut


def undominated(merged):
    """Keep weaker cuts and a covering witness for every input neighbourhood.

    Cuts form a disjunction. With nonnegative multiplicities, a subset of
    coordinates and a greater RHS gives a weaker inequality. Every removed
    cut therefore still implies its retained witness. Lean checks this again
    for each concrete root; this function is only a serializer.
    """
    sets = {key: frozenset(key) for key in merged}
    keys = [key for key in merged if not any(
        other != key and sets[other] <= sets[key] and merged[other] >= merged[key]
        for other in merged)]
    witness = {key: next(other for other in keys
        if sets[other] <= sets[key] and merged[other] >= merged[key]) for key in merged}
    return keys, witness


def reduction(row, checkpoints, geometry):
    goal, anchor = row[3:5]
    lower, upper = [0] * 75, list(row[6:81])
    lower[anchor] = upper[anchor] = row[1]
    frequencies = Counter(int(x) - 3 for x in re.findall(r'\.(?:step|close) (\d+)', checkpoints)
                          if int(x) >= 3)
    used = set(frequencies)
    if not used <= set(range(75)):
        raise ValueError('invalid target family')
    text, counts, viable_counts = '', [], []
    for target in sorted(used):
        alternatives, merged = [], {}
        for subset in range(1, 256):
            members = [i for i, mask in enumerate(geometry[target]) if mask & subset]
            rhs = subset.bit_count() - 1
            if (sum(lower[i] for i in members) <= rhs and
                    goal <= rhs + sum(upper) - sum(upper[i] for i in members)):
                free = tuple(i for i in members if lower[i] != upper[i])
                residual = rhs - sum(lower[i] for i in members if lower[i] == upper[i])
                merged[free] = max(merged.get(free, -1), residual)
                alternatives.append(free)
            else:
                alternatives.append(None)
        keys, witness = undominated(merged)
        indices = {key: i for i, key in enumerate(keys)}
        counts.append(len(keys))
        viable_counts.append(sum(x is not None for x in alternatives))
        text += f'\ndef reduced{target} : Array Cut := #['
        text += ','.join(cut(key, merged[key]) for key in keys) + ']\n'
        text += f'def witnesses{target} : List Nat := ['
        text += ','.join(str(indices[witness[x]]) if x is not None else '0' for x in alternatives) + ']\n'
        text += f'''theorem valid{target} : ∀ c ∈ reduced{target}.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered{target} : ∀ c ∈ families {target+3}, possible root {goal} c →
    ∃ d ∈ reduced{target}.toList, relaxes root c d = true :=
  covers_sound root {goal} reduced{target} (families {target+3}) witnesses{target} (by decide +kernel)
'''
    text += '\ndef checkedFamilies (r : Fin 78) : List Cut :=\n  match r.val with\n'
    text += ''.join(f'  | {target+3} => reduced{target}.toList\n' for target in sorted(used))
    text += '  | _ => families r\n'
    text += '''
theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by
  intro r
  fin_cases r
'''
    text += ''.join(f'  · exact valid{i-3}\n' if i-3 in used else
                    f'  · exact families_valid {i}\n' for i in range(78))
    text += f'''
theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root {goal} c →
    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by
  intro r
  fin_cases r
'''
    text += ''.join(f'  · exact covered{i-3}\n' if i-3 in used else
                    '  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩\n' for i in range(78))
    return text, {'used_target_families': len(used), 'original_cuts': 255 * len(used),
                  'viable_cuts': sum(viable_counts), 'reduced_cuts': sum(counts),
                  'target_scans_before': 255 * sum(frequencies.values()),
                  'target_scans_after': sum(frequencies[t] * n for t, n in zip(sorted(used), counts))}
