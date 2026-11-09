#!/usr/bin/env python3
"""Independent replay for retained core-and-extension certificates.

Q5C1: 156-byte Q5P2 header, Q5P2 rules plus (3,0) for listed singleton.
Q5L1: original 156-byte header, 75-byte core lower bound, Q5P2 rules.
Lift upper bounds are ORIGINAL root bounds, so additions may be anywhere.
No search or enumeration heuristic is trusted. No Lean check is claimed.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import tempfile
from classification_core_inputs import load_core_inputs
import tarfile
import time

N = 75
ALL = (1 << N) - 1
EXPECTED_ROOTS = frozenset({58,59,60,61,62,63,64,65,66,68,69,71,325})

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def validate_entries(entries):
    require(len(entries) == len(EXPECTED_ROOTS), 'incomplete or extra root bundle')
    seen = []
    for path,metadata in entries:
        root = metadata.get('original_root')
        require(type(root) is int and root in EXPECTED_ROOTS, 'unexpected root identity')
        require(path.parent.name == f'r{root}', 'directory/root identity mismatch')
        seen.append(root)
    require(len(set(seen)) == len(seen), 'duplicate root identity')
    require(set(seen) == EXPECTED_ROOTS, 'incorrect complete root set')

def read_geometry(path, physical):
    raw = list(map(int, path.read_text().split()))
    require(len(raw) == 1 + 6*N + N*N and raw[0] == N, 'geometry dimensions')
    faces = [tuple(raw[1+6*i:1+6*(i+1)]) for i in range(N)]
    fits = [raw[1+6*N+N*t:1+6*N+N*(t+1)] for t in range(N)]
    if physical:
        rotations = {tuple(range(6))}
        pending = list(rotations)
        while pending:
            p = pending.pop()
            for q in ((0,1,5,4,2,3), (3,2,0,1,4,5)):
                r = tuple(p[i] for i in q)
                if r not in rotations:
                    rotations.add(r)
                    pending.append(r)
        require(len(rotations) == 24, 'proper rotations')
        def canonical(f):
            return min(tuple(f[i] for i in r) for r in rotations)
        expected = sorted({canonical(f) for f in itertools.product(range(5), repeat=6)
                           if len(set(f)) == 5})
        require(expected == faces, 'physical catalogue mismatch')
        slots = [(i,2+j,4+k) for i,j,k in itertools.product(range(2),repeat=3)]
        physical_fits = [[sum(1 << k for k,slot in enumerate(slots)
                             if any(all(source[r[a]] == target[a] for a in slot)
                                    for r in rotations))
                          for source in faces] for target in faces]
        require(physical_fits == fits, 'physical incidence mismatch')
    return [[(sum(1 << i for i,m in enumerate(row) if m & d), d.bit_count()-1)
             for d in range(1,256)] for row in fits]

class Checker:
    def __init__(self, data, row, hall, lower=None, points=None, lower_boxes=None):
        self.data, self.row, self.hall = data, row, hall
        self.goal, self.budget = row[3], row[5]
        self.bad = sum(v << i for i,v in enumerate(row[81:]))
        require(points is None or lower_boxes is None, 'ambiguous cover kind')
        self.cover_kind = 'point' if points is not None else 'lower' if lower_boxes is not None else None
        magic = b'Q5C1' if points is not None else b'Q5B1' if lower_boxes is not None else b'Q5L1'
        require(data[:4] == magic and data[4:160] == bytes(row), 'header mismatch')
        self.position = 160
        upper = list(row[6:81])
        require(upper[row[4]] == 0 and not row[81+row[4]], 'anchor convention')
        upper[row[4]] = row[1]
        if self.cover_kind is None:
            require(data[160:235] == bytes(lower), 'lift lower mismatch')
            self.position = 235
        else:
            lower = [0]*N
            lower[row[4]] = row[1]
        self.lower, self.upper = list(lower), upper
        require(all(0 <= l <= h <= 7 for l,h in zip(lower,upper)), 'invalid initial box')
        self.allowed = points if points is not None else lower_boxes
        self.observed = set()
        self.ops = Counter()
        self.mass_refinements = 0

    def byte(self):
        require(self.position < len(self.data), 'truncated certificate')
        value = self.data[self.position]
        self.position += 1
        return value

    @staticmethod
    def layers(vector):
        return tuple(sum(1 << i for i,v in enumerate(vector) if v > k)
                     for k in range(max(vector, default=0)))

    def refine(self, lo, hi, reason):
        low, high = sum(lo), sum(hi)
        if reason == 0:
            if low > self.goal or high < self.goal:
                return None
            new_lo = [max(l,self.goal-high+h) for l,h in zip(lo,hi)]
            new_hi = [min(h,self.goal-low+l) for l,h in zip(lo,hi)]
            # Existing Lean families: empty-cut lower step, full-cut upper step.
            sequential_hi = [min(h,self.goal-sum(new_lo)+l) for l,h in zip(new_lo,hi)]
            require(sequential_hi == new_hi, 'mass-step expansion changes bounds')
            return new_lo,new_hi
        require(1 <= reason <= 76, 'invalid reason')
        families = [(self.bad,self.budget)] if reason == 1 else self.hall[reason-2]
        ll, hh = self.layers(lo), self.layers(hi)
        common, united, slack, gap = ALL, 0, -1, -1
        for mask, rhs in families:
            il = sum((mask & z).bit_count() for z in ll)
            ih = sum((mask & z).bit_count() for z in hh)
            outside = high-ih
            if il > rhs or outside+rhs < self.goal:
                continue
            common &= mask
            united |= mask
            slack = max(slack,rhs-il)
            gap = max(gap,rhs+outside-self.goal)
        if slack < 0:
            return None
        return ([max(l,h-gap) if not (united >> i & 1) else l
                 for i,(l,h) in enumerate(zip(lo,hi))],
                [min(h,l+slack) if common >> i & 1 else h
                 for i,(l,h) in enumerate(zip(lo,hi))])

    def run(self):
        pending = [(self.lower,self.upper)]
        while pending:
            lo,hi = pending.pop()
            while True:
                op,a = self.byte(),self.byte()
                self.ops[op] += 1
                if op == 0:
                    require(self.refine(lo,hi,a) is None, 'invalid exclusion')
                    break
                if op == 3:
                    require(a == 0 and self.cover_kind == 'point' and lo == hi
                            and tuple(lo) in self.allowed, 'unlisted or nonsingleton point')
                    self.observed.add(tuple(lo))
                    break
                if op == 4:
                    require(a == 0 and self.cover_kind == 'lower' and tuple(lo) in self.allowed,
                            'unlisted lower-bound box')
                    self.observed.add(tuple(lo))
                    break
                if op == 1:
                    pivot = self.byte()
                    require(0 <= a < N and lo[a] <= pivot < hi[a], 'invalid split')
                    right_lo = lo.copy()
                    right_lo[a] = pivot+1
                    pending.append((right_lo,hi.copy()))
                    hi = hi.copy()
                    hi[a] = pivot
                    continue
                require(op == 2, 'invalid opcode')
                self.mass_refinements += (a == 0)
                result = self.refine(lo,hi,a)
                require(result is not None and result != (lo,hi), 'invalid/nonchanging refinement')
                nl,nh = result
                require(all(l <= a <= b <= h for l,a,b,h in zip(lo,nl,nh,hi)),
                        'refinement breaks box ordering')
                lo,hi = nl,nh
        require(self.position == len(self.data), 'trailing certificate bytes')
        if self.allowed is not None:
            require(self.observed == self.allowed, 'missing declared core')
        return dict(instructions=sum(self.ops.values()),
                    mass_refinements=self.mass_refinements,
                    lean_compatible_instructions=sum(self.ops.values())+self.mass_refinements,
                    refinements=self.ops[2], splits=self.ops[1],
                    exclusions=self.ops[0], points=self.ops[3], lower_boxes=self.ops[4],
                    bytes=len(self.data), sha256=sha(self.data))

def raw_instruction_count(data):
    require(data[:4] in (b'Q5E1',b'Q5P2'), 'old archive format')
    p,total = 160,0
    while p < len(data):
        op = data[p]
        require(op in (0,1,2,3), 'old archive opcode')
        p += 3 if op == 1 else 2
        total += 1
    require(p == len(data), 'old archive alignment')
    return total

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--results',type=Path)
    parser.add_argument('--physical',action='store_true')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'build/classification-cores-audit.json')
    args = parser.parse_args()
    temp = tempfile.TemporaryDirectory(prefix='q5-core-audit-')
    if args.results is None:
        _, args.results = load_core_inputs(args.repo, Path(temp.name))
    started = time.monotonic()
    datadir = args.repo/'data'
    hall = read_geometry(datadir/'five-colour-geometry.txt',args.physical)
    rows = [list(map(int,l.split())) for l in
            (datadir/'q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    classification = json.loads((datadir/'five-colour-classification.json').read_text())
    projections = json.loads((datadir/'five-colour-classification-projections.json').read_text())
    replacements = {e['original_root']:e for e in projections['cases']}
    old = tarfile.open(datadir/'five-colour-classification-certificates.tar.gz')
    results = []
    entries = [(p,json.loads(p.read_text())) for p in args.results.glob('r*/search.json')]
    validate_entries(entries)
    for path,metadata in sorted(entries,key=lambda item:item[1]['original_root']):
        root = metadata['original_root']
        require(metadata['complete'] and metadata['core_cover_complete'], 'incomplete search')
        original = rows[root].copy()
        original[3] = 14
        projected = original.copy()
        projected[3] = 14-original[5]
        projected[5] = 0
        for i in range(N):
            if projected[81+i]:
                projected[6+i] = 0
        require(projected[3] >= original[1], 'projection loses anchor')
        require(metadata['original_total'] == 14 and metadata['projected_total'] == projected[3],
                'metadata totals mismatch')
        cores = [tuple(v) for v in metadata['cores']]
        require(len(cores) == len(set(cores)) and cores, 'invalid core list')
        expected_files = {'cover.q5c'} | {f'lift-{j}.q5l' for j in range(len(cores))}
        require({p.name for p in path.parent.glob('*.q5*')} == expected_files,
                'missing or extra certificate files')
        for core in cores:
            require(len(core) == N and sum(core) == projected[3]
                    and core[original[4]] == original[1], 'core total/anchor')
            for i,x in enumerate(core):
                require(0 <= x <= (original[1] if i == original[4] else projected[6+i]),
                        'core outside projection bounds')
            ll = Checker.layers(core)
            require(all(any(sum((z & mask).bit_count() for z in ll) <= rhs
                            for mask,rhs in family) for family in hall),
                    'listed core is actually solvable')
        cover = Checker((path.parent/'cover.q5c').read_bytes(),projected,hall,
                        points=set(cores)).run()
        lift_results = []
        for j,core in enumerate(cores):
            lift = Checker((path.parent/f'lift-{j}.q5l').read_bytes(),original,hall,
                           lower=core).run()
            lift_results.append(lift)
        index, entry = next((i,e) for i,e in enumerate(classification['roots'])
                            if e['original_root'] == root)
        legacy = old.extractfile(f'case-{index}.q5p').read()
        require(sha(legacy) == entry['certificate_sha256'], 'old archive hash mismatch')
        old_instructions = raw_instruction_count(legacy)
        current = replacements.get(root,{}).get('new_instructions',old_instructions)
        combined = cover['instructions']+sum(e['instructions'] for e in lift_results)
        expanded = cover['lean_compatible_instructions']+sum(e['lean_compatible_instructions']
                                                            for e in lift_results)
        result = dict(original_root=root,projected_total=projected[3],cores=len(cores),
                      baseline_instructions=current,original_instructions=old_instructions,
                      cover=cover,lifts=lift_results,combined_instructions=combined,
                      lean_compatible_instructions=expanded,
                      lift_instructions=sum(e['instructions'] for e in lift_results),
                      lift_splits=sum(e['splits'] for e in lift_results),
                      saved_instructions=current-expanded)
        results.append(result)
        print(f'root {root}: {len(cores)} cores; cover {cover["instructions"]:,}, '
              f'lifts {result["lift_instructions"]:,} ({result["lift_splits"]} splits); '
              f'total {expanded:,} Lean-compatible vs baseline {current:,}; saved {current-expanded:,}',flush=True)
    old.close()
    report = dict(format=1,method='independent Python interval replay; no Lean replay',
                  physical_geometry_checked=args.physical,
                  original_total=14,projection_retained_budget=0,
                  lift_upper_bounds='original root bounds; additions allowed in every coordinate',
                  elapsed_seconds=time.monotonic()-started,
                  geometry_sha256=sha((datadir/'five-colour-geometry.txt').read_bytes()),
                  cases_sha256=sha((datadir/'q5-threshold-cases-size15.txt').read_bytes()),
                  production_search_sha256=sha((args.repo/'src/five_colour_boxes.cpp').read_bytes()),
                  root_set=sorted(EXPECTED_ROOTS),
                  total_cores=sum(r['cores'] for r in results),
                  baseline_instructions=sum(r['baseline_instructions'] for r in results),
                  native_instructions=sum(r['combined_instructions'] for r in results),
                  lean_compatible_instructions=sum(r['lean_compatible_instructions'] for r in results),
                  total_lift_splits=sum(r['lift_splits'] for r in results),
                  cases=results)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(f'accepted {len(results)} roots; saved '
          f'{sum(r["saved_instructions"] for r in results):,} interval instructions; '
          f'{report["elapsed_seconds"]:.2f} seconds')

if __name__ == '__main__':
    main()
