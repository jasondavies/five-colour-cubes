#!/usr/bin/env python3
"""Audit coverage and summarize the complete five-colour threshold computation.

The C++ search is trusted software, not a Lean proof or a proof certificate.
The checked build validates each matching assignment before pruning. The two
physical audits below regenerate geometry independently of the search model.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import check_five_colour
import check_five_colour_distinct
from physical_geometry import require

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data'
REPORT = ROOT / 'build/checks'
REPORT.mkdir(parents=True, exist_ok=True)


def read_cases(name):
    lines = (OUT / name).read_text().splitlines()
    rows = [tuple(map(int, line.split())) for line in lines[1:]]
    require(len(rows) == int(lines[0]), 'Wrong row count in ' + name)
    require(all(len(row) == 156 for row in rows), 'Wrong row length in ' + name)
    return rows


def main():
    check_five_colour.main()
    check_five_colour_distinct.main()
    old = read_cases('q5-cases-size15.txt')
    distinct = read_cases('q5-distinct-shared-cases-size15.txt')
    expected = [row for row in old if row[1] >= 2] + distinct
    actual = read_cases('q5-threshold-cases-size15.txt')
    require(actual == expected and len(actual) == 357, 'Wrong combined partition')
    result_file = OUT / 'q5-threshold-checked-size15.json'
    records = json.loads(result_file.read_text())
    require(len(records) == len(actual), 'Incomplete result file')
    require({r['case'] for r in records} == set(range(len(actual))), 'Missing case IDs')
    for r in records:
        row = actual[r['case']]
        require((r['kind'], r['m'], r['cover'], r['size_requested']) == row[:4],
                'Result and case disagree')
        require(r['status'] in ('EXHAUSTIVE_UNSAT', 'UNKNOWN', 'SAT'), 'Unknown status')
    statuses = dict(Counter(r['status'] for r in records))
    complete = statuses == {'EXHAUSTIVE_UNSAT': 357}
    files = ['src/five_colour_exact.cpp', 'src/five_colour_matching.hpp',
             'scripts/check_five_colour.py', 'scripts/check_five_colour_distinct.py',
             'scripts/physical_geometry.py',
             'scripts/check_five_colour_threshold.py',
             'data/five-colour-geometry.txt',
             'data/q5-threshold-cases-size15.txt',
             'data/q5-threshold-checked-size15.json',
             'data/q5-three-variety-obstruction.json']
    report = dict(model='five fixed colours, all used on each cube and on target; repeats allowed',
                  threshold=15 if complete else None, lower_bound=15,
                  upper_bound=15 if complete else None,
                  proof_type='computer-assisted exhaustive search; not Lean-certified',
                  case_count=len(actual), case_statuses=statuses,
                  repeated_variety_cases=sum(row[1] >= 2 for row in actual),
                  distinct_adjacent_cases=sum(row[:2] == (0, 1) for row in actual),
                  distinct_opposite_cases=sum(row[:2] == (1, 1) for row in actual),
                  total_prefix_nodes=sum(r['nodes'] for r in records),
                  sum_case_seconds=sum(r['seconds'] for r in records),
                  worst_case_seconds=max(r['seconds'] for r in records),
                  compiler_option='-DMACMAHON_VERIFY_MATCHES',
                  source_and_data_sha256={f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
                                          for f in files})
    (REPORT / 'q5-threshold-summary.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    require(complete, 'Some cases remain unresolved: no upper bound of 15 certified')


if __name__ == '__main__':
    main()
