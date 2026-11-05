#!/usr/bin/env python3
"""Replay the archived certificates and run rejection and positive controls.

This validates a separate C++ certificate checker. Lean replay and the
physical-to-Hall bridge are checked by their own reproduction commands.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import check_five_colour
import check_five_colour_distinct
import check_five_colour_root_projection

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'
REPORT=ROOT/'build/checks'
REPORT.mkdir(parents=True,exist_ok=True)
CHECK=ROOT/'build/check_five_colour_certificate'
GEOMETRY=OUT/'five-colour-geometry.txt'
CASES=OUT/'q5-projected-root-cases.txt'
ARCHIVE=OUT/'q5-projected-certificates.tar.gz'


def replay(cases,prefix,output,workers):
    return subprocess.run([str(CHECK),str(GEOMETRY),str(cases),str(prefix),str(output),str(workers)],
                          stdout=subprocess.DEVNULL,check=False).returncode


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--workers',type=int,default=2)
    a=p.parse_args()
    if a.workers < 1: p.error('--workers must be positive')
    geometry=check_five_colour.main()
    check_five_colour_distinct.main(geometry)
    check_five_colour_root_projection.audit(a.workers,geometry)
    original=(OUT/'q5-cases-size15.txt').read_text().splitlines()[1:]
    expected=[r for r in original if int(r.split()[1])>=2]
    expected+=(OUT/'q5-distinct-shared-cases-size15.txt').read_text().splitlines()[1:]
    actual=(OUT/'q5-threshold-cases-size15.txt').read_text().splitlines()
    assert int(actual[0])==357 and actual[1:]==expected
    with tempfile.TemporaryDirectory(prefix='q5-replay-') as tmp:
        tmp=Path(tmp)
        # Malformed geometry must fail before any uninitialised value is used.
        tokens=GEOMETRY.read_text().split()
        malformed=['', 'not-a-number', '74', '75\n0',
                   ' '.join(tokens[:451]),
                   ' '.join(tokens[:1]+['5']+tokens[2:]),
                   ' '.join(tokens[:451]+['256']+tokens[452:])]
        for contents in malformed:
            badgeometry=tmp/'geometry.txt'
            badgeometry.write_text(contents)
            status=subprocess.run([str(CHECK),str(badgeometry),str(CASES),
                str(tmp/'unused-'),str(tmp/'geometry-result.json'),'1'],
                stdout=subprocess.DEVNULL).returncode
            if status!=1 or (tmp/'geometry-result.json').exists():
                raise RuntimeError('malformed geometry reached certificate processing')
        with tarfile.open(ARCHIVE) as tar:
            members=tar.getmembers()
            assert {m.name for m in members}=={f'case-{i}.q5p' for i in range(279)}
            assert len(members)==279 and all(m.isfile() for m in members)
            tar.extractall(tmp,filter='data')
        rows=CASES.read_text().splitlines()[1:]
        # Three malformed versions of a real two-command proof: truncate it,
        # append junk, or replace its final target reason with a false mass claim.
        control_id=next(i for i in range(279) if len((tmp/f'case-{i}.q5p').read_bytes())==164
                        and (tmp/f'case-{i}.q5p').read_bytes()[-2]==0
                        and (tmp/f'case-{i}.q5p').read_bytes()[-1]!=0)
        original=(tmp/f'case-{control_id}.q5p').read_bytes()
        variants=[original[:-1],original+b'\x00',original[:-1]+b'\x00']
        # A known unsolvable eleven-set satisfies this root case. No direct
        # mass, budget or target refutation of the entire root can be valid.
        control=list(map(int,(OUT/'q5-distinct-known-control.txt').read_text().splitlines()[1].split()))
        for reason in range(77):variants.append(b'Q5P2'+bytes(control)+bytes([0,reason]))
        badrows=[rows[control_id]]*3+[' '.join(map(str,control))]*77
        badcases=tmp/'rejection-cases.txt'
        badcases.write_text('80\n'+'\n'.join(badrows)+'\n')
        for i,data in enumerate(variants):(tmp/f'reject-{i}.q5p').write_bytes(data)
        rejection_status=replay(badcases,tmp/'reject-',tmp/'rejections.json',a.workers)
        if rejection_status!=1:
            raise RuntimeError(f'unexpected checker exit status for rejection controls: {rejection_status}')
        rejected=json.loads((tmp/'rejections.json').read_text())
        if len(rejected)!=80 or {r['case'] for r in rejected}!=set(range(80)) or any(r['accepted'] for r in rejected):
            raise RuntimeError('checker failed to reject every negative control')
    summary=dict(certificates_accepted=279,rejection_controls=80,geometry_rejection_controls=len(malformed),
                 archive_sha256=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
                 proof_status='C++ audit; the full command separately checks the Lean proof')
    (REPORT/'q5-certificate-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
