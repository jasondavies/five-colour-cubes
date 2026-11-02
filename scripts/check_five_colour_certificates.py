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

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'
REPORT=ROOT/'build/checks'
REPORT.mkdir(parents=True,exist_ok=True)
CHECK=ROOT/'build/check_five_colour_certificate'
GEOMETRY=OUT/'five-colour-geometry.txt'
CASES=OUT/'q5-threshold-cases-size15.txt'
ARCHIVE=OUT/'q5-certificates.tar.gz'


def replay(cases,prefix,output,workers):
    return subprocess.run([str(CHECK),str(GEOMETRY),str(cases),str(prefix),str(output),str(workers)],
                          stdout=subprocess.DEVNULL,check=False).returncode


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--workers',type=int,default=8)
    a=p.parse_args()
    check_five_colour.main()
    check_five_colour_distinct.main()
    original=(OUT/'q5-cases-size15.txt').read_text().splitlines()[1:]
    expected=[r for r in original if int(r.split()[1])>=2]
    expected+=(OUT/'q5-distinct-shared-cases-size15.txt').read_text().splitlines()[1:]
    actual=CASES.read_text().splitlines()
    assert int(actual[0])==357 and actual[1:]==expected
    with tempfile.TemporaryDirectory(prefix='q5-replay-') as tmp:
        tmp=Path(tmp)
        with tarfile.open(ARCHIVE) as tar:
            members=tar.getmembers()
            assert {m.name for m in members}=={f'case-{i}.q5p' for i in range(357)}
            assert len(members)==357 and all(m.isfile() for m in members)
            tar.extractall(tmp,filter='data')
        assert replay(CASES,tmp/'case-',REPORT/'q5-certificate-replay.json',a.workers)==0
        rows=CASES.read_text().splitlines()[1:]
        # Three malformed versions of a real two-command proof: truncate it,
        # append junk, or replace its final target reason with a false mass claim.
        original=(tmp/'case-79.q5p').read_bytes()
        variants=[original[:-1],original+b'\x00',original[:-1]+b'\x00']
        # A known unsolvable eleven-set satisfies this root case. No direct
        # mass, budget or target refutation of the entire root can be valid.
        control=list(map(int,(OUT/'q5-distinct-known-control.txt').read_text().splitlines()[1].split()))
        for reason in range(77):variants.append(b'Q5P2'+bytes(control)+bytes([0,reason]))
        badrows=[rows[79]]*3+[' '.join(map(str,control))]*77
        badcases=tmp/'rejection-cases.txt'
        badcases.write_text('80\n'+'\n'.join(badrows)+'\n')
        for i,data in enumerate(variants):(tmp/f'reject-{i}.q5p').write_bytes(data)
        assert replay(badcases,tmp/'reject-',tmp/'rejections.json',a.workers)!=0
        rejected=json.loads((tmp/'rejections.json').read_text())
        assert len(rejected)==80 and all(not r['accepted'] for r in rejected)
    records=json.loads((REPORT/'q5-certificate-replay.json').read_text())
    assert len(records)==357 and all(r['accepted'] for r in records)
    assert {r['case'] for r in records}==set(range(357))
    sources=['src/five_colour_boxes.cpp','src/check_five_colour_certificate.cpp',
             'scripts/check_five_colour_certificates.py',
             'data/five-colour-geometry.txt',
             'data/q5-threshold-cases-size15.txt',
             'data/q5-certificates.tar.gz']
    summary=dict(certificates_accepted=357,rejection_controls=80,
                 certificate_bytes=sum(r['bytes'] for r in records),
                 compressed_bytes=ARCHIVE.stat().st_size,
                 commands=sum(r['commands'] for r in records),
                 leaves=sum(r['leaves'] for r in records),
                 proof_status='C++ certificate replay only; Lean verification is performed separately',
                 sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in sources})
    (REPORT/'q5-certificate-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
