#!/usr/bin/env python3
"""Audit the projected archive against original roots and physical geometry.

No search generator is imported. Recomputes every row, checks the preserved
anchor and the projection's size condition, and replays all proof objects.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
from physical_geometry import match, require

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT/'data'


def audit(workers, geometry):
    require(workers>0,'Worker count')
    manifest=json.loads((DATA/'q5-projected-root-manifest.json').read_text())
    def read_rows(name):
        lines=(DATA/name).read_text().splitlines()
        rows=[list(map(int,l.split())) for l in lines[1:]]
        require(len(rows)==int(lines[0]) and all(len(r)==156 for r in rows),'Malformed rows')
        return rows
    original=read_rows('q5-threshold-cases-size15.txt')
    projected=read_rows('q5-projected-root-cases.txt')
    expected=json.loads((DATA/'q5-root-reduction.json').read_text())['replay_case_ids']
    require([r['original_case'] for r in manifest['cases']]==expected,'Root coverage')
    require(len(projected)==len(expected)==279,'Root count')
    for case,meta in enumerate(manifest['cases']):
        old,new=original[meta['original_case']],projected[case]
        kind,m,cover,G,anchor,budget=old[:6]
        s=new[5]
        require(meta['case']==case and G==15 and 0<=s<=budget,'Budget range')
        require(new[:3]==old[:3] and new[4]==anchor and new[81:]==old[81:],'Fixed fields')
        require(new[3]==15-budget+s and new[3]>=m,'Goal and protected anchor')
        require(old[81+anchor]==0 and new[6+anchor]==old[6+anchor]==0,'Anchor outside budget')
        require(all(new[6+i]==(min(old[6+i],s) if old[81+i] else old[6+i])
                    for i in range(75)),'Projected upper bounds')
        require((meta['original_budget'],meta['retained_budget'],meta['goal'])==
                (budget,s,new[3]),'Metadata')
    for key,name in [('source_cases_sha256','q5-threshold-cases-size15.txt'),
                     ('projected_cases_sha256','q5-projected-root-cases.txt'),
                     ('projected_archive_sha256','q5-projected-certificates.tar.gz')]:
        require(hashlib.sha256((DATA/name).read_bytes()).hexdigest()==manifest[key],'Input hash')

    # Independently rebuild the physical incidence matrix used by the checker.
    cubes, incidence, masks = geometry
    witnesses=[]
    for attempt in manifest['zero_budget_counterexamples']:
        r=original[attempt['original_case']];s=attempt['retained_budget'];x=attempt['counts']
        require(len(x)==75 and all(n>=0 for n in x),'Witness length/nonnegativity')
        require(sum(x)==15-r[5]+s and x[r[4]]==r[1],'Witness total/anchor')
        require(sum(x[i] for i in range(75) if r[81+i])<=s,'Witness budget')
        require(all(x[i]<=r[6+i] for i in range(75) if i!=r[4]),'Witness bounds')
        require(not any(match(row,x) for row in incidence),'Claimed counterexample is solvable')
        witnesses.append(dict(original_case=attempt['original_case'],size=sum(x),counts=x))
    require({r['original_case'] for r in witnesses}=={68,69},'Unexpected exceptions')

    with tempfile.TemporaryDirectory(prefix='q5-projected-check-') as temp:
        temp=Path(temp)
        with tarfile.open(DATA/'q5-projected-certificates.tar.gz') as archive:
            members=archive.getmembers()
            require(len(members)==279 and {m.name for m in members}==
                    {f'case-{i}.q5p' for i in range(279)},'Archive members')
            for member in members:
                require(member.isfile(),'Non-file archive member')
                i=int(member.name[5:-4]);raw=archive.extractfile(member).read()
                require(raw[:160]==b'Q5P2'+bytes(projected[i]),'Certificate header')
                require(hashlib.sha256(raw).hexdigest()==manifest['cases'][i]['certificate_sha256'],
                        'Certificate hash')
                (temp/member.name).write_bytes(raw)
        output=temp/'replay.json'
        subprocess.run([str(ROOT/'build/check_five_colour_certificate'),str(DATA/'five-colour-geometry.txt'),
                        str(DATA/'q5-projected-root-cases.txt'),str(temp/'case-'),str(output),str(workers)],
                       check=True,stdout=subprocess.DEVNULL)
        records=json.loads(output.read_text())
        require(len(records)==279 and {r['case'] for r in records}==set(range(279))
                and all(r['accepted'] for r in records),'Incomplete replay')
        require(all(r['commands']==manifest['cases'][r['case']]['instructions'] for r in records),
                'Command count')
        require(sum(r['commands'] for r in records)==manifest['projected_instructions'],'Total count')
    result=dict(checked_roots=279,physical_bits=45000,certificates_accepted=279,
                instructions=manifest['projected_instructions'],exception_witnesses=witnesses,
                archive_sha256=manifest['projected_archive_sha256'],
                checker_source_sha256=hashlib.sha256((ROOT/'src/check_five_colour_certificate.cpp').read_bytes()).hexdigest(),
                audit_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                limitation='Finite data and separate C++ replay audit; does not assert completed Lean replay.')
    report=ROOT/'build/checks'
    report.mkdir(parents=True,exist_ok=True)
    (report/'q5-projected-root-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='exception_witnesses'},indent=2))


if __name__=='__main__':
    from check_five_colour import main as audit_geometry
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=2)
    args=parser.parse_args()
    audit(args.workers, audit_geometry())
