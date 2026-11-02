#!/usr/bin/env python3
"""A complete alternative cover split for distinct sets of size >= 11.

If an opposite-repeat variety is present, anchor there. Otherwise all cubes
are adjacent-repeat varieties. Each has two double-colour corners among just
20 possible types. At least 11 distinct cubes therefore give a shared double
corner. Anchor at one of its two cubes. The two characteristic corner slots
of that anchor cannot form a Hall-deficient set, because at least two cubes
are usable there. This deletes one cover without deleting any counterexample.

These cases have different caps from the older adjacent-priority split and
must NOT be merged into its case ledger by (kind, multiplicity, cover).
"""
import argparse
import hashlib
import json
from pathlib import Path
from case_geometry import geometry
from case_geometry import covers
from cube_geometry import corners


def generate(size):
    if size < 11:raise ValueError('Shared-corner argument requires size >= 11')
    data=geometry();cubes,opposite,anchors,_,_=data
    lines=[];counts={};excluded=[]
    for kind in (0,1):
        anchor=anchors[kind]
        characteristic=sum(1<<k for k,q in enumerate(corners(cubes[anchor])) if len(set(q))==2)
        assert characteristic.bit_count()==(2 if kind==0 else 0)
        counts[kind]=0
        for bad,budget,k in covers(data,kind,1):
            if kind==0 and k==(255^characteristic):
                assert budget==0
                excluded.append(dict(kind=kind,cover=k,characteristic=characteristic))
                continue
            upper=[int(kind==1 or not f) for f in opposite]
            for i in range(75):
                if bad>>i&1:upper[i]=min(upper[i],budget)
            upper[anchor]=0
            lines.append(' '.join(map(str,[kind,1,k,size,anchor,budget,*upper,
                                          *[int(bad>>i&1) for i in range(75)]])))
            counts[kind]+=1
    return lines,dict(partition='distinct-opposite-first-shared-corner',size=size,
                      case_count=len(lines),case_counts_by_kind=counts,excluded=excluded)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--size',type=int,default=15)
    p.add_argument('--output',required=True)
    p.add_argument('--metadata',help='Optional generated metadata output')
    a=p.parse_args();lines,metadata=generate(a.size)
    metadata['source_hashes']={n:hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest()
                              for n in ['five_colour_distinct_cases.py','case_geometry.py','cube_geometry.py']}
    Path(a.output).write_text(str(len(lines))+'\n'+'\n'.join(lines)+'\n')
    if a.metadata:Path(a.metadata).write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata),flush=True)


if __name__=='__main__':main()
