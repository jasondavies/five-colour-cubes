"""Reconnaissance for pairwise-intersecting adjacent-cut families.

Checks one opposite source plus thirteen capped adjacent sources in
each of the three proposed maximal family representatives. Not a proof.
"""
import json,sys
from pathlib import Path
from collections import Counter
from itertools import combinations_with_replacement
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS

FAMILIES=((0,2,5,7,8,19),(0,2,4,6,9,11,13),(0,2,4,6,9,11,15))
sources=CUTS+tuple(CORNERS[60:])
masks=[]
for target in CORNERS[60:]:
    corners=sorted(target)
    masks.append([sum(1<<k for k,c in enumerate(corners) if c in src) for src in sources])
def solves(g,o):
    os=(o,) if isinstance(o,int) else o
    copies=[j for j,n in enumerate(g)for _ in range(n)]+[20+x for x in os]
    for row in masks:
        ms=[row[j] for j in copies]
        union=0
        for m in ms:union|=m
        if union!=255:continue
        owner=[-1]*len(ms)
        def aug(k,seen):
            for i,m in enumerate(ms):
                if i in seen or not(m>>k&1):continue
                seen.add(i)
                if owner[i]<0 or aug(owner[i],seen):
                    owner[i]=k;return True
            return False
        if all(aug(k,set())for k in range(8)):return True
    return False
def counts(n,total):
    if n==0:
        if total==0:yield ()
        return
    for x in range(max(0,total-3*(n-1)),min(3,total)+1):
        for rest in counts(n-1,total-x):yield (x,)+rest
def main():
    two=len(sys.argv)>1 and sys.argv[1]=='two'
    label='twoopp' if two else 'oneopp'
    out=Path(__file__).with_name('pairwise-13adj-'+label+'-fails.jsonl').open('w')
    for fi,fam in enumerate(FAMILIES):
        stats=Counter();profiles=Counter();tested=0
        for vals in counts(len(fam),13):
            g=[0]*20
            for j,x in zip(fam,vals):g[j]=x
            for o in (combinations_with_replacement(range(15),2) if two else range(15)):
                tested+=1
                if solves(g,o):continue
                key=tuple(60+x for x in o) if two else 60+o
                stats[key]+=1;profiles[tuple(sorted((x for x in vals if x),reverse=True))]+=1
                out.write(json.dumps({'family':fi,'opposite':key,'adjacent':g})+'\n')
        print('family',fi,'tested',tested,'fail_by_O',dict(stats),'profiles',dict(profiles),flush=True)
    out.close()
if __name__=='__main__':main()
