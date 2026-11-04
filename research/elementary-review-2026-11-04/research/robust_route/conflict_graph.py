"""Exact reduction of repeated-colour refinements to list multicolouring.

Fix the 20 adjacent tricolour-class multiplicities and 15 opposite counts.
The graph records incompatible pairs of classes sharing a repeated colour.
It is used only after ruling out opposite-repeat target assemblies.
"""
import sys
from pathlib import Path
from itertools import combinations
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import *

TRI_SOURCES = CUTS + tuple(CORNERS[60:])
TRI_MASKS = tuple(tuple(sum(1<<k for k,e in enumerate(sorted(c)) if e in src)
                        for src in TRI_SOURCES) for c in CUTS)

def tri_match(counts,t):
    masks=[m for i,m in enumerate(TRI_MASKS[t]) for _ in range(counts[i]) if m]
    owners=[-1]*len(masks)
    def aug(k,seen):
        for i,m in enumerate(masks):
            if i in seen or not (m>>k&1):continue
            seen.add(i)
            if owners[i]<0 or aug(owners[i],seen):owners[i]=k;return True
        return False
    order=sorted(range(6),key=lambda k:sum(bool(m>>k&1)for m in masks))
    return all(aug(k,set()) for k in order)

def conflict_graph(gs,os=None):
    if os is None:os=[0]*15
    counts=list(gs)+list(os)
    active=[j for j,g in enumerate(gs)if g]
    edges=[];loops=[];witness={}
    for j in active:
        for k in active:
            if k<j or (j==k and gs[j]<2):continue
            pj=set(CLASSES[j][0]);pk=set(CLASSES[k][0])
            candidates=[t for t,(p,sg) in enumerate(CLASSES)
                        if ((p[0]in pj and p[1]in pk)or(p[1]in pj and p[0]in pk))]
            counts[j]-=1;counts[k]-=1
            t=next((t for t in candidates if tri_match(counts,t)),None)
            counts[j]+=1;counts[k]+=1
            if t is not None:
                witness[j,k]=t
                if j==k:loops.append(j)
                else:edges.append((j,k))
    return {'active':active,'edges':edges,'loops':loops,'witnesses':witness}

def refinement_respects_graph(x,G):
    repeats={j:{r for i,(a,r)in enumerate(ADJ)if a==j and x[i]}
             for j in G['active']}
    return (all(x[i]<=1 for j in G['loops'] for i in range(3*j,3*j+3))
            and all(not (repeats[j]&repeats[k]) for j,k in G['edges']))

def clique_obstruction(gs,G):
    """Return a demand clique needing >5 colours after pole exclusions."""
    active=G['active'];loops=set(G['loops']);edges=set(G['edges'])
    for size in range(1,len(active)+1):
        for clique in combinations(active,size):
            if any(tuple(sorted((j,k)))not in edges for j,k in combinations(clique,2)):continue
            poles=set(V)
            for j in clique:poles&=set(CLASSES[j][0])
            weight=sum(gs[j]if j in loops else 1 for j in clique)
            if weight+len(poles)>5:return {'clique':clique,'weight':weight,'common_poles':sorted(poles)}
    return None

def find_failure_refinement(gs,os=None):
    if os is None:os=[0]*15
    representative=[v for g in gs for v in [g,0,0]]+list(os)
    if solution(representative,range(60,75)) is not None:return None,None,0
    G=conflict_graph(gs,os);loops=set(G['loops'])
    neigh={j:set()for j in G['active']}
    for j,k in G['edges']:neigh[j].add(k);neigh[k].add(j)
    options={}
    for j in G['active']:
        demand=gs[j]if j in loops else 1
        choices=[r for r in V if r not in CLASSES[j][0]]
        options[j]=[sum(1<<r for r in rs)for rs in combinations(choices,demand)]
    nodes=0
    def rec(options,assigned):
        nonlocal nodes
        nodes+=1
        if not options:return assigned
        j=min(options,key=lambda j:(len(options[j]),-len(neigh[j])))
        for c in options[j]:
            remaining={k:([d for d in ds if not c&d]if k in neigh[j]else ds)
                       for k,ds in options.items()if k!=j}
            if any(not ds for ds in remaining.values()):continue
            out=rec(remaining,{**assigned,j:c})
            if out is not None:return out
        return None
    assigned=rec(options,{})
    if assigned is None:return None,G,nodes
    x=[0]*60+list(os)
    for j,cs in assigned.items():
        rs=[r for r in V if cs>>r&1]
        for r in rs:
            i=ADJ.index((j,r));x[i]=1 if j in loops else gs[j]
    assert solution(x) is None
    return x,G,nodes

if __name__=='__main__':
    gs=[0]*20
    for j,g in [(0,3),(9,1),(10,3),(15,2),(17,2),(19,3)]:gs[j]=g
    x,G,nodes=find_failure_refinement(gs)
    print('refinement',x,'nodes',nodes)
    print('loops',G['loops'],'edges',G['edges'])
    print('edge target witnesses',G['witnesses'])
