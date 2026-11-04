import sys,json,time,itertools
from pathlib import Path
from check_double_covers import *

def test(total_o,size):
    output=[]
    for row in cover_orbits(size):
        start=time.monotonic();js=row['classes'];ops=row['opps']
        outside=[j for j in range(35)if (j not in js if j<20 else j+40 not in ops) and j!=20]
        triples=[]
        for n in range(6-size):
            triples.extend(itertools.combinations_with_replacement(outside,n))
        counters={'tested':0,'oppfail':0,'loopkill':0,'cliquekill':0,'fullkill':0};survivors=[];noclique=[];examples=[]
        for ext in triples:
            outg=[0]*20;outo=[0]*15
            for j in ext:
                if j<20:outg[j]+=1
                else:outo[j-20]+=1
            if max(outo)>2 or sum(outo)>total_o-2:continue
            for oo in allocations(total_o-2-sum(outo),[2]*len(ops)):
                os=outo.copy();os[0]=2
                for t,n in zip(ops,oo):os[t-60]+=n
                missO=[sum(n for n,(r,p,q)in zip(os,OPP)if pair==p or pair==q)for pair in PAIRS]
                for gg in allocations(14-total_o-sum(outg),[5]*len(js)):
                    gs=outg.copy()
                    for j,n in zip(js,gg):gs[j]+=n
                    if any(gs[j]+gs[k]>7 for j in range(20) for k in range(j) if len(CUTS[j]&CUTS[k])==4):continue
                    if any(m+sum(gs[j]for j in range(20) if CLASSES[j][0]==pair)>7 for m,pair in zip(missO,PAIRS)):continue
                    counters['tested']+=1
                    xx=[v for g in gs for v in [g,0,0]]+os
                    if solution(xx,range(60,75))is not None:continue
                    counters['oppfail']+=1;G=conflict_graph(gs,os)
                    if any(gs[j]>3 for j in G['loops']):counters['loopkill']+=1;continue
                    clique=clique_obstruction(gs,G)
                    if clique:
                        counters['cliquekill']+=1
                        examples.append({'gs':gs,'os':os,'ext':ext,'clique':clique})
                        continue
                    x,G,nodes=find_failure_refinement(gs,os)
                    if x is None:counters['fullkill']+=1
                    else:survivors.append(x)
                    noclique.append({'gs':gs,'os':os,'ext':ext,'G':{k:v for k,v in G.items()if k!='witnesses'},'nodes':nodes})
        result={**row,'size':size,'O':total_o,**counters,'survivors':survivors,'noclique':noclique,'examples':examples,'seconds':time.monotonic()-start}
        output.append(result)
        print({k:v for k,v in result.items()if k not in ['survivors','noclique','examples']}|{'survivors':len(survivors)},flush=True)
    Path(__file__).with_name(f'double-cover-{size}-O{total_o}.json').write_text(json.dumps(output,indent=2))
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]))
