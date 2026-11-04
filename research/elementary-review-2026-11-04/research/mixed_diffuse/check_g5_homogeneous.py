from check_double_covers import *

def main():
    out=[]
    for opp in [60,71]:
        h=CORNERS[opp]&CUTS[0]
        js=[j for j in range(20)if j!=0 and CUTS[j]&CUTS[0]<=h]
        tested=0;O_fail=[]
        os=[0]*15;os[opp-60]=2
        for gg in allocations(7,[5]*len(js)):
            gs=[0]*20;gs[0]=5
            for j,n in zip(js,gg):gs[j]=n
            if any(gs[j]+gs[k]>7 for j in range(20)for k in range(j)if len(CUTS[j]&CUTS[k])==4):continue
            if any(sum(gs[j]for j in range(20)if CLASSES[j][0]==pair)+sum(n for n,(r,p,q)in zip(os,OPP)if pair==p or pair==q)>7 for pair in PAIRS):continue
            tested+=1
            xx=[v for g in gs for v in [g,0,0]]+os
            if solution(xx,range(60,75))is not None:continue
            G=conflict_graph(gs,os);cl=clique_obstruction(gs,G)
            O_fail.append({'counts':gg,'loops':G['loops'],'edges':G['edges'],'clique':cl})
        result={'opp':opp,'classes':js,'H':sorted(h),'tested':tested,'O_failing':O_fail}
        out.append(result)
        print('opp',opp,'js',js,'tested',tested,'O_fail',len(O_fail),flush=True)
        for row in O_fail:print(row,flush=True)
    Path(__file__).with_name('g5-homogeneous-O2.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
