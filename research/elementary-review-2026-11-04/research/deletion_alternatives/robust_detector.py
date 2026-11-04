from pathlib import Path
import sys,json
import numpy as np
ROOT=Path('/workspace/scratch/66c0ebb8d303/review/five-colour-cubes')
sys.path.insert(0,str(ROOT/'scripts'))
from cube_geometry import corners,canonical

lines=(ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
cubes=[tuple(map(int,row.split())) for row in lines[1:76]]
inc=np.array([list(map(int,row.split())) for row in lines[76:]],dtype=np.uint16)
tri=[];bi=[];opp=[];adj=[]
for t,c in enumerate(cubes):
    tc=corners(c)
    ts=[k for k,x in enumerate(tc) if len(set(x))==3]
    bs=[k for k,x in enumerate(tc) if len(set(x))==2]
    tri.append(ts);bi.append(bs)
    (opp if not bs else adj).append(t)
M=[];sizes=[]
for t in range(75):
    M.append(np.array([[bool(v&m) for v in inc[t]] for m in range(1,256)],dtype=np.int16))
    sizes.append(np.array([m.bit_count() for m in range(1,256)],dtype=np.int16))
M=np.stack(M);sizes=np.stack(sizes)

def analyze(x):
    mass=M@np.array(x,dtype=np.int16)
    full=[t for t in range(75) if np.all(mass[t]>=sizes[t])]
    fast=[t for t in opp if t in full]
    robust=[]
    for t in adj:
        ts=tri[t];bs=bi[t]
        tmasks=[sum(1<<ts[k] for k in range(6) if m>>k&1) for m in range(1,64)]
        h=min(int(mass[t,m-1])-m.bit_count() for m in tmasks)
        if h>=2:
            robust.append(t)
            if all(mass[t,(1<<b)-1]>=1 for b in bs) and mass[t,sum(1<<b for b in bs)-1]>=2:fast.append(t)
    return full,fast,robust

def inventory(file):
    x=[0]*75
    for row in json.loads((ROOT/'data'/file).read_text())['collection']:
        x[cubes.index(canonical(row['faces']))]+=row['count']
    return x

if __name__=='__main__':
    for file in ['q5-initial.json','q5-three-variety-obstruction.json','q5-local-initial.json','q5-local-diverse.json']:
        x=inventory(file)
        print('base',file,'size',sum(x),'counts',[(cubes[i],v) for i,v in enumerate(x) if v],flush=True)
        missed=[]
        for i in range(75):
            y=x.copy();y[i]+=1
            full,fast,rob=analyze(y)
            assert full
            if not fast:
                missed.append(i)
                if len(missed)<=3:print('missed added',cubes[i],'fulltargets',[cubes[t] for t in full],'robust',[cubes[t] for t in rob],flush=True)
        print('missed',len(missed),missed,flush=True)
