"""Find/check small explicit witnesses for the four residual cut families.

Discovery aid only: this does not prove these are the only possible families.
The hand note gives the independent repeated-colour conclusion once one of
the stated family hypotheses is established.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CUTS, CORNERS, CLASSES, V

FAMILIES = ((2, 8, 11, 19), (4, 7, 10, 17),
            (4, 7, 13, 14), (4, 9, 10, 17))

def name(j):
    p,s=CLASSES[j]
    return 'C'+''.join(map(str, sorted(p if s==1 else set(V)-set(p))))

def assignment(copies, target):
    corners=sorted(CUTS[target])
    masks=[set(CUTS[j] if j<20 else CORNERS[j]) & set(corners)
           for j in copies]
    owners=[None]*len(copies)
    def augment(c,seen):
        for i,m in enumerate(masks):
            if i in seen or c not in m:
                continue
            seen.add(i)
            if owners[i] is None or augment(owners[i],seen):
                owners[i]=c
                return True
        return False
    if not all(augment(c,set()) for c in corners):
        return None
    return [(copies[i],c) for i,c in enumerate(owners) if c is not None]

def main():
    output=[]
    for fi,fam in enumerate(FAMILIES,1):
        for target in fam:
            # Reserve two of the target triple. Every other class has >=2.
            copies=[j for j in fam for _ in range(1 if j==target else 2)]
            copies += [71,73,73]
            w=assignment(copies,target)
            assert w is not None
            counts={j:copies.count(j) for j in copies}
            used={j:sum(s==j for s,c in w) for j in counts}
            assert all(used[j]<=counts[j] for j in used)
            assert {c for s,c in w}==CUTS[target]
            row={'family':fi,'classes':list(fam),'target':target,
                 'assignment':[(s,''.join(map(str,c[1:]))) for s,c in w]}
            output.append(row)
            print(fi,','.join(name(j) for j in fam),'target',name(target),
                  '; '.join(('P' if s==71 else 'Q' if s==73 else name(s))+':'+''.join(map(str,c[1:])) for s,c in w))
    triple=(4,10,17)
    for target in triple:
        copies=[j for j in triple for _ in range(1 if j==target else 3)]+[71,73]
        w=assignment(copies,target)
        assert w is not None
        output.append({'triple_core':list(triple),'opposite':[71,73],
                       'target':target,'assignment':[(s,''.join(map(str,c[1:]))) for s,c in w]})
        print('triple core target',name(target),'; '.join(('P' if s==71 else 'Q' if s==73 else name(s))+':'+''.join(map(str,c[1:])) for s,c in w))
    Path(__file__).with_name('adjacent-residual-witnesses.json').write_text(json.dumps(output,indent=2)+'\n')

if __name__=='__main__':
    main()
