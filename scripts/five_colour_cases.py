#!/usr/bin/env python3
"""Export complete anchored Hall-cover cases for the compiled exact search."""
import argparse
from pathlib import Path
from case_geometry import geometry
from case_geometry import covers


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--size',type=int,default=15)
    p.add_argument('--multiplicity',type=int,nargs='*',default=list(range(1,8)))
    p.add_argument('--output',required=True)
    a=p.parse_args();data=geometry();_,opposite,anchors,pairs,_=data
    lines=[]
    for m in a.multiplicity:
        for kind in (0,1):
            anchor=anchors[kind]
            for bad,budget,k in covers(data,kind,m):
                upper=[m if kind==0 or f else m-1 for f in opposite]
                for i in range(75):
                    if bad>>i&1:upper[i]=min(upper[i],budget)
                for (i,j),values in pairs.items():
                    if i==anchor:
                        for v in values:
                            if v<=m:upper[j]=min(upper[j],7-v)
                    if j==anchor:
                        for v in values:
                            if 8-v<=m:upper[i]=min(upper[i],v-1)
                upper[anchor]=0
                lines.append(' '.join(map(str,[kind,m,k,a.size,anchor,budget,*upper,
                                              *[int(bad>>i&1) for i in range(75)]])))
    Path(a.output).write_text(str(len(lines))+'\n'+'\n'.join(lines)+'\n')
    print(len(lines),'cases')


if __name__=='__main__':main()
