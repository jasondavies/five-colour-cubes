#!/usr/bin/env python3
"""Rejection controls for the independent core-and-extension reader."""
import argparse
import json
from pathlib import Path
import tempfile
from classification_core_inputs import load_core_inputs
from check_classification_cores import Checker, read_geometry, validate_entries

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--results',type=Path)
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'build/classification-core-controls.json')
    a=p.parse_args()
    temp=tempfile.TemporaryDirectory(prefix='q5-core-controls-')
    if a.results is None:
        _, a.results=load_core_inputs(a.repo,Path(temp.name))
    rows=[list(map(int,l.split())) for l in
          (a.repo/'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    hall=read_geometry(a.repo/'data/five-colour-geometry.txt',False)
    path=a.results/'r58'
    meta=json.loads((path/'search.json').read_text())
    cores=[tuple(x) for x in meta['cores']]
    allowed=set(cores)
    original=rows[58].copy();original[3]=14
    projected=original.copy();projected[3]=14-original[5];projected[5]=0
    for i in range(75):
        if projected[81+i]:projected[6+i]=0
    cover=(path/'cover.q5c').read_bytes()
    lift=(path/'lift-0.q5l').read_bytes()
    def cover_check(data=cover,points=allowed):
        return Checker(data,projected,hall,points=points).run()
    def lift_check(data=lift,lower=cores[0]):
        return Checker(data,original,hall,lower=lower).run()
    def changed(data,index,value):
        out=bytearray(data);out[index]=value;return bytes(out)
    cover_check();lift_check()
    controls=[]
    def reject(name,call):
        try:call()
        except (ValueError,IndexError) as e:
            controls.append({'name':name,'rejected':True,'reason':str(e)})
        else:raise AssertionError('accepted invalid control: '+name)
    reject('cover_truncated',lambda:cover_check(cover[:-1]))
    reject('cover_trailing_bytes',lambda:cover_check(cover+b'\0'))
    reject('cover_bad_magic',lambda:cover_check(changed(cover,0,0)))
    reject('cover_wrong_goal',lambda:cover_check(changed(cover,7,12)))
    reject('cover_wrong_retained_budget',lambda:cover_check(changed(cover,9,1)))
    reject('cover_missing_core',lambda:cover_check(points=allowed-{cores[0]}))
    reject('cover_unobserved_core',lambda:cover_check(points=allowed|{(0,)*75}))
    relabel=list(cores[0]);i=next(i for i,x in enumerate(relabel) if x)
    j=next(i for i,x in enumerate(relabel) if not x);relabel[i],relabel[j]=relabel[j],relabel[i]
    reject('cover_relabelled_core',lambda:cover_check(points=(allowed-{cores[0]})|{tuple(relabel)}))
    pos=160
    while cover[pos]!=3:pos+=3 if cover[pos]==1 else 2
    reject('cover_bad_point_opcode_argument',lambda:cover_check(changed(cover,pos+1,1)))
    reject('cover_false_mass_close',lambda:cover_check(cover[:160]+bytes([0,0])))
    reject('cover_nonsingleton_point',lambda:cover_check(cover[:160]+bytes([3,0])))
    reject('cover_invalid_split',lambda:cover_check(cover[:160]+bytes([1,3,0,0,0,0,0])))
    reject('lift_truncated',lambda:lift_check(lift[:-1]))
    reject('lift_trailing_bytes',lambda:lift_check(lift+b'\0'))
    reject('lift_bad_magic',lambda:lift_check(changed(lift,0,0)))
    reject('lift_wrong_original_goal',lambda:lift_check(changed(lift,7,13)))
    reject('lift_wrong_original_budget',lambda:lift_check(changed(lift,9,0)))
    reject('lift_relabelled_core',lambda:lift_check(lower=cores[1]))
    reject('lift_changed_lower_bound',lambda:lift_check(changed(lift,160+3,1)))
    j=next(i for i in range(75) if not original[81+i] and original[6+i]>cores[0][i])
    reject('lift_illegal_unbudgeted_upper_tightening',
           lambda:lift_check(changed(lift,10+j,cores[0][j])))
    j=next(i for i in range(75) if original[81+i] and original[6+i]>0)
    reject('lift_illegal_budgeted_upper_tightening',lambda:lift_check(changed(lift,10+j,0)))
    reject('lift_false_mass_close',lambda:lift_check(lift[:235]+bytes([0,0])))
    reject('lift_point_leaf_forbidden',lambda:lift_check(lift[:235]+bytes([3,0])))
    entries=[(p,json.loads(p.read_text())) for p in a.results.glob('r*/search.json')]
    validate_entries(entries)
    reject('bundle_missing_root',lambda:validate_entries(entries[:-1]))
    reject('bundle_duplicate_root',lambda:validate_entries(entries[:-1]+entries[:1]))
    p0,m0=entries[0]
    reject('bundle_directory_root_mismatch',
           lambda:validate_entries([(p0.with_name('search.json').parent.with_name('r999')/'search.json',m0)]
                                   +entries[1:]))
    result={'valid_cover_and_lift_accepted':True,'controls':controls,
            'rejected':len(controls),'accepted_invalid':0}
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'Accepted valid cover/lift; rejected all {len(controls)} invalid controls.')

if __name__=='__main__':main()
