#!/usr/bin/env python3
"""Replay retained Q5E1 certificates and serialize kernel-checked enumeration.

No search is run. --check compares the complete generated file set and bytes
without changing retained sources. Python/C++ outputs are untrusted: Lean
checks each root identity, weakening, checkpoint and coverage proof.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
from generate_five_colour_chunks import packed
from generate_five_colour_packed import cut

ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'FiveColour/EnumerationChunks'


class HallFamilies:
    """Geometry-only cuts and reduced families shared by identical root keys."""
    def __init__(self, geometry):
        self.cuts = tuple(tuple(
            (sum(1 << i for i, mask in enumerate(masks) if mask & subset),
             subset.bit_count() - 1)
            for subset in range(1, 256)) for masks in geometry)
        self.cache = {}

    def reduced(self, row):
        anchor, multiplicity = row[4], row[1]
        active = sum(1 << i for i in range(75) if i != anchor and row[6+i] > 0)
        key = (anchor, multiplicity, active)
        if key not in self.cache:
            result = []
            for cuts in self.cuts:
                best = {}
                for mask, rhs in cuts:
                    rhs -= multiplicity if mask >> anchor & 1 else 0
                    if rhs < 0:
                        continue
                    mask &= active
                    best[mask] = max(best.get(mask, -1), rhs)
                result.append(tuple((a, r) for a, r in sorted(best.items())
                    if not any(b != a and b & a == b and t >= r for b, t in best.items())))
            self.cache[key] = tuple(result)
        return self.cache[key]


def reduced_families(row, geometry):
    """Single-root convenience entry point used by the rejection controls."""
    return HallFamilies(geometry).reduced(row)


def case_sources(case, text, limit=10000):
    """Split oversized roots only at complete checkpoint namespace boundaries.

    The public declaration names and every proof term stay unchanged. Smaller
    roots retain their exact source bytes; each split root imports a chain of
    modules, so Lake checks all checkpoints before its existing endpoint.
    """
    entry = f'Case{case}.lean'
    if len(text.splitlines()) <= limit:
        return {entry: text}
    namespace = f'FiveColour.Packed.EnumerationChunks.Case{case}'
    chunks = re.split(r'(?m)(?=^namespace Part\d+\n)', text)
    base, blocks = chunks[0], chunks[1:]
    if not blocks:
        raise ValueError(f'oversized root {case} has no checkpoint boundaries')
    marker = '/-- Every admissible vector in the original root'
    last, separator, footer = blocks[-1].partition(marker)
    if not separator:
        raise ValueError(f'root {case} has no coverage endpoint')
    blocks[-1] = last
    footer = separator + footer
    sources = {f'Case{case}/Base.lean': base + f'end {namespace}\n'}
    previous = f'FiveColour.EnumerationChunks.Case{case}.Base'
    batch = []
    lines = 0

    def emit():
        nonlocal previous, batch, lines
        name = f'Case{case}/Parts{len(sources)-1}.lean'
        header = (f'module\npublic import {previous}\n@[expose] public section\n'
                  f'namespace {namespace}\nset_option maxHeartbeats 0\n'
                  'set_option maxRecDepth 100000\n')
        sources[name] = header + ''.join(batch) + f'end {namespace}\n'
        previous = 'FiveColour.EnumerationChunks.' + name[:-5].replace('/', '.')
        batch = []
        lines = 0

    for index, block in enumerate(blocks):
        if not block.startswith(f'namespace Part{index}\n'):
            raise ValueError(f'nonconsecutive checkpoint {case}:{index}')
        count = len(block.splitlines())
        if batch and lines + count + 7 > limit:
            emit()
        batch.append(block)
        lines += count
    if batch:
        emit()
    sources[entry] = (f'module\npublic import {previous}\n@[expose] public section\n'
                      f'namespace {namespace}\nset_option maxHeartbeats 0\n'
                      'set_option maxRecDepth 100000\n' + footer)
    oversized = [name for name, source in sources.items() if len(source.splitlines()) > limit]
    if oversized:
        raise ValueError(f'generated modules exceed {limit} lines: {oversized}')
    return sources


def generate_case(i,row,original,points,hall_cuts,families,checkpoint,dest):
    lines=checkpoint.read_text().splitlines()
    used=sorted({int(x)-3 for line in lines for x in re.findall(r'\.(?:step|close) (\d+)',line) if int(x)>=3})
    hi=list(row[6:81]);hi[row[4]]=row[1]
    buf=io.StringIO();w=buf.write
    w(f'''module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case{i}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root {original}
def families : Fin 78 → List Cut := Enumeration.families {original}
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid {original}
def points : List Nat := ['''+','.join(str(packed(v)) for v in points)+']\n')
    for t in used:
        cs=families[t];witnesses=[]
        for subset,(mask,rhs) in enumerate(hall_cuts[t],1):
            # Only the anchor has a nonzero lower bound. Reduced masks omit
            # it, so their lower-bound mass is zero.
            lm = row[1] if mask >> row[4] & 1 else 0
            if lm>rhs or 14>rhs+sum(hi[j] for j in range(75) if not mask>>j&1):witnesses.append(0);continue
            candidate = next((k for k,(d,s) in enumerate(cs)
                              if d & mask == d and rhs <= s + lm), None)
            if candidate is None:raise ValueError(('uncovered cut',i,t,subset))
            witnesses.append(candidate)
        w(f'def reduced{t} : Array Cut := #['+','.join(cut([j for j in range(75) if m>>j&1],r) for m,r in cs)+']\n')
        w(f'def witnesses{t} : List Nat := ['+','.join(map(str,witnesses))+']\n')
        w(f'''theorem valid{t} : ∀ c ∈ reduced{t}.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered{t} : ∀ c ∈ families {t+3}, possible root 14 c →
    ∃ d ∈ reduced{t}.toList, relaxes root c d = true :=
  covers_sound root 14 reduced{t} (families {t+3}) witnesses{t} (by decide +kernel)
''')
    w('def checkedFamilies (r : Fin 78) : List Cut :=\n  match r.val with\n')
    w(''.join(f'  | {t+3} => reduced{t}.toList\n' for t in used)+'  | _ => families r\n')
    w('theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by\n  intro r\n  fin_cases r\n')
    w(''.join(f'  · exact valid{j-3}\n' if j-3 in used else f'  · exact families_valid {j}\n' for j in range(78)))
    w('theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root 14 c →\n    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by\n  intro r\n  fin_cases r\n')
    w(''.join(f'  · exact covered{j-3}\n' if j-3 in used else '  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩\n' for j in range(78)))
    sizes=[]
    for line in lines:
        ident,l,h,size,refs,proof=line.split('\t');ident=int(ident);size=int(size)
        refs=list(map(int,refs.split(','))) if refs else []
        if ident!=len(sizes) or not 1<=size<=128 or any(r>=ident or r<0 for r in refs):raise ValueError('bad chunks')
        sizes.append(size)
        rv='!['+', '.join(f'Part{r}.root' for r in refs)+']' if refs else 'Fin.elim0'
        w(f'''namespace Part{ident}
def root : Box := ⟨{packed(l)}, {packed(h)}⟩
def references : Fin {len(refs)} → Box := {rv}
def proof : Enumeration.Proof {len(refs)} := {proof}
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
''')
        if refs:w('  intro i\n  fin_cases i\n'+''.join(f'  · exact Part{r}.covered\n' for r in refs))
        else:w('  intro i\n  exact Fin.elim0 i\n')
        w(f'''theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part{ident}
''')
    w(f'''/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid {original}) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part{len(sizes)-1}.covered
end FiveColour.Packed.EnumerationChunks.Case{i}
''')
    for name, source in case_sources(i, buf.getvalue()).items():
        path = dest/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    return {'case':i,'original_root':original,'commands':sum(sizes),'chunks':len(sizes),'points':len(points)}


def generate(dest,work,workers):
    info=json.loads((ROOT/'data/five-colour-classification.json').read_text())
    if info['format']!=1 or len(info['roots'])!=349:raise ValueError('bad classification input')
    originals=[list(map(int,l.split())) for l in (ROOT/'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    rows=[]
    for r in info['roots']:
        row=list(originals[r['original_root']]);row[3]=14;rows.append(row)
    if {r['original_root'] for r in info['roots']}!={i for i,r in enumerate(originals) if r[1]<=5}:raise ValueError('incomplete root set')
    cases=work/'cases.txt';cases.write_text('349\n'+'\n'.join(' '.join(map(str,r)) for r in rows)+'\n')
    geometry=[list(map(int,l.split())) for l in (ROOT/'data/five-colour-geometry.txt').read_text().splitlines()[76:]]
    with tarfile.open(ROOT/'data/five-colour-classification-certificates.tar.gz') as archive:
        members=archive.getmembers();expected={f'case-{i}.q5p' for i in range(349)}
        if len(members)!=349 or {m.name for m in members}!=expected or any(not m.isfile() for m in members):raise ValueError('unexpected archive entries')
        for i,r in enumerate(info['roots']):
            payload=archive.extractfile(f'case-{i}.q5p').read()
            if hashlib.sha256(payload).hexdigest()!=r['certificate_sha256']:raise ValueError('certificate hash mismatch')
            (work/f'case-{i}.q5p').write_bytes(payload)
    dest.mkdir(parents=True,exist_ok=True)
    hall = HallFamilies(geometry)
    # Populate once before workers: subsequent accesses are read-only.
    root_families = [hall.reduced(row) for row in rows]
    def one(i):
        entry=info['roots'][i];points=[]
        for j in entry['terminals']:
            counts=Counter(info['terminals'][j]);points.append([counts[k] for k in range(75)])
        fs=root_families[i]
        ffile=work/f'families{i}.txt';pfile=work/f'points{i}.txt';tsv=work/f'chunks{i}.tsv'
        ffile.write_text('\n'.join(str(len(f))+'\n'+'\n'.join(f'{m&((1<<64)-1)} {m>>64} {r}' for m,r in f) for f in fs)+'\n')
        pfile.write_text(str(len(points))+'\n'+'\n'.join(' '.join(map(str,v)) for v in points)+'\n')
        subprocess.run([str(ROOT/'build/five_colour_enumeration'),str(ROOT/'data/five-colour-geometry.txt'),str(cases),str(work/f'case-{i}.q5p'),str(i),'128',str(tsv),str(ffile),str(pfile)],check=True,stdout=subprocess.DEVNULL)
        return generate_case(i,rows[i],entry['original_root'],points,hall.cuts,fs,tsv,dest)
    with ThreadPoolExecutor(max_workers=workers) as pool:records=list(pool.map(one,range(349)))
    (dest/'manifest.json').write_text(json.dumps({'format':'Q5E1','cases':records,'commands':sum(r['commands'] for r in records),'chunks':sum(r['chunks'] for r in records)},indent=2)+'\n')
    # Keep groups small so the aggregate does not import hundreds of proofs into
    # one large tactic invocation.
    for group in range(18):
        ids=list(range(group*20,min(349,(group+1)*20)))
        text='module\n'+''.join(f'public import FiveColour.EnumerationChunks.Case{i}\n' for i in ids)
        text+='@[expose] public section\nnamespace FiveColour.Packed.EnumerationChunks\n'
        text+=f'def group{group}Roots : Fin {len(ids)} → Fin 357 := !['+','.join(str(info['roots'][i]['original_root']) for i in ids)+']\n'
        text+=f'def group{group}Points : Fin {len(ids)} → List Nat := !['+','.join(f'Case{i}.points' for i in ids)+']\n'
        text+=f'theorem group{group}Covered : ∀ i, Enumeration.Covers (group{group}Points i) 14 (Enumeration.families (group{group}Roots i)) (Archive.root (group{group}Roots i)) := by\n  intro i\n  fin_cases i\n'
        text+=''.join(f'  · exact Case{i}.covered\n' for i in ids)+'end FiveColour.Packed.EnumerationChunks\n'
        (dest/f'Group{group}.lean').write_text(text)
    return records


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');parser.add_argument('--workers',type=int,default=2);args=parser.parse_args()
    if args.workers<1:parser.error('workers must be positive')
    subprocess.run(['make','build/five_colour_enumeration'],cwd=ROOT,check=True)
    with tempfile.TemporaryDirectory(prefix='q5-enumeration-') as temp:
        work=Path(temp);dest=work/'generated' if args.check else DEST
        records=generate(dest,work,args.workers)
        if args.check:
            expected={str(p.relative_to(dest)) for p in dest.rglob('*') if p.is_file()};actual={str(p.relative_to(DEST)) for p in DEST.rglob('*') if p.is_file()}
            if expected!=actual:raise SystemExit(f'enumeration file set differs: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}')
            changed=[name for name in expected if (dest/name).read_bytes()!=(DEST/name).read_bytes()]
            if changed:raise SystemExit(f'enumeration files differ: {changed}')
    print(f'Checked {len(records)} classification certificates; {sum(r["commands"] for r in records):,} instructions.')
if __name__=='__main__':main()
