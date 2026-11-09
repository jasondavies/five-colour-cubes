"""Generate complete core covers and original-bound extension exclusions.

Core trees are translated to existing Q5E1 rules and replayed by the production
reader. Lean checks coverage, extensions and the uniform projection bridge.
"""
import io
import subprocess
from generate_five_colour_chunks import packed, problem
from generate_five_colour_projection import encoded_header
from classification_projection import projected_row


def translate_cover(raw):
    if raw[:4] != b'Q5C1' or len(raw) < 160:
        raise ValueError('invalid core cover')
    out = bytearray(b'Q5E1'+raw[4:160]);p=160
    while p<len(raw):
        if p+2>len(raw):raise ValueError('truncated core opcode')
        op,a=raw[p:p+2];p+=2
        if op==1:
            if p>=len(raw):raise ValueError('truncated core split')
            out.extend([op,a,raw[p]]);p+=1
        elif op==3:
            if a!=0:raise ValueError('invalid point opcode')
            out.extend([op,a])
        elif op==0:out.extend([0,255 if a==0 else a+1])
        elif op==2:out.extend([2,0,2,1] if a==0 else [2,a+1])
        else:raise ValueError('invalid core opcode')
    return bytes(out)


def extension_proof(raw, original, core):
    if raw[:235]!=b'Q5L1'+bytes(original)+bytes(core):
        raise ValueError('extension must restore all original bounds and budget')
    steps=[];p=235;leaf=None
    while p<len(raw):
        if p+2>len(raw):raise ValueError('truncated extension opcode')
        op,a=raw[p:p+2];p+=2
        if op==2 and 1<=a<=76:steps.append(a+1)
        elif op==0 and 0<=a<=76:
            if p!=len(raw):raise ValueError('trailing extension instructions')
            leaf='.mass' if a==0 else f'(.close {a+1})'
        else:raise ValueError('unsupported extension opcode; expected propagation only')
    if leaf is None:raise ValueError('missing extension exclusion')
    proof='(.run '+leaf+')'
    for r in reversed(steps):proof=f'(.step {r} {proof})'
    return proof,len(steps)+1


def generate_core_case(root,i,original,source,record,folder,hall,work,dest):
    row=projected_row(source,0);goal=row[3];points=record['cores']
    if record['projected_total']!=goal:raise ValueError('incorrect core total')
    original_row=source.copy();original_row[3]=14
    raw=(folder/'cover.q5c').read_bytes()
    if raw[:160]!=b'Q5C1'+bytes(row):raise ValueError('core header mismatch')
    certificate=work/f'core-{i}.q5e';certificate.write_bytes(translate_cover(raw))
    cases=work/f'core-{i}.cases';cases.write_text('1\n'+' '.join(map(str,row))+'\n')
    ps=work/f'core-{i}.points';ps.write_text(str(len(points))+'\n'+'\n'.join(' '.join(map(str,p)) for p in points)+'\n')
    fs=work/'core-families.txt'
    tsv=work/f'core-{i}.tsv'
    subprocess.run([str(root/'build/five_colour_enumeration'),str(root/'data/five-colour-geometry.txt'),str(cases),str(certificate),'0','128',str(tsv),str(fs),str(ps)],check=True,stdout=subprocess.DEVNULL)
    buf=io.StringIO();w=buf.write
    ns=f'FiveColour.Packed.EnumerationChunks.Case{i}'
    w(f'''module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace {ns}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
''')
    w('def header : Archive.Header := ⟨'+','.join(map(str,encoded_header(row)))+'⟩\n')
    w(f'theorem header_valid : Projection.HeaderValid 14 {original} 0 {goal} header := by decide +kernel\n')
    upper=encoded_header(original_row)[1]
    w(f'def originalUpper : Nat := {upper}\n')
    w(f'theorem upper_eq : originalUpper = (Archive.root {original}).upper := by decide +kernel\n')
    w('namespace Core\n'+problem(row))
    w('def points : List Nat := ['+','.join(str(packed(p)) for p in points)+']\n')
    chunks=tsv.read_text().splitlines();cover_ops=0
    for k,line in enumerate(chunks):
        ident,lo,hi,size,refs,proof=line.split('\t');refs=[int(r) for r in refs.split(',')] if refs else []
        if int(ident)!=k or not 1<=int(size)<=128 or any(r>=k or r<0 for r in refs):raise ValueError('invalid core checkpoint order')
        cover_ops+=int(size)
        rv='!['+', '.join(f'Part{r}.root' for r in refs)+']' if refs else 'Fin.elim0'
        w(f'''namespace Part{k}
def root : Box := ⟨{packed(lo)}, {packed(hi)}⟩
def references : Fin {len(refs)} → Box := {rv}
def proof : Enumeration.Proof {len(refs)} := {proof}
theorem accepted : Enumeration.check points {goal} families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points {goal} families (references i) := by
''')
        if refs:w('  intro i\n  fin_cases i\n'+''.join(f'  · exact Part{r}.covered\n' for r in refs))
        else:w('  intro i\n  exact Fin.elim0 i\n')
        w(f'''theorem covered : Enumeration.Covers points {goal} families root :=
  Enumeration.check_sound points {goal} families families_valid references references_covered proof root root_valid accepted
end Part{k}
''')
    w(f'''theorem covered : Enumeration.Covers points {goal} families root := Part{len(chunks)-1}.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families {goal} header := rfl
end Core
''')
    lift_ops=0
    for j,p in enumerate(points):
        proof,n=extension_proof((folder/f'lift-{j}.q5l').read_bytes(),original_row,p);lift_ops+=n
        w(f'''namespace Lift{j}
def root : Box := ⟨{packed(p)}, originalUpper⟩
def proof : Chunks.Proof 0 := {proof}
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families {original}) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families {original}) root :=
  Fast.check_sound 14 (Enumeration.families {original}) (Enumeration.families_valid {original})
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift{j}
''')
    w(f'''theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families {original}) (CoreExtension.extension {original} p) := by
  exact ''')
    # A linear list proof avoids a large equality case split over all cores.
    proof='List.forall_mem_nil _'
    for j in reversed(range(len(points))):
        leaf=f'(by simpa only [Lift{j}.root, upper_eq, CoreExtension.extension] using Lift{j}.excludes)'
        proof=f'List.forall_mem_cons.mpr ⟨{leaf},\n    {proof}⟩'
    w(proof+'\n')
    w(f'''theorem covered : Enumeration.Covers [] 14 (Enumeration.families {original}) (Archive.root {original}) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model {original})
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end {ns}
''')
    text=buf.getvalue()
    if len(text.splitlines())>10000:raise ValueError('core root exceeds source line limit')
    (dest/f'Case{i}.lean').write_text(text)
    return {'case':i,'original_root':original,'commands':cover_ops+lift_ops,'chunks':len(chunks)+len(points),
            'points':0,'route':'core extensions','projected_total':goal,'cores':len(points),
            'cover_commands':cover_ops,'extension_commands':lift_ops}
