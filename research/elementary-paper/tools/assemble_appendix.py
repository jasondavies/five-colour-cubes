#!/usr/bin/env python3
"""Assemble a review draft of the necessary mathematical appendix.

This performs editorial extraction and reference conversion, not verification.
The manifest records exactly which source sections were retained.
"""
from pathlib import Path
import re,json,hashlib,subprocess,collections
BASE=Path(__file__).resolve().parents[1]
SRC=BASE.parent/'elementary-review-2026-11-04/research'
OUT=BASE/'paper'
ALL=list(SRC.rglob('*.md'));BYNAME=collections.defaultdict(list)
for p in ALL:BYNAME[p.name].append(p.relative_to(SRC).as_posix())
# These are theorem dependencies, not folders of discovery history.
START=['root/six-adjacent-elementary.md','opposite_small_lemma/three-opposite-pairs.md',
 'root/o4-elementary.md','root/o3-covers-guide.md',
 *['mixed_diffuse/'+n+'.md' for n in ['five-class-mixed-hand-proof','four-class-four-opposites-hand-proof','four-class-three-opposites-hand-proof','four-class-two-distinct-opposites-hand-proof','four-class-two-identical-opposites-hand-proof','four-class-one-opposite-hand-proof','one-opposite-row-cover-hand-proof']],
 'root/pure-fifteen-elementary.md','elementary_alternative_next/one-opposite-fourteen-adjacent.md',
 'root/three-opposites-eleven-adjacent.md','three_opposite_distinct/two-star-two-opposites.md',
 'elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md',
 'three_opposite_double/star-triangle-thirteen-adjacent-hand.md',
 'root/five-opposites-nine-adjacent.md','root/eight-opposite-elementary.md']
OMIT={'root/fifteen-elementary-proof.md','root/two-opposites-thirteen-adjacent.md',
 'root/four-opposites-ten-adjacent.md','root/eight-distinct-class-counterexample.md',
 'five_opposite_profiles/two-pairs-two-adjacent-one.md'}
MAIN={'root/eight-plus-three-common-missing-pair.md': 'the main article’s eight-plus-three lemma',
 'three_opposite_root/pair-compression-and-intersecting-cuts.md': 'the main article’s disjoint-cut compression and intersecting-cuts lemmas',
 'three_opposite_root/repeated-colour-closures.md': 'the main article’s nine-source construction'}
# Subresults borrowed from older longer proofs: retain the actual geometry,
# not the numerical four- or six-opposite theorems that are no longer needed.
SECTIONS={
 'four_opposite_lowrep/four-distinct-opposites.md':{'1'},
 'four_opposite_root/common-high-targets.md':{'1','3'},
 'opposite_small_lemma/nine-opposite-sources.md':{'3'},
 'invariant_structure/elementary_refinements.md':{'1','2','3','5','6'},
 'root/five-opposites-nine-adjacent.md':{'Result','1','2','3','4'},
 'root/pure-fifteen-elementary.md':{'1','2'},
}
TITLES={'root/o4-elementary.md':'Four identical opposite copies',
 'root/o3-covers-guide.md':'Three identical opposite copies',
 'four_opposite_lowrep/four-distinct-opposites.md':'Cut intersections on an opposite target',
 'four_opposite_root/common-high-targets.md':'Avoided edges and common high targets',
 'opposite_small_lemma/nine-opposite-sources.md':'Two four-cycle line normal forms',
 'invariant_structure/elementary_refinements.md':'Butterfly repeats and concentrated-opposite tools'}
# Mathematical uses named in prose rather than by filenames. This records
# the dependency checks made during the bounded pass, not a claim that every
# implicit premise in the research bundle has been audited.
MANUAL_DEPS={
 'root/o3-covers-guide.md':['root/o4-elementary.md'],
 'invariant_structure/elementary_refinements.md':['root/o4-elementary.md'],
 'root/g3-private-column-hand.md':['root/six-doubled-classes-hand.md'],
 'pure_supported/private-diagonal-unconditional-hand.md':['pure_supported/g3-nonprivate-hand.md','pure_supported/two-own-loop-triples-hand.md'],
 'mixed_diffuse/butterfly-plus-opposite-hand-proof.md':['invariant_structure/elementary_refinements.md'],
 'root/pure-fifteen-elementary.md':['root/six-adjacent-elementary.md','pure_supported/g4-row-hand.md','pure_supported/g4-hook-disjoint-hand.md','pure_supported/g4-exception-hand.md'],
}

def resolve(f,ref):
 q=(SRC/f).parent/ref
 try:
  if q.exists():return q.resolve().relative_to(SRC.resolve()).as_posix()
 except ValueError:pass
 q=SRC.parent/ref
 if q.exists():return q.resolve().relative_to(SRC.resolve()).as_posix()
 choices=BYNAME[Path(ref).name]
 if len(choices)==1:return choices[0]
 return None

def excluded(ref):
 return any(t in ref.lower() for t in ['audit','checkpoint','next_step','dependency-outline'])

def content(f):
 override=BASE/'overrides'/f
 s=(override if override.exists() else SRC/f).read_text()
 pieces=re.split(r'(?=^## )',s,flags=re.M)
 keep=[]
 for i,part in enumerate(pieces):
  title=part.splitlines()[0] if part else ''
  num=re.match(r'## (\d+)',title)
  key=num.group(1) if num else title.removeprefix('## ').strip()
  if i and f in SECTIONS and key not in SECTIONS[f]:continue
  if re.match(r'## (?:\d+\. )?(?:Scope|Verification|Independent audit|Provenance|Audits?|Proof status|Current status|Application to the exploratory|Consequences and exact scope|Consequence for the fourteen|Consequence: the seven-source rescue)',title,re.I):continue
  if i==0 and f in SECTIONS and f not in ('root/pure-fifteen-elementary.md','root/five-opposites-nine-adjacent.md'):
   part='# '+TITLES.get(f,title.lstrip('# '))+'\n\n'
  keep.append(part)
 s=''.join(keep)
 s=re.sub(r'\*\*Status:.*?(?:\n\n|\Z)','',s,flags=re.S)
 s=re.sub(r'^\d{1,2} November 2026\s*\n','',s,flags=re.M)
 if f in TITLES:s=re.sub(r'^# .*',lambda m:'# '+TITLES[f],s,count=1)
 # Remove purely historical/reporting paragraphs; keep theorem/proof paragraphs.
 paras=s.split('\n\n'); cleaned=[]
 for p in paras:
  if any(v in p for v in ['independent mathematical audit','independent root audit','production repository','No new Lean','The accompanying checker','The exploratory script','The proof was independently','The statement was originally recorded']):continue
  if p.startswith(('The audit and adapted proof','The independent audit','This note supplies the main reduction for four opposite','The source multiset is 2D+P+Q','Both component arguments have passed')):continue
  cleaned.append(p)
 s='\n\n'.join(cleaned)
 s=re.sub(r'Section\s*2\s+of\s+`[^`]*repeated-colour-closures\.md`',
  'the main article’s nine-source construction',s,flags=re.I)
 if f=='four_opposite_root/common-high-targets.md':
  # Only the nine-avoider observation is used from the first section.
  s=re.sub(r'### Ten capped adjacent sources.*?(?=## 3\.)','',s,flags=re.S)
  s=re.sub(r'Consequently at least two of the ten adjacent cubes.*?\n\n','',s,flags=re.S)
  s=s.replace('Consequently\nSection 2 already solves every triple containing a neighbouring pair.','')
  s=s.replace('The O72 row is fully supported, so Section 2 solves it.','')
 if f=='opposite_small_lemma/nine-opposite-sources.md':
  s=s.replace('The graph \\(L\\) contains at least three distinct four-cycles.',
   'Let \\(P,Q\\) be four-cycles sharing exactly one edge \\(e\\). Let disjoint two-edge sets \\(F\\subset P\\setminus Q\\) and \\(G\\subset Q\\setminus P\\) have six-edge complement \\(L\\) in \\(K_5\\). Suppose \\(L\\) contains at least two distinct four-cycles.')
  s=s.replace('Thus the three common avoiders are precisely the three\nline varieties in \\(L\\), and all occur as single source copies.','')
 return s

texts={};edges={};unresolved=[]
def visit(f):
 if f in texts or f in OMIT or f in MAIN or excluded(f):return
 s=content(f);texts[f]=s;deps=[]
 for ref in re.findall(r'[\w./-]+\.md',s):
  if excluded(ref):continue
  q=resolve(f,ref)
  if q is None:unresolved.append([f,ref]);continue
  if q in OMIT or q in MAIN:continue
  deps.append(q);visit(q)
 for q in MANUAL_DEPS.get(f,[]):
  deps.append(q);visit(q)
 edges[f]=sorted(set(deps))
for f in START:visit(f)
# The shared missing-pair lemma is proved in the main article before the corner proof.
texts.pop('root/eight-plus-three-common-missing-pair.md',None)
# Arrange foundations before the numerical cases. Local numbered divisions
# retain their original numbers so sectional cross-references remain meaningful.
rank={'root':2,'support_families':3,'invariant_structure':4,'robust_route':4,
 'pure_supported':5,'mixed_diffuse':6,'opposite_small_lemma':1,
 'four_opposite_lowrep':1,'four_opposite_root':1,'five_opposite_profiles':8,
 'elementary_alternative_next':9,'three_opposite_double':10,
 'three_opposite_distinct':11,'three_opposite_root':7}
ordered=[];pending=set(texts)
while pending:
 ready=[f for f in pending if not (set(edges[f])&pending)]
 if not ready:raise RuntimeError('Unresolved reference cycle: '+', '.join(sorted(pending)))
 f=min(ready,key=lambda f:(rank.get(f.split('/')[0],8),f))
 ordered.append(f);pending.remove(f)
ids={f:'arg-'+str(i+1) for i,f in enumerate(ordered)}
labels={f:re.search(r'^# (.*)',s,re.M).group(1) for f,s in texts.items()}
intro='''---
title: "Mathematical appendix to Sharp thresholds for five-colour cube assemblies"
author: "Jason Davies"
date: "Consolidation draft, 4 November 2026"
geometry: margin=22mm
fontsize: 10pt
mainfont: DejaVu Serif
monofont: DejaVu Sans Mono
---

# Reading this mathematical appendix

This appendix is an integral mathematical part of the article, intended for
refereeing with it. It contains the longer corner arguments used by the direct
fifteen-source proof. The alternative certificate proof, executable audits,
and Lean implementation are described separately.

**Editorial status.** This is a consolidation draft. The arguments have been
collected and cross-linked from the proof-development notes. A final editorial
pass is still needed to shorten repetitions and standardise all local notation.
No claim is made that this appendix follows the existing Lean proof route.

A directed corner $ab$ abbreviates the complementary cyclic tricoloured corner.
$C(S)=S\\to V\\setminus S$, where $V=\\{0,1,2,3,4\\}$, is an adjacent class.
Its pole pair is the two-element side, and a repeated colour lies outside that
pair. An opposite variety supplies both directions of the edges of a four-cycle.
Every multiplicity refers to physical source copies. Hall matchings select
distinct copies; repeated entries assigned to one variety use separate copies.
An *own loop* in the arguments below is the article's *own completion*: a
matching of the six tricoloured corners after two class copies are reserved.

Arguments are ordered so that the recorded dependencies precede their uses.
This includes explicit file references and the implicit dependencies reviewed
in the bounded simplification pass; it is not a certification that every
implicit dependency has been found. Internal divisions retain local numbers: “Section 3” means local
division 3 of that argument unless another argument is named. Links to another
argument replace the research filenames. The prescribed-family eight-plus-three
lemma is proved in the main article's shared geometric tools, independently of
the corner threshold.

The proof uses mathematical case exhaustion and the displayed Hall tables.
Programs used to discover or audit these tables are not premises of the proof.

'''
# Research labels are convenience names, not an appeal to a checked catalogue.
# Define them explicitly so every displayed construction can be read on paper.
codebook='## Opposite-variety names\n\n'
codebook+='The local names $O_{60},\\ldots,O_{74}$ (also printed O60, etc.) denote the following bidirected four-cycles. Each row means all edges joining the two displayed pairs; the remaining colour is repeated.\n\n'
codebook+='| Name | Repeated colour | Bipartition |\n|---|---:|---|\n'
i=60
for r in range(5):
 left=[v for v in range(5) if v!=r]
 for b in left[1:]:
  p=(left[0],b);q=tuple(v for v in left if v not in p)
  codebook+=f'| O{i} | {r} | {p[0]}{p[1]} / {q[0]}{q[1]} |\n';i+=1
parts=[intro,codebook+'\n']
for i,f in enumerate(ordered):
 s=texts[f]
 # File references are internal mathematical cross-references, not repository links.
 def replace_ref(m):
  ref=m.group(0);q=resolve(f,ref)
  if q in MAIN:return MAIN[q]
  if q in ids:return '[Argument '+str(ordered.index(q)+1)+'](#'+ids[q]+')'
  if q in OMIT:return 'the main article’s direct fifteen-source argument'
  if excluded(ref):return 'the proof-development record'
  unresolved.append([f,ref]);return ref
 # First unwrap links/code spans enclosing a filename, then replace the filename.
 s=re.sub(r'\[([^]]+)\]\(([^)]+\.md)\)',lambda m:m.group(2),s)
 s=re.sub(r'`([^`\n]+\.md)`',lambda m:m.group(1),s)
 s=re.sub(r'[\w./-]+\.md',replace_ref,s)
 title=labels[f]
 s=re.sub(r'^# .*',lambda m:'# Argument '+str(i+1)+': '+title+' {#'+ids[f]+'}',s,count=1)
 # Local section numbers are deliberately unnumbered by LaTeX.
 s=re.sub(r'^(#{2,6}) (.*)$',lambda m:m.group(1)+' '+m.group(2)+' {.unnumbered}',s,flags=re.M)
 parts.append(s+'\n\n')
(OUT/'elementary-appendix.md').write_text('\n'.join(parts))
manifest={'status':'editorial consolidation draft','archive_sha256':'146aa371dbd612d8678ce48a1a79bdc5078b76ea035eabf831a3829d13aa68de','arguments':[{'source':f,'title':labels[f],'id':ids[f],'retained_sections':sorted(SECTIONS[f]) if f in SECTIONS else 'mathematical sections','sha256':hashlib.sha256((SRC/f).read_bytes()).hexdigest()} for f in ordered],'unresolved_references':sorted(set(tuple(x)for x in unresolved)),'words':sum(len(s.split()) for s in texts.values())}
(BASE/'appendix-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
locations=[
 ('Concentrated opposite profiles',['root/o3-covers-guide.md','root/o4-elementary.md']),
 ('Fifteen adjacent sources',['root/pure-fifteen-elementary.md']),
 ('One opposite and fourteen adjacent',['elementary_alternative_next/one-opposite-fourteen-adjacent.md']),
 ('Three opposite and eleven adjacent',['root/three-opposites-eleven-adjacent.md']),
 ('Five-opposite helper construction',['root/five-opposites-nine-adjacent.md']),
 ('Nine distinct adjacent classes',['root/nine-distinct-hall-proof.md']),
 ('Eight opposite; seven plus one adjacent',['root/eight-opposite-elementary.md']),
 ('Butterfly; two stars; star and triangle',['elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md','three_opposite_distinct/two-star-two-opposites.md','three_opposite_double/star-triangle-thirteen-adjacent-hand.md'])]
table=['% Generated by assemble_appendix.py; do not renumber by hand.',r'\[\begin{array}{l|l}',r'\text{Input}&\text{Appendix argument}\\\hline']
for label,files in locations:
 table.append(r'\text{'+label+'}&'+','.join(str(ordered.index(f)+1) for f in files)+r'\\')
table.append(r'\end{array}\]')
(OUT/'elementary-locations.tex').write_text('\n'.join(table)+'\n')
for entry in manifest['arguments']:
 f=entry['source'];override=BASE/'overrides'/f
 entry['edited_text_sha256']=hashlib.sha256(texts[f].encode()).hexdigest()
 entry['edited_words']=len(texts[f].split())
 entry['references']=[q for q in edges[f] if q in ids]
 if override.exists():
  entry['editorial_override']=str(override.relative_to(BASE))
  entry['editorial_override_sha256']=hashlib.sha256(override.read_bytes()).hexdigest()
(BASE/'appendix-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(ordered),'arguments;',manifest['words'],'words;',len(manifest['unresolved_references']),'unresolved file references')
subprocess.run(['pandoc','elementary-appendix.md','-f','markdown+tex_math_single_backslash-raw_tex','-s','--toc','--no-highlight','-o','five-colour-elementary-appendix.tex','--pdf-engine=pdflatex','--include-in-header=appendix-format.tex'],cwd=OUT,check=True)
