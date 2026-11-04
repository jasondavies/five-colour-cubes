#!/usr/bin/env python3
from pathlib import Path
import re
BASE=Path(__file__).resolve().parents[1];D=BASE/'paper'
# This review branch retains the unchanged production paper at the repository root.
SRC=BASE.parent.parent/'paper'
s=(SRC/'five-colour-cubes.tex').read_text();boxes=(SRC/'boxes.tex').read_text()
start=s.index('\\section{Reduction to finite problems}')
end=s.index('\\section{Compatibility and missing-pair families}')
cert=s[start:end]
geoend=s.index('\\input{boxes}')
shared=s[end:geoend]
# Move the projection and eight-plus-three proofs before the new corner proof.
bs=boxes.index('\\subsection{Signed corner projections}')
be=boxes.index('\\subsection{A uniform lower bound}')
shared+=boxes[bs:be]
shared=shared.replace('\\section{Compatibility and missing-pair families}','\\section{Shared geometric and matching tools}')
shared=shared.replace('The frame arguments depend on how many positions a source can miss.',
 'The corner and frame arguments share the following geometric and matching tools.\nAll statements in this section are independent of the corner threshold.')
boxes=boxes[:bs]+boxes[be:]
boxes=boxes.replace('A prescribed-family corner lemma\nand a uniform lower obstruction come first, followed by the thin-box\nupper bounds and the remaining shapes. The only certified input is\nTheorem~\\ref{thm:main}; the prescribed-family lemma is independent of it.',
 'The shared corner lemmas and Theorem~\\ref{thm:main} are now available.\nA uniform lower obstruction is followed by the thin-box upper bounds and\nthe remaining shapes. These deductions use no computational premise.')
(D/'shared-tools.tex').write_text(shared)
(D/'boxes.tex').write_text(boxes)
s=s[:start]+'\\input{elementary-corners}\n\n'+s[geoend:]
# Shared tools immediately follow the physical corner model.
pos=s.index('\\section{An elementary fourteen-cube obstruction}')
s=s[:pos]+'\\input{shared-tools}\n\n'+s[pos:]
s=s.replace('\\date{November 3, 2026}','\\date{November 4, 2026}')
s=s.replace('The proof combines a certified fifteen-cube corner theorem with elementary\nHall arguments and a uniform three-variety obstruction.',
 'The proof combines an elementary fifteen-cube corner theorem with Hall\narguments and a uniform three-variety obstruction. The corner proof uses\ndirected cuts, repeated-colour completions and geometric case analysis;\nits longer cases are proved in a companion mathematical appendix.')
s=s.replace('All threshold statements are formalised in Lean.',
 'The same threshold statements have a separate Lean verification, using\na certificate-based proof of the corner theorem.')
s=s.replace('We also determine the corner thresholds when the\nnumber of source varieties is bounded.',
 'A secondary result, using additional finite checks, determines corner\nthresholds when the number of source varieties is bounded.')
a=s.index('An elementary fourteen-cube obstruction proves the lower bound.')
b=s.index('\nThe side-length restriction',a)
s=s[:a]+'''An elementary fourteen-cube obstruction proves the lower bound.
For the upper bound, adjacent corner classes become directed cuts on five
colours, while opposite-repeat varieties become bidirected four-cycles.
Small matching constructions and repeated-colour arguments constrain a
hypothetical failure. Compression of disjoint cuts reduces the two-opposite
case to three geometric support families. Section~\\ref{sec:elementary}
combines these ingredients into a direct fifteen-source proof; all necessary
longer cases are included in the companion mathematical appendix, submitted
as part of the proof rather than as optional computational material.

Section~\\ref{sec:frames} establishes the shared geometry, including the
eight-plus-three missing-pair lemma independently of the corner theorem.
Section~\\ref{sec:boxes} extends the corner input to all cuboids. A uniform
three-variety obstruction explains the two sixteen-position exceptions.
Section~\\ref{sec:construction} gives a compressed flow algorithm, and
Section~\\ref{sec:support} treats bounded numbers of source varieties using
separate finite geometric checks. The elementary-proof claim concerns the
main threshold classification. Section~\\ref{sec:formal} distinguishes that
argument from the existing formal verification.
''' + s[b:]
a=s.index('\\section{Formal verification}');b=s.index('\\section*{AI disclosure',a)
s=s[:a]+r'''\section{Separate formal verification}\label{sec:formal}
The threshold statements have a Lean~4 and mathlib verification, both at
\texttt{v4.35.0}, using the physical model and palette-independent geometry
of \texttt{colour-cubes-core}~\cite{ColourCubes}. This verifies the same
conclusions through a different corner proof: physical cubes are connected
to catalogue matchings, a complete finite root cover, and checked exclusion
certificates. It does not formalise the new elementary derivation or every
lemma of the mathematical appendix. The cuboid deductions then apply the
verified corner theorem.

In namespace \path{FiveColour.Puzzle}, \path{Solution.lean} exports the
unconditional \path{box_frame_threshold} and \path{complete_box_threshold}.
They use the project's physical box definitions and proper-rotation bridges.
The separate Mathlib-only comparator challenge covers the corner problem;
a full external comparator pass remains unconfirmed. The construction
algorithm's complexity bound is a mathematical deduction, not a Lean claim.

The accompanying \emph{Certificate proof and verification supplement}
retains the alternative mathematical reduction, interval-checker soundness,
implementation details and reproduction commands. This supplement and the
repository explain the formal route; they are not premises of the elementary
proof. The command \texttt{make verify-full} replays the projected certificates,
builds the unconditional cuboid results and audits their dependencies. The
shorter \texttt{make check} does not reproduce the full theorem.

\section{Further structure and questions}
The main thresholds leave questions about the structure of extremal
obstructions. A separate computer-assisted classification identifies 11,430
failing fourteen-source inventories in three families. All have the invariant
\[
 3\sum_j\binom{g_j}{2}-4\binom{o}{2}=36,
\]
where $g_j$ counts copies in an adjacent class and $o$ is the total number
of opposite copies. This gives a different proof of the corner threshold
by single-copy deletion. Its new Lean replay is still in progress; these
classification claims are not included in the formal-verification statement
above or used in the elementary proof. An elementary classification of all
fourteen-source failures remains open, as does finding a substantially shorter
proof of the threshold. Boxes with a side of length one require a different
exposure model and are outside the classification proved here.

''' +s[b:]
s=s.replace('\\appendix\n\\input{verification}\n','')
# A visible review-draft marker prevents a staging document being mistaken for a release.
s=s.replace('\\maketitle','\\maketitle\n\\begin{center}\\small Editorial integration draft: companion mathematical appendix under consolidation.\\end{center}',1)
(D/'five-colour-cubes.tex').write_text(s)
# Preserve the alternative proof intact, with external references to article lemmas.
pre=s[:s.index('\\begin{document}')]
pre=re.sub(r'\\title\{[^\n]*\}',lambda m:r'\title{Certificate proof and verification supplement}',pre)
pre=pre.replace('\\usepackage[colorlinks', '\\usepackage{xr}\n\\externaldocument[main-]{five-colour-cubes}\n\\usepackage[colorlinks')
bib=s[s.index('\\begin{thebibliography}'):s.index('\\end{document}')]
verification=(SRC/'verification.tex').read_text().replace('\\section{Verification and reproduction details}', '\\section{Verification and reproduction details}')
cert=cert.replace('\\begin{proof}[Proof of Theorem~\\ref{thm:main}]','\\begin{proof}[Alternative proof of Theorem~\\ref{thm:main}]')
local_labels=set(re.findall(r'\\label\{([^}]+)\}',cert+verification))
def external_refs(text):
 return re.sub(r'\\(ref|eqref)\{([^}]+)\}',lambda m:'\\'+m[1]+'{'+('' if m[2] in local_labels else 'main-')+m[2]+'}',text)
cert=external_refs(cert);verification=external_refs(verification)
(D/'certificate-supplement.tex').write_text(pre+'\\begin{document}\n\\maketitle\n'+
 'This supplement preserves the computer-assisted corner proof used by the\nLean development. It is independent of the elementary corner argument in\nthe revised article and is not a formalisation of that argument.\n\n'+cert+verification+bib+'\\end{document}\n')
print('Article, early shared tools, boxes and alternative proof assembled.')
