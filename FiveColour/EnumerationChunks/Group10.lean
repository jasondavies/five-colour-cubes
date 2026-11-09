module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case200
public import FiveColour.EnumerationChunks.Case201
public import FiveColour.EnumerationChunks.Case202
public import FiveColour.EnumerationChunks.Case203
public import FiveColour.EnumerationChunks.Case204
public import FiveColour.EnumerationChunks.Case205
public import FiveColour.EnumerationChunks.Case206
public import FiveColour.EnumerationChunks.Case207
public import FiveColour.EnumerationChunks.Case208
public import FiveColour.EnumerationChunks.Case209
public import FiveColour.EnumerationChunks.Case210
public import FiveColour.EnumerationChunks.Case211
public import FiveColour.EnumerationChunks.Case212
public import FiveColour.EnumerationChunks.Case213
public import FiveColour.EnumerationChunks.Case214
public import FiveColour.EnumerationChunks.Case215
public import FiveColour.EnumerationChunks.Case216
public import FiveColour.EnumerationChunks.Case217
public import FiveColour.EnumerationChunks.Case218
public import FiveColour.EnumerationChunks.Case219
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group10Roots : Fin 20 → Fin 357 := ![87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106]
def group10Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],Case213.points,[],[],[],[],[],[]]
theorem group10Covered : ∀ i, Enumeration.Covers (group10Points i) 14 (Enumeration.families (group10Roots i)) (Archive.root (group10Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 187 Case200.excludes
  · exact ClassificationProjected.covered 188 Case201.excludes
  · exact ClassificationProjected.covered 189 Case202.excludes
  · exact ClassificationProjected.covered 190 Case203.excludes
  · exact ClassificationProjected.covered 191 Case204.excludes
  · exact ClassificationProjected.covered 192 Case205.excludes
  · exact ClassificationProjected.covered 193 Case206.excludes
  · exact ClassificationProjected.covered 194 Case207.excludes
  · exact ClassificationProjected.covered 195 Case208.excludes
  · exact ClassificationProjected.covered 196 Case209.excludes
  · exact ClassificationProjected.covered 197 Case210.excludes
  · exact ClassificationProjected.covered 198 Case211.excludes
  · exact ClassificationProjected.covered 199 Case212.excludes
  · exact Case213.covered
  · exact ClassificationProjected.covered 200 Case214.excludes
  · exact ClassificationProjected.covered 201 Case215.excludes
  · exact ClassificationProjected.covered 202 Case216.excludes
  · exact ClassificationProjected.covered 203 Case217.excludes
  · exact ClassificationProjected.covered 204 Case218.excludes
  · exact ClassificationProjected.covered 205 Case219.excludes
end FiveColour.Packed.EnumerationChunks
