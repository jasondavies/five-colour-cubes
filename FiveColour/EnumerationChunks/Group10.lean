module
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
def group10Roots : Fin 20 → Fin 357 := ![87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106]
def group10Points : Fin 20 → List Nat := ![Case200.points,Case201.points,Case202.points,Case203.points,Case204.points,Case205.points,Case206.points,Case207.points,Case208.points,Case209.points,Case210.points,Case211.points,Case212.points,Case213.points,Case214.points,Case215.points,Case216.points,Case217.points,Case218.points,Case219.points]
theorem group10Covered : ∀ i, Enumeration.Covers (group10Points i) 14 (Enumeration.families (group10Roots i)) (Archive.root (group10Roots i)) := by
  intro i
  fin_cases i
  · exact Case200.covered
  · exact Case201.covered
  · exact Case202.covered
  · exact Case203.covered
  · exact Case204.covered
  · exact Case205.covered
  · exact Case206.covered
  · exact Case207.covered
  · exact Case208.covered
  · exact Case209.covered
  · exact Case210.covered
  · exact Case211.covered
  · exact Case212.covered
  · exact Case213.covered
  · exact Case214.covered
  · exact Case215.covered
  · exact Case216.covered
  · exact Case217.covered
  · exact Case218.covered
  · exact Case219.covered
end FiveColour.Packed.EnumerationChunks
