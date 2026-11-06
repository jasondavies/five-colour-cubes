module
public import FiveColour.EnumerationChunks.Case80
public import FiveColour.EnumerationChunks.Case81
public import FiveColour.EnumerationChunks.Case82
public import FiveColour.EnumerationChunks.Case83
public import FiveColour.EnumerationChunks.Case84
public import FiveColour.EnumerationChunks.Case85
public import FiveColour.EnumerationChunks.Case86
public import FiveColour.EnumerationChunks.Case87
public import FiveColour.EnumerationChunks.Case88
public import FiveColour.EnumerationChunks.Case89
public import FiveColour.EnumerationChunks.Case90
public import FiveColour.EnumerationChunks.Case91
public import FiveColour.EnumerationChunks.Case92
public import FiveColour.EnumerationChunks.Case93
public import FiveColour.EnumerationChunks.Case94
public import FiveColour.EnumerationChunks.Case95
public import FiveColour.EnumerationChunks.Case96
public import FiveColour.EnumerationChunks.Case97
public import FiveColour.EnumerationChunks.Case98
public import FiveColour.EnumerationChunks.Case99
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group4Roots : Fin 20 → Fin 357 := ![324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343]
def group4Points : Fin 20 → List Nat := ![Case80.points,Case81.points,Case82.points,Case83.points,Case84.points,Case85.points,Case86.points,Case87.points,Case88.points,Case89.points,Case90.points,Case91.points,Case92.points,Case93.points,Case94.points,Case95.points,Case96.points,Case97.points,Case98.points,Case99.points]
theorem group4Covered : ∀ i, Enumeration.Covers (group4Points i) 14 (Enumeration.families (group4Roots i)) (Archive.root (group4Roots i)) := by
  intro i
  fin_cases i
  · exact Case80.covered
  · exact Case81.covered
  · exact Case82.covered
  · exact Case83.covered
  · exact Case84.covered
  · exact Case85.covered
  · exact Case86.covered
  · exact Case87.covered
  · exact Case88.covered
  · exact Case89.covered
  · exact Case90.covered
  · exact Case91.covered
  · exact Case92.covered
  · exact Case93.covered
  · exact Case94.covered
  · exact Case95.covered
  · exact Case96.covered
  · exact Case97.covered
  · exact Case98.covered
  · exact Case99.covered
end FiveColour.Packed.EnumerationChunks
