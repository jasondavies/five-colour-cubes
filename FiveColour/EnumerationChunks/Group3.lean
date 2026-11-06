module
public import FiveColour.EnumerationChunks.Case60
public import FiveColour.EnumerationChunks.Case61
public import FiveColour.EnumerationChunks.Case62
public import FiveColour.EnumerationChunks.Case63
public import FiveColour.EnumerationChunks.Case64
public import FiveColour.EnumerationChunks.Case65
public import FiveColour.EnumerationChunks.Case66
public import FiveColour.EnumerationChunks.Case67
public import FiveColour.EnumerationChunks.Case68
public import FiveColour.EnumerationChunks.Case69
public import FiveColour.EnumerationChunks.Case70
public import FiveColour.EnumerationChunks.Case71
public import FiveColour.EnumerationChunks.Case72
public import FiveColour.EnumerationChunks.Case73
public import FiveColour.EnumerationChunks.Case74
public import FiveColour.EnumerationChunks.Case75
public import FiveColour.EnumerationChunks.Case76
public import FiveColour.EnumerationChunks.Case77
public import FiveColour.EnumerationChunks.Case78
public import FiveColour.EnumerationChunks.Case79
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group3Roots : Fin 20 → Fin 357 := ![304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323]
def group3Points : Fin 20 → List Nat := ![Case60.points,Case61.points,Case62.points,Case63.points,Case64.points,Case65.points,Case66.points,Case67.points,Case68.points,Case69.points,Case70.points,Case71.points,Case72.points,Case73.points,Case74.points,Case75.points,Case76.points,Case77.points,Case78.points,Case79.points]
theorem group3Covered : ∀ i, Enumeration.Covers (group3Points i) 14 (Enumeration.families (group3Roots i)) (Archive.root (group3Roots i)) := by
  intro i
  fin_cases i
  · exact Case60.covered
  · exact Case61.covered
  · exact Case62.covered
  · exact Case63.covered
  · exact Case64.covered
  · exact Case65.covered
  · exact Case66.covered
  · exact Case67.covered
  · exact Case68.covered
  · exact Case69.covered
  · exact Case70.covered
  · exact Case71.covered
  · exact Case72.covered
  · exact Case73.covered
  · exact Case74.covered
  · exact Case75.covered
  · exact Case76.covered
  · exact Case77.covered
  · exact Case78.covered
  · exact Case79.covered
end FiveColour.Packed.EnumerationChunks
