module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group3Roots : Fin 20 → Fin 357 := ![304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323]
def group3Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group3Covered : ∀ i, Enumeration.Covers (group3Points i) 14 (Enumeration.families (group3Roots i)) (Archive.root (group3Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 60 Case60.excludes
  · exact ClassificationProjected.covered 61 Case61.excludes
  · exact ClassificationProjected.covered 62 Case62.excludes
  · exact ClassificationProjected.covered 63 Case63.excludes
  · exact ClassificationProjected.covered 64 Case64.excludes
  · exact ClassificationProjected.covered 65 Case65.excludes
  · exact ClassificationProjected.covered 66 Case66.excludes
  · exact ClassificationProjected.covered 67 Case67.excludes
  · exact ClassificationProjected.covered 68 Case68.excludes
  · exact ClassificationProjected.covered 69 Case69.excludes
  · exact ClassificationProjected.covered 70 Case70.excludes
  · exact ClassificationProjected.covered 71 Case71.excludes
  · exact ClassificationProjected.covered 72 Case72.excludes
  · exact ClassificationProjected.covered 73 Case73.excludes
  · exact ClassificationProjected.covered 74 Case74.excludes
  · exact ClassificationProjected.covered 75 Case75.excludes
  · exact ClassificationProjected.covered 76 Case76.excludes
  · exact ClassificationProjected.covered 77 Case77.excludes
  · exact ClassificationProjected.covered 78 Case78.excludes
  · exact ClassificationProjected.covered 79 Case79.excludes
end FiveColour.Packed.EnumerationChunks
