module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group4Roots : Fin 20 → Fin 357 := ![324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343]
def group4Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group4Covered : ∀ i, Enumeration.Covers (group4Points i) 14 (Enumeration.families (group4Roots i)) (Archive.root (group4Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 80 Case80.excludes
  · exact Case81.covered
  · exact ClassificationProjected.covered 81 Case82.excludes
  · exact ClassificationProjected.covered 82 Case83.excludes
  · exact ClassificationProjected.covered 83 Case84.excludes
  · exact ClassificationProjected.covered 84 Case85.excludes
  · exact ClassificationProjected.covered 85 Case86.excludes
  · exact ClassificationProjected.covered 86 Case87.excludes
  · exact ClassificationProjected.covered 87 Case88.excludes
  · exact ClassificationProjected.covered 88 Case89.excludes
  · exact ClassificationProjected.covered 89 Case90.excludes
  · exact ClassificationProjected.covered 90 Case91.excludes
  · exact ClassificationProjected.covered 91 Case92.excludes
  · exact ClassificationProjected.covered 92 Case93.excludes
  · exact ClassificationProjected.covered 93 Case94.excludes
  · exact ClassificationProjected.covered 94 Case95.excludes
  · exact ClassificationProjected.covered 95 Case96.excludes
  · exact ClassificationProjected.covered 96 Case97.excludes
  · exact ClassificationProjected.covered 97 Case98.excludes
  · exact ClassificationProjected.covered 98 Case99.excludes
end FiveColour.Packed.EnumerationChunks
