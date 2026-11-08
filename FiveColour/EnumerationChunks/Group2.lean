module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case40
public import FiveColour.EnumerationChunks.Case41
public import FiveColour.EnumerationChunks.Case42
public import FiveColour.EnumerationChunks.Case43
public import FiveColour.EnumerationChunks.Case44
public import FiveColour.EnumerationChunks.Case45
public import FiveColour.EnumerationChunks.Case46
public import FiveColour.EnumerationChunks.Case47
public import FiveColour.EnumerationChunks.Case48
public import FiveColour.EnumerationChunks.Case49
public import FiveColour.EnumerationChunks.Case50
public import FiveColour.EnumerationChunks.Case51
public import FiveColour.EnumerationChunks.Case52
public import FiveColour.EnumerationChunks.Case53
public import FiveColour.EnumerationChunks.Case54
public import FiveColour.EnumerationChunks.Case55
public import FiveColour.EnumerationChunks.Case56
public import FiveColour.EnumerationChunks.Case57
public import FiveColour.EnumerationChunks.Case58
public import FiveColour.EnumerationChunks.Case59
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group2Roots : Fin 20 → Fin 357 := ![284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303]
def group2Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group2Covered : ∀ i, Enumeration.Covers (group2Points i) 14 (Enumeration.families (group2Roots i)) (Archive.root (group2Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 40 Case40.excludes
  · exact ClassificationProjected.covered 41 Case41.excludes
  · exact ClassificationProjected.covered 42 Case42.excludes
  · exact ClassificationProjected.covered 43 Case43.excludes
  · exact ClassificationProjected.covered 44 Case44.excludes
  · exact ClassificationProjected.covered 45 Case45.excludes
  · exact ClassificationProjected.covered 46 Case46.excludes
  · exact ClassificationProjected.covered 47 Case47.excludes
  · exact ClassificationProjected.covered 48 Case48.excludes
  · exact ClassificationProjected.covered 49 Case49.excludes
  · exact ClassificationProjected.covered 50 Case50.excludes
  · exact ClassificationProjected.covered 51 Case51.excludes
  · exact ClassificationProjected.covered 52 Case52.excludes
  · exact ClassificationProjected.covered 53 Case53.excludes
  · exact ClassificationProjected.covered 54 Case54.excludes
  · exact ClassificationProjected.covered 55 Case55.excludes
  · exact ClassificationProjected.covered 56 Case56.excludes
  · exact ClassificationProjected.covered 57 Case57.excludes
  · exact ClassificationProjected.covered 58 Case58.excludes
  · exact ClassificationProjected.covered 59 Case59.excludes
end FiveColour.Packed.EnumerationChunks
