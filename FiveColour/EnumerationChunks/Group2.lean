module
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
def group2Roots : Fin 20 → Fin 357 := ![284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303]
def group2Points : Fin 20 → List Nat := ![Case40.points,Case41.points,Case42.points,Case43.points,Case44.points,Case45.points,Case46.points,Case47.points,Case48.points,Case49.points,Case50.points,Case51.points,Case52.points,Case53.points,Case54.points,Case55.points,Case56.points,Case57.points,Case58.points,Case59.points]
theorem group2Covered : ∀ i, Enumeration.Covers (group2Points i) 14 (Enumeration.families (group2Roots i)) (Archive.root (group2Roots i)) := by
  intro i
  fin_cases i
  · exact Case40.covered
  · exact Case41.covered
  · exact Case42.covered
  · exact Case43.covered
  · exact Case44.covered
  · exact Case45.covered
  · exact Case46.covered
  · exact Case47.covered
  · exact Case48.covered
  · exact Case49.covered
  · exact Case50.covered
  · exact Case51.covered
  · exact Case52.covered
  · exact Case53.covered
  · exact Case54.covered
  · exact Case55.covered
  · exact Case56.covered
  · exact Case57.covered
  · exact Case58.covered
  · exact Case59.covered
end FiveColour.Packed.EnumerationChunks
