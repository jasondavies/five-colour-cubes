module
public import FiveColour.EnumerationChunks.Case20
public import FiveColour.EnumerationChunks.Case21
public import FiveColour.EnumerationChunks.Case22
public import FiveColour.EnumerationChunks.Case23
public import FiveColour.EnumerationChunks.Case24
public import FiveColour.EnumerationChunks.Case25
public import FiveColour.EnumerationChunks.Case26
public import FiveColour.EnumerationChunks.Case27
public import FiveColour.EnumerationChunks.Case28
public import FiveColour.EnumerationChunks.Case29
public import FiveColour.EnumerationChunks.Case30
public import FiveColour.EnumerationChunks.Case31
public import FiveColour.EnumerationChunks.Case32
public import FiveColour.EnumerationChunks.Case33
public import FiveColour.EnumerationChunks.Case34
public import FiveColour.EnumerationChunks.Case35
public import FiveColour.EnumerationChunks.Case36
public import FiveColour.EnumerationChunks.Case37
public import FiveColour.EnumerationChunks.Case38
public import FiveColour.EnumerationChunks.Case39
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group1Roots : Fin 20 → Fin 357 := ![264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283]
def group1Points : Fin 20 → List Nat := ![Case20.points,Case21.points,Case22.points,Case23.points,Case24.points,Case25.points,Case26.points,Case27.points,Case28.points,Case29.points,Case30.points,Case31.points,Case32.points,Case33.points,Case34.points,Case35.points,Case36.points,Case37.points,Case38.points,Case39.points]
theorem group1Covered : ∀ i, Enumeration.Covers (group1Points i) 14 (Enumeration.families (group1Roots i)) (Archive.root (group1Roots i)) := by
  intro i
  fin_cases i
  · exact Case20.covered
  · exact Case21.covered
  · exact Case22.covered
  · exact Case23.covered
  · exact Case24.covered
  · exact Case25.covered
  · exact Case26.covered
  · exact Case27.covered
  · exact Case28.covered
  · exact Case29.covered
  · exact Case30.covered
  · exact Case31.covered
  · exact Case32.covered
  · exact Case33.covered
  · exact Case34.covered
  · exact Case35.covered
  · exact Case36.covered
  · exact Case37.covered
  · exact Case38.covered
  · exact Case39.covered
end FiveColour.Packed.EnumerationChunks
