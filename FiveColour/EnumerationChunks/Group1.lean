module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group1Roots : Fin 20 → Fin 357 := ![264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283]
def group1Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group1Covered : ∀ i, Enumeration.Covers (group1Points i) 14 (Enumeration.families (group1Roots i)) (Archive.root (group1Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 20 Case20.excludes
  · exact ClassificationProjected.covered 21 Case21.excludes
  · exact ClassificationProjected.covered 22 Case22.excludes
  · exact ClassificationProjected.covered 23 Case23.excludes
  · exact ClassificationProjected.covered 24 Case24.excludes
  · exact ClassificationProjected.covered 25 Case25.excludes
  · exact ClassificationProjected.covered 26 Case26.excludes
  · exact ClassificationProjected.covered 27 Case27.excludes
  · exact ClassificationProjected.covered 28 Case28.excludes
  · exact ClassificationProjected.covered 29 Case29.excludes
  · exact ClassificationProjected.covered 30 Case30.excludes
  · exact ClassificationProjected.covered 31 Case31.excludes
  · exact ClassificationProjected.covered 32 Case32.excludes
  · exact ClassificationProjected.covered 33 Case33.excludes
  · exact ClassificationProjected.covered 34 Case34.excludes
  · exact ClassificationProjected.covered 35 Case35.excludes
  · exact ClassificationProjected.covered 36 Case36.excludes
  · exact ClassificationProjected.covered 37 Case37.excludes
  · exact ClassificationProjected.covered 38 Case38.excludes
  · exact ClassificationProjected.covered 39 Case39.excludes
end FiveColour.Packed.EnumerationChunks
