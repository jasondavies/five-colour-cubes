module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case0
public import FiveColour.EnumerationChunks.Case1
public import FiveColour.EnumerationChunks.Case2
public import FiveColour.EnumerationChunks.Case3
public import FiveColour.EnumerationChunks.Case4
public import FiveColour.EnumerationChunks.Case5
public import FiveColour.EnumerationChunks.Case6
public import FiveColour.EnumerationChunks.Case7
public import FiveColour.EnumerationChunks.Case8
public import FiveColour.EnumerationChunks.Case9
public import FiveColour.EnumerationChunks.Case10
public import FiveColour.EnumerationChunks.Case11
public import FiveColour.EnumerationChunks.Case12
public import FiveColour.EnumerationChunks.Case13
public import FiveColour.EnumerationChunks.Case14
public import FiveColour.EnumerationChunks.Case15
public import FiveColour.EnumerationChunks.Case16
public import FiveColour.EnumerationChunks.Case17
public import FiveColour.EnumerationChunks.Case18
public import FiveColour.EnumerationChunks.Case19
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group0Roots : Fin 20 → Fin 357 := ![244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263]
def group0Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group0Covered : ∀ i, Enumeration.Covers (group0Points i) 14 (Enumeration.families (group0Roots i)) (Archive.root (group0Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 0 Case0.excludes
  · exact ClassificationProjected.covered 1 Case1.excludes
  · exact ClassificationProjected.covered 2 Case2.excludes
  · exact ClassificationProjected.covered 3 Case3.excludes
  · exact ClassificationProjected.covered 4 Case4.excludes
  · exact ClassificationProjected.covered 5 Case5.excludes
  · exact ClassificationProjected.covered 6 Case6.excludes
  · exact ClassificationProjected.covered 7 Case7.excludes
  · exact ClassificationProjected.covered 8 Case8.excludes
  · exact ClassificationProjected.covered 9 Case9.excludes
  · exact ClassificationProjected.covered 10 Case10.excludes
  · exact ClassificationProjected.covered 11 Case11.excludes
  · exact ClassificationProjected.covered 12 Case12.excludes
  · exact ClassificationProjected.covered 13 Case13.excludes
  · exact ClassificationProjected.covered 14 Case14.excludes
  · exact ClassificationProjected.covered 15 Case15.excludes
  · exact ClassificationProjected.covered 16 Case16.excludes
  · exact ClassificationProjected.covered 17 Case17.excludes
  · exact ClassificationProjected.covered 18 Case18.excludes
  · exact ClassificationProjected.covered 19 Case19.excludes
end FiveColour.Packed.EnumerationChunks
