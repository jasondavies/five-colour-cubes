module
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
def group0Roots : Fin 20 → Fin 357 := ![244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263]
def group0Points : Fin 20 → List Nat := ![Case0.points,Case1.points,Case2.points,Case3.points,Case4.points,Case5.points,Case6.points,Case7.points,Case8.points,Case9.points,Case10.points,Case11.points,Case12.points,Case13.points,Case14.points,Case15.points,Case16.points,Case17.points,Case18.points,Case19.points]
theorem group0Covered : ∀ i, Enumeration.Covers (group0Points i) 14 (Enumeration.families (group0Roots i)) (Archive.root (group0Roots i)) := by
  intro i
  fin_cases i
  · exact Case0.covered
  · exact Case1.covered
  · exact Case2.covered
  · exact Case3.covered
  · exact Case4.covered
  · exact Case5.covered
  · exact Case6.covered
  · exact Case7.covered
  · exact Case8.covered
  · exact Case9.covered
  · exact Case10.covered
  · exact Case11.covered
  · exact Case12.covered
  · exact Case13.covered
  · exact Case14.covered
  · exact Case15.covered
  · exact Case16.covered
  · exact Case17.covered
  · exact Case18.covered
  · exact Case19.covered
end FiveColour.Packed.EnumerationChunks
