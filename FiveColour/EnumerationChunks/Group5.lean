module
public import FiveColour.EnumerationChunks.Case100
public import FiveColour.EnumerationChunks.Case101
public import FiveColour.EnumerationChunks.Case102
public import FiveColour.EnumerationChunks.Case103
public import FiveColour.EnumerationChunks.Case104
public import FiveColour.EnumerationChunks.Case105
public import FiveColour.EnumerationChunks.Case106
public import FiveColour.EnumerationChunks.Case107
public import FiveColour.EnumerationChunks.Case108
public import FiveColour.EnumerationChunks.Case109
public import FiveColour.EnumerationChunks.Case110
public import FiveColour.EnumerationChunks.Case111
public import FiveColour.EnumerationChunks.Case112
public import FiveColour.EnumerationChunks.Case113
public import FiveColour.EnumerationChunks.Case114
public import FiveColour.EnumerationChunks.Case115
public import FiveColour.EnumerationChunks.Case116
public import FiveColour.EnumerationChunks.Case117
public import FiveColour.EnumerationChunks.Case118
public import FiveColour.EnumerationChunks.Case119
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group5Roots : Fin 20 → Fin 357 := ![344,345,346,347,348,349,350,351,352,353,354,355,356,0,1,2,3,4,5,6]
def group5Points : Fin 20 → List Nat := ![Case100.points,Case101.points,Case102.points,Case103.points,Case104.points,Case105.points,Case106.points,Case107.points,Case108.points,Case109.points,Case110.points,Case111.points,Case112.points,Case113.points,Case114.points,Case115.points,Case116.points,Case117.points,Case118.points,Case119.points]
theorem group5Covered : ∀ i, Enumeration.Covers (group5Points i) 14 (Enumeration.families (group5Roots i)) (Archive.root (group5Roots i)) := by
  intro i
  fin_cases i
  · exact Case100.covered
  · exact Case101.covered
  · exact Case102.covered
  · exact Case103.covered
  · exact Case104.covered
  · exact Case105.covered
  · exact Case106.covered
  · exact Case107.covered
  · exact Case108.covered
  · exact Case109.covered
  · exact Case110.covered
  · exact Case111.covered
  · exact Case112.covered
  · exact Case113.covered
  · exact Case114.covered
  · exact Case115.covered
  · exact Case116.covered
  · exact Case117.covered
  · exact Case118.covered
  · exact Case119.covered
end FiveColour.Packed.EnumerationChunks
