module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group5Roots : Fin 20 → Fin 357 := ![344,345,346,347,348,349,350,351,352,353,354,355,356,0,1,2,3,4,5,6]
def group5Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group5Covered : ∀ i, Enumeration.Covers (group5Points i) 14 (Enumeration.families (group5Roots i)) (Archive.root (group5Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 99 Case100.excludes
  · exact ClassificationProjected.covered 100 Case101.excludes
  · exact ClassificationProjected.covered 101 Case102.excludes
  · exact ClassificationProjected.covered 102 Case103.excludes
  · exact ClassificationProjected.covered 103 Case104.excludes
  · exact ClassificationProjected.covered 104 Case105.excludes
  · exact ClassificationProjected.covered 105 Case106.excludes
  · exact ClassificationProjected.covered 106 Case107.excludes
  · exact ClassificationProjected.covered 107 Case108.excludes
  · exact ClassificationProjected.covered 108 Case109.excludes
  · exact ClassificationProjected.covered 109 Case110.excludes
  · exact ClassificationProjected.covered 110 Case111.excludes
  · exact ClassificationProjected.covered 111 Case112.excludes
  · exact ClassificationProjected.covered 112 Case113.excludes
  · exact ClassificationProjected.covered 113 Case114.excludes
  · exact ClassificationProjected.covered 114 Case115.excludes
  · exact ClassificationProjected.covered 115 Case116.excludes
  · exact ClassificationProjected.covered 116 Case117.excludes
  · exact ClassificationProjected.covered 117 Case118.excludes
  · exact ClassificationProjected.covered 118 Case119.excludes
end FiveColour.Packed.EnumerationChunks
