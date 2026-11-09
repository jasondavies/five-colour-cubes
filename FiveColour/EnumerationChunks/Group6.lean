module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case120
public import FiveColour.EnumerationChunks.Case121
public import FiveColour.EnumerationChunks.Case122
public import FiveColour.EnumerationChunks.Case123
public import FiveColour.EnumerationChunks.Case124
public import FiveColour.EnumerationChunks.Case125
public import FiveColour.EnumerationChunks.Case126
public import FiveColour.EnumerationChunks.Case127
public import FiveColour.EnumerationChunks.Case128
public import FiveColour.EnumerationChunks.Case129
public import FiveColour.EnumerationChunks.Case130
public import FiveColour.EnumerationChunks.Case131
public import FiveColour.EnumerationChunks.Case132
public import FiveColour.EnumerationChunks.Case133
public import FiveColour.EnumerationChunks.Case134
public import FiveColour.EnumerationChunks.Case135
public import FiveColour.EnumerationChunks.Case136
public import FiveColour.EnumerationChunks.Case137
public import FiveColour.EnumerationChunks.Case138
public import FiveColour.EnumerationChunks.Case139
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group6Roots : Fin 20 → Fin 357 := ![7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def group6Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group6Covered : ∀ i, Enumeration.Covers (group6Points i) 14 (Enumeration.families (group6Roots i)) (Archive.root (group6Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 119 Case120.excludes
  · exact ClassificationProjected.covered 120 Case121.excludes
  · exact ClassificationProjected.covered 121 Case122.excludes
  · exact ClassificationProjected.covered 122 Case123.excludes
  · exact ClassificationProjected.covered 123 Case124.excludes
  · exact ClassificationProjected.covered 124 Case125.excludes
  · exact ClassificationProjected.covered 125 Case126.excludes
  · exact ClassificationProjected.covered 126 Case127.excludes
  · exact ClassificationProjected.covered 127 Case128.excludes
  · exact ClassificationProjected.covered 128 Case129.excludes
  · exact ClassificationProjected.covered 129 Case130.excludes
  · exact ClassificationProjected.covered 130 Case131.excludes
  · exact ClassificationProjected.covered 131 Case132.excludes
  · exact ClassificationProjected.covered 132 Case133.excludes
  · exact ClassificationProjected.covered 133 Case134.excludes
  · exact ClassificationProjected.covered 134 Case135.excludes
  · exact ClassificationProjected.covered 135 Case136.excludes
  · exact ClassificationProjected.covered 136 Case137.excludes
  · exact ClassificationProjected.covered 137 Case138.excludes
  · exact ClassificationProjected.covered 138 Case139.excludes
end FiveColour.Packed.EnumerationChunks
