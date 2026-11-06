module
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
def group6Roots : Fin 20 → Fin 357 := ![7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def group6Points : Fin 20 → List Nat := ![Case120.points,Case121.points,Case122.points,Case123.points,Case124.points,Case125.points,Case126.points,Case127.points,Case128.points,Case129.points,Case130.points,Case131.points,Case132.points,Case133.points,Case134.points,Case135.points,Case136.points,Case137.points,Case138.points,Case139.points]
theorem group6Covered : ∀ i, Enumeration.Covers (group6Points i) 14 (Enumeration.families (group6Roots i)) (Archive.root (group6Roots i)) := by
  intro i
  fin_cases i
  · exact Case120.covered
  · exact Case121.covered
  · exact Case122.covered
  · exact Case123.covered
  · exact Case124.covered
  · exact Case125.covered
  · exact Case126.covered
  · exact Case127.covered
  · exact Case128.covered
  · exact Case129.covered
  · exact Case130.covered
  · exact Case131.covered
  · exact Case132.covered
  · exact Case133.covered
  · exact Case134.covered
  · exact Case135.covered
  · exact Case136.covered
  · exact Case137.covered
  · exact Case138.covered
  · exact Case139.covered
end FiveColour.Packed.EnumerationChunks
