module
public import FiveColour.EnumerationChunks.Case180
public import FiveColour.EnumerationChunks.Case181
public import FiveColour.EnumerationChunks.Case182
public import FiveColour.EnumerationChunks.Case183
public import FiveColour.EnumerationChunks.Case184
public import FiveColour.EnumerationChunks.Case185
public import FiveColour.EnumerationChunks.Case186
public import FiveColour.EnumerationChunks.Case187
public import FiveColour.EnumerationChunks.Case188
public import FiveColour.EnumerationChunks.Case189
public import FiveColour.EnumerationChunks.Case190
public import FiveColour.EnumerationChunks.Case191
public import FiveColour.EnumerationChunks.Case192
public import FiveColour.EnumerationChunks.Case193
public import FiveColour.EnumerationChunks.Case194
public import FiveColour.EnumerationChunks.Case195
public import FiveColour.EnumerationChunks.Case196
public import FiveColour.EnumerationChunks.Case197
public import FiveColour.EnumerationChunks.Case198
public import FiveColour.EnumerationChunks.Case199
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group9Roots : Fin 20 → Fin 357 := ![67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86]
def group9Points : Fin 20 → List Nat := ![Case180.points,Case181.points,Case182.points,Case183.points,Case184.points,Case185.points,Case186.points,Case187.points,Case188.points,Case189.points,Case190.points,Case191.points,Case192.points,Case193.points,Case194.points,Case195.points,Case196.points,Case197.points,Case198.points,Case199.points]
theorem group9Covered : ∀ i, Enumeration.Covers (group9Points i) 14 (Enumeration.families (group9Roots i)) (Archive.root (group9Roots i)) := by
  intro i
  fin_cases i
  · exact Case180.covered
  · exact Case181.covered
  · exact Case182.covered
  · exact Case183.covered
  · exact Case184.covered
  · exact Case185.covered
  · exact Case186.covered
  · exact Case187.covered
  · exact Case188.covered
  · exact Case189.covered
  · exact Case190.covered
  · exact Case191.covered
  · exact Case192.covered
  · exact Case193.covered
  · exact Case194.covered
  · exact Case195.covered
  · exact Case196.covered
  · exact Case197.covered
  · exact Case198.covered
  · exact Case199.covered
end FiveColour.Packed.EnumerationChunks
