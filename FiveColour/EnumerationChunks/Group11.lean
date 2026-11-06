module
public import FiveColour.EnumerationChunks.Case220
public import FiveColour.EnumerationChunks.Case221
public import FiveColour.EnumerationChunks.Case222
public import FiveColour.EnumerationChunks.Case223
public import FiveColour.EnumerationChunks.Case224
public import FiveColour.EnumerationChunks.Case225
public import FiveColour.EnumerationChunks.Case226
public import FiveColour.EnumerationChunks.Case227
public import FiveColour.EnumerationChunks.Case228
public import FiveColour.EnumerationChunks.Case229
public import FiveColour.EnumerationChunks.Case230
public import FiveColour.EnumerationChunks.Case231
public import FiveColour.EnumerationChunks.Case232
public import FiveColour.EnumerationChunks.Case233
public import FiveColour.EnumerationChunks.Case234
public import FiveColour.EnumerationChunks.Case235
public import FiveColour.EnumerationChunks.Case236
public import FiveColour.EnumerationChunks.Case237
public import FiveColour.EnumerationChunks.Case238
public import FiveColour.EnumerationChunks.Case239
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group11Roots : Fin 20 → Fin 357 := ![107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126]
def group11Points : Fin 20 → List Nat := ![Case220.points,Case221.points,Case222.points,Case223.points,Case224.points,Case225.points,Case226.points,Case227.points,Case228.points,Case229.points,Case230.points,Case231.points,Case232.points,Case233.points,Case234.points,Case235.points,Case236.points,Case237.points,Case238.points,Case239.points]
theorem group11Covered : ∀ i, Enumeration.Covers (group11Points i) 14 (Enumeration.families (group11Roots i)) (Archive.root (group11Roots i)) := by
  intro i
  fin_cases i
  · exact Case220.covered
  · exact Case221.covered
  · exact Case222.covered
  · exact Case223.covered
  · exact Case224.covered
  · exact Case225.covered
  · exact Case226.covered
  · exact Case227.covered
  · exact Case228.covered
  · exact Case229.covered
  · exact Case230.covered
  · exact Case231.covered
  · exact Case232.covered
  · exact Case233.covered
  · exact Case234.covered
  · exact Case235.covered
  · exact Case236.covered
  · exact Case237.covered
  · exact Case238.covered
  · exact Case239.covered
end FiveColour.Packed.EnumerationChunks
