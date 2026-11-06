module
public import FiveColour.EnumerationChunks.Case240
public import FiveColour.EnumerationChunks.Case241
public import FiveColour.EnumerationChunks.Case242
public import FiveColour.EnumerationChunks.Case243
public import FiveColour.EnumerationChunks.Case244
public import FiveColour.EnumerationChunks.Case245
public import FiveColour.EnumerationChunks.Case246
public import FiveColour.EnumerationChunks.Case247
public import FiveColour.EnumerationChunks.Case248
public import FiveColour.EnumerationChunks.Case249
public import FiveColour.EnumerationChunks.Case250
public import FiveColour.EnumerationChunks.Case251
public import FiveColour.EnumerationChunks.Case252
public import FiveColour.EnumerationChunks.Case253
public import FiveColour.EnumerationChunks.Case254
public import FiveColour.EnumerationChunks.Case255
public import FiveColour.EnumerationChunks.Case256
public import FiveColour.EnumerationChunks.Case257
public import FiveColour.EnumerationChunks.Case258
public import FiveColour.EnumerationChunks.Case259
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group12Roots : Fin 20 → Fin 357 := ![127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146]
def group12Points : Fin 20 → List Nat := ![Case240.points,Case241.points,Case242.points,Case243.points,Case244.points,Case245.points,Case246.points,Case247.points,Case248.points,Case249.points,Case250.points,Case251.points,Case252.points,Case253.points,Case254.points,Case255.points,Case256.points,Case257.points,Case258.points,Case259.points]
theorem group12Covered : ∀ i, Enumeration.Covers (group12Points i) 14 (Enumeration.families (group12Roots i)) (Archive.root (group12Roots i)) := by
  intro i
  fin_cases i
  · exact Case240.covered
  · exact Case241.covered
  · exact Case242.covered
  · exact Case243.covered
  · exact Case244.covered
  · exact Case245.covered
  · exact Case246.covered
  · exact Case247.covered
  · exact Case248.covered
  · exact Case249.covered
  · exact Case250.covered
  · exact Case251.covered
  · exact Case252.covered
  · exact Case253.covered
  · exact Case254.covered
  · exact Case255.covered
  · exact Case256.covered
  · exact Case257.covered
  · exact Case258.covered
  · exact Case259.covered
end FiveColour.Packed.EnumerationChunks
