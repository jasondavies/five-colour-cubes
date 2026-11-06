module
public import FiveColour.EnumerationChunks.Case300
public import FiveColour.EnumerationChunks.Case301
public import FiveColour.EnumerationChunks.Case302
public import FiveColour.EnumerationChunks.Case303
public import FiveColour.EnumerationChunks.Case304
public import FiveColour.EnumerationChunks.Case305
public import FiveColour.EnumerationChunks.Case306
public import FiveColour.EnumerationChunks.Case307
public import FiveColour.EnumerationChunks.Case308
public import FiveColour.EnumerationChunks.Case309
public import FiveColour.EnumerationChunks.Case310
public import FiveColour.EnumerationChunks.Case311
public import FiveColour.EnumerationChunks.Case312
public import FiveColour.EnumerationChunks.Case313
public import FiveColour.EnumerationChunks.Case314
public import FiveColour.EnumerationChunks.Case315
public import FiveColour.EnumerationChunks.Case316
public import FiveColour.EnumerationChunks.Case317
public import FiveColour.EnumerationChunks.Case318
public import FiveColour.EnumerationChunks.Case319
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group15Roots : Fin 20 → Fin 357 := ![187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206]
def group15Points : Fin 20 → List Nat := ![Case300.points,Case301.points,Case302.points,Case303.points,Case304.points,Case305.points,Case306.points,Case307.points,Case308.points,Case309.points,Case310.points,Case311.points,Case312.points,Case313.points,Case314.points,Case315.points,Case316.points,Case317.points,Case318.points,Case319.points]
theorem group15Covered : ∀ i, Enumeration.Covers (group15Points i) 14 (Enumeration.families (group15Roots i)) (Archive.root (group15Roots i)) := by
  intro i
  fin_cases i
  · exact Case300.covered
  · exact Case301.covered
  · exact Case302.covered
  · exact Case303.covered
  · exact Case304.covered
  · exact Case305.covered
  · exact Case306.covered
  · exact Case307.covered
  · exact Case308.covered
  · exact Case309.covered
  · exact Case310.covered
  · exact Case311.covered
  · exact Case312.covered
  · exact Case313.covered
  · exact Case314.covered
  · exact Case315.covered
  · exact Case316.covered
  · exact Case317.covered
  · exact Case318.covered
  · exact Case319.covered
end FiveColour.Packed.EnumerationChunks
