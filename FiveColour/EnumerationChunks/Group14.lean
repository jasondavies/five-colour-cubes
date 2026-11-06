module
public import FiveColour.EnumerationChunks.Case280
public import FiveColour.EnumerationChunks.Case281
public import FiveColour.EnumerationChunks.Case282
public import FiveColour.EnumerationChunks.Case283
public import FiveColour.EnumerationChunks.Case284
public import FiveColour.EnumerationChunks.Case285
public import FiveColour.EnumerationChunks.Case286
public import FiveColour.EnumerationChunks.Case287
public import FiveColour.EnumerationChunks.Case288
public import FiveColour.EnumerationChunks.Case289
public import FiveColour.EnumerationChunks.Case290
public import FiveColour.EnumerationChunks.Case291
public import FiveColour.EnumerationChunks.Case292
public import FiveColour.EnumerationChunks.Case293
public import FiveColour.EnumerationChunks.Case294
public import FiveColour.EnumerationChunks.Case295
public import FiveColour.EnumerationChunks.Case296
public import FiveColour.EnumerationChunks.Case297
public import FiveColour.EnumerationChunks.Case298
public import FiveColour.EnumerationChunks.Case299
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group14Roots : Fin 20 → Fin 357 := ![167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186]
def group14Points : Fin 20 → List Nat := ![Case280.points,Case281.points,Case282.points,Case283.points,Case284.points,Case285.points,Case286.points,Case287.points,Case288.points,Case289.points,Case290.points,Case291.points,Case292.points,Case293.points,Case294.points,Case295.points,Case296.points,Case297.points,Case298.points,Case299.points]
theorem group14Covered : ∀ i, Enumeration.Covers (group14Points i) 14 (Enumeration.families (group14Roots i)) (Archive.root (group14Roots i)) := by
  intro i
  fin_cases i
  · exact Case280.covered
  · exact Case281.covered
  · exact Case282.covered
  · exact Case283.covered
  · exact Case284.covered
  · exact Case285.covered
  · exact Case286.covered
  · exact Case287.covered
  · exact Case288.covered
  · exact Case289.covered
  · exact Case290.covered
  · exact Case291.covered
  · exact Case292.covered
  · exact Case293.covered
  · exact Case294.covered
  · exact Case295.covered
  · exact Case296.covered
  · exact Case297.covered
  · exact Case298.covered
  · exact Case299.covered
end FiveColour.Packed.EnumerationChunks
