module
public import FiveColour.EnumerationChunks.Case260
public import FiveColour.EnumerationChunks.Case261
public import FiveColour.EnumerationChunks.Case262
public import FiveColour.EnumerationChunks.Case263
public import FiveColour.EnumerationChunks.Case264
public import FiveColour.EnumerationChunks.Case265
public import FiveColour.EnumerationChunks.Case266
public import FiveColour.EnumerationChunks.Case267
public import FiveColour.EnumerationChunks.Case268
public import FiveColour.EnumerationChunks.Case269
public import FiveColour.EnumerationChunks.Case270
public import FiveColour.EnumerationChunks.Case271
public import FiveColour.EnumerationChunks.Case272
public import FiveColour.EnumerationChunks.Case273
public import FiveColour.EnumerationChunks.Case274
public import FiveColour.EnumerationChunks.Case275
public import FiveColour.EnumerationChunks.Case276
public import FiveColour.EnumerationChunks.Case277
public import FiveColour.EnumerationChunks.Case278
public import FiveColour.EnumerationChunks.Case279
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group13Roots : Fin 20 → Fin 357 := ![147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166]
def group13Points : Fin 20 → List Nat := ![Case260.points,Case261.points,Case262.points,Case263.points,Case264.points,Case265.points,Case266.points,Case267.points,Case268.points,Case269.points,Case270.points,Case271.points,Case272.points,Case273.points,Case274.points,Case275.points,Case276.points,Case277.points,Case278.points,Case279.points]
theorem group13Covered : ∀ i, Enumeration.Covers (group13Points i) 14 (Enumeration.families (group13Roots i)) (Archive.root (group13Roots i)) := by
  intro i
  fin_cases i
  · exact Case260.covered
  · exact Case261.covered
  · exact Case262.covered
  · exact Case263.covered
  · exact Case264.covered
  · exact Case265.covered
  · exact Case266.covered
  · exact Case267.covered
  · exact Case268.covered
  · exact Case269.covered
  · exact Case270.covered
  · exact Case271.covered
  · exact Case272.covered
  · exact Case273.covered
  · exact Case274.covered
  · exact Case275.covered
  · exact Case276.covered
  · exact Case277.covered
  · exact Case278.covered
  · exact Case279.covered
end FiveColour.Packed.EnumerationChunks
