module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group14Roots : Fin 20 → Fin 357 := ![167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186]
def group14Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group14Covered : ∀ i, Enumeration.Covers (group14Points i) 14 (Enumeration.families (group14Roots i)) (Archive.root (group14Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 278 Case280.excludes
  · exact ClassificationProjected.covered 279 Case281.excludes
  · exact ClassificationProjected.covered 280 Case282.excludes
  · exact ClassificationProjected.covered 281 Case283.excludes
  · exact ClassificationProjected.covered 282 Case284.excludes
  · exact ClassificationProjected.covered 283 Case285.excludes
  · exact ClassificationProjected.covered 284 Case286.excludes
  · exact ClassificationProjected.covered 285 Case287.excludes
  · exact ClassificationProjected.covered 286 Case288.excludes
  · exact ClassificationProjected.covered 287 Case289.excludes
  · exact ClassificationProjected.covered 288 Case290.excludes
  · exact ClassificationProjected.covered 289 Case291.excludes
  · exact ClassificationProjected.covered 290 Case292.excludes
  · exact ClassificationProjected.covered 291 Case293.excludes
  · exact ClassificationProjected.covered 292 Case294.excludes
  · exact ClassificationProjected.covered 293 Case295.excludes
  · exact ClassificationProjected.covered 294 Case296.excludes
  · exact ClassificationProjected.covered 295 Case297.excludes
  · exact ClassificationProjected.covered 296 Case298.excludes
  · exact ClassificationProjected.covered 297 Case299.excludes
end FiveColour.Packed.EnumerationChunks
