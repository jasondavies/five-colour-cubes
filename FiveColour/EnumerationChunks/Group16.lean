module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case320
public import FiveColour.EnumerationChunks.Case321
public import FiveColour.EnumerationChunks.Case322
public import FiveColour.EnumerationChunks.Case323
public import FiveColour.EnumerationChunks.Case324
public import FiveColour.EnumerationChunks.Case325
public import FiveColour.EnumerationChunks.Case326
public import FiveColour.EnumerationChunks.Case327
public import FiveColour.EnumerationChunks.Case328
public import FiveColour.EnumerationChunks.Case329
public import FiveColour.EnumerationChunks.Case330
public import FiveColour.EnumerationChunks.Case331
public import FiveColour.EnumerationChunks.Case332
public import FiveColour.EnumerationChunks.Case333
public import FiveColour.EnumerationChunks.Case334
public import FiveColour.EnumerationChunks.Case335
public import FiveColour.EnumerationChunks.Case336
public import FiveColour.EnumerationChunks.Case337
public import FiveColour.EnumerationChunks.Case338
public import FiveColour.EnumerationChunks.Case339
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group16Roots : Fin 20 → Fin 357 := ![207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226]
def group16Points : Fin 20 → List Nat := ![Case320.points,[],[],[],[],[],[],[],[],Case329.points,[],Case331.points,[],[],[],[],[],[],[],[]]
theorem group16Covered : ∀ i, Enumeration.Covers (group16Points i) 14 (Enumeration.families (group16Roots i)) (Archive.root (group16Roots i)) := by
  intro i
  fin_cases i
  · exact Case320.covered
  · exact ClassificationProjected.covered 316 Case321.excludes
  · exact ClassificationProjected.covered 317 Case322.excludes
  · exact ClassificationProjected.covered 318 Case323.excludes
  · exact ClassificationProjected.covered 319 Case324.excludes
  · exact ClassificationProjected.covered 320 Case325.excludes
  · exact ClassificationProjected.covered 321 Case326.excludes
  · exact ClassificationProjected.covered 322 Case327.excludes
  · exact ClassificationProjected.covered 323 Case328.excludes
  · exact Case329.covered
  · exact ClassificationProjected.covered 324 Case330.excludes
  · exact Case331.covered
  · exact ClassificationProjected.covered 325 Case332.excludes
  · exact ClassificationProjected.covered 326 Case333.excludes
  · exact ClassificationProjected.covered 327 Case334.excludes
  · exact ClassificationProjected.covered 328 Case335.excludes
  · exact ClassificationProjected.covered 329 Case336.excludes
  · exact ClassificationProjected.covered 330 Case337.excludes
  · exact ClassificationProjected.covered 331 Case338.excludes
  · exact ClassificationProjected.covered 332 Case339.excludes
end FiveColour.Packed.EnumerationChunks
