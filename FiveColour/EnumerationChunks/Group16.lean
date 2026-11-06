module
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
def group16Roots : Fin 20 → Fin 357 := ![207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226]
def group16Points : Fin 20 → List Nat := ![Case320.points,Case321.points,Case322.points,Case323.points,Case324.points,Case325.points,Case326.points,Case327.points,Case328.points,Case329.points,Case330.points,Case331.points,Case332.points,Case333.points,Case334.points,Case335.points,Case336.points,Case337.points,Case338.points,Case339.points]
theorem group16Covered : ∀ i, Enumeration.Covers (group16Points i) 14 (Enumeration.families (group16Roots i)) (Archive.root (group16Roots i)) := by
  intro i
  fin_cases i
  · exact Case320.covered
  · exact Case321.covered
  · exact Case322.covered
  · exact Case323.covered
  · exact Case324.covered
  · exact Case325.covered
  · exact Case326.covered
  · exact Case327.covered
  · exact Case328.covered
  · exact Case329.covered
  · exact Case330.covered
  · exact Case331.covered
  · exact Case332.covered
  · exact Case333.covered
  · exact Case334.covered
  · exact Case335.covered
  · exact Case336.covered
  · exact Case337.covered
  · exact Case338.covered
  · exact Case339.covered
end FiveColour.Packed.EnumerationChunks
