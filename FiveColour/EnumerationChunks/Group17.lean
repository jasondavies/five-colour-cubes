module
public import FiveColour.EnumerationChunks.Case340
public import FiveColour.EnumerationChunks.Case341
public import FiveColour.EnumerationChunks.Case342
public import FiveColour.EnumerationChunks.Case343
public import FiveColour.EnumerationChunks.Case344
public import FiveColour.EnumerationChunks.Case345
public import FiveColour.EnumerationChunks.Case346
public import FiveColour.EnumerationChunks.Case347
public import FiveColour.EnumerationChunks.Case348
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
def group17Roots : Fin 9 → Fin 357 := ![227,228,229,230,231,232,233,234,235]
def group17Points : Fin 9 → List Nat := ![Case340.points,Case341.points,Case342.points,Case343.points,Case344.points,Case345.points,Case346.points,Case347.points,Case348.points]
theorem group17Covered : ∀ i, Enumeration.Covers (group17Points i) 14 (Enumeration.families (group17Roots i)) (Archive.root (group17Roots i)) := by
  intro i
  fin_cases i
  · exact Case340.covered
  · exact Case341.covered
  · exact Case342.covered
  · exact Case343.covered
  · exact Case344.covered
  · exact Case345.covered
  · exact Case346.covered
  · exact Case347.covered
  · exact Case348.covered
end FiveColour.Packed.EnumerationChunks
