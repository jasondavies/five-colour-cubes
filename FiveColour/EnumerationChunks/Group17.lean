module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group17Roots : Fin 9 → Fin 357 := ![227,228,229,230,231,232,233,234,235]
def group17Points : Fin 9 → List Nat := ![[],[],[],[],[],[],[],[],[]]
theorem group17Covered : ∀ i, Enumeration.Covers (group17Points i) 14 (Enumeration.families (group17Roots i)) (Archive.root (group17Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 320 Case340.excludes
  · exact ClassificationProjected.covered 321 Case341.excludes
  · exact ClassificationProjected.covered 322 Case342.excludes
  · exact ClassificationProjected.covered 323 Case343.excludes
  · exact ClassificationProjected.covered 324 Case344.excludes
  · exact ClassificationProjected.covered 325 Case345.excludes
  · exact ClassificationProjected.covered 326 Case346.excludes
  · exact ClassificationProjected.covered 327 Case347.excludes
  · exact ClassificationProjected.covered 328 Case348.excludes
end FiveColour.Packed.EnumerationChunks
