module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group11Roots : Fin 20 → Fin 357 := ![107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126]
def group11Points : Fin 20 → List Nat := ![[],[],[],Case223.points,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group11Covered : ∀ i, Enumeration.Covers (group11Points i) 14 (Enumeration.families (group11Roots i)) (Archive.root (group11Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 219 Case220.excludes
  · exact ClassificationProjected.covered 220 Case221.excludes
  · exact ClassificationProjected.covered 221 Case222.excludes
  · exact Case223.covered
  · exact ClassificationProjected.covered 222 Case224.excludes
  · exact ClassificationProjected.covered 223 Case225.excludes
  · exact ClassificationProjected.covered 224 Case226.excludes
  · exact ClassificationProjected.covered 225 Case227.excludes
  · exact ClassificationProjected.covered 226 Case228.excludes
  · exact ClassificationProjected.covered 227 Case229.excludes
  · exact ClassificationProjected.covered 228 Case230.excludes
  · exact ClassificationProjected.covered 229 Case231.excludes
  · exact ClassificationProjected.covered 230 Case232.excludes
  · exact ClassificationProjected.covered 231 Case233.excludes
  · exact ClassificationProjected.covered 232 Case234.excludes
  · exact ClassificationProjected.covered 233 Case235.excludes
  · exact ClassificationProjected.covered 234 Case236.excludes
  · exact ClassificationProjected.covered 235 Case237.excludes
  · exact ClassificationProjected.covered 236 Case238.excludes
  · exact ClassificationProjected.covered 237 Case239.excludes
end FiveColour.Packed.EnumerationChunks
