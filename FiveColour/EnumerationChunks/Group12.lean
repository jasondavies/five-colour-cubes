module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group12Roots : Fin 20 → Fin 357 := ![127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146]
def group12Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group12Covered : ∀ i, Enumeration.Covers (group12Points i) 14 (Enumeration.families (group12Roots i)) (Archive.root (group12Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 225 Case240.excludes
  · exact ClassificationProjected.covered 226 Case241.excludes
  · exact ClassificationProjected.covered 227 Case242.excludes
  · exact ClassificationProjected.covered 228 Case243.excludes
  · exact ClassificationProjected.covered 229 Case244.excludes
  · exact ClassificationProjected.covered 230 Case245.excludes
  · exact ClassificationProjected.covered 231 Case246.excludes
  · exact ClassificationProjected.covered 232 Case247.excludes
  · exact ClassificationProjected.covered 233 Case248.excludes
  · exact ClassificationProjected.covered 234 Case249.excludes
  · exact ClassificationProjected.covered 235 Case250.excludes
  · exact ClassificationProjected.covered 236 Case251.excludes
  · exact ClassificationProjected.covered 237 Case252.excludes
  · exact ClassificationProjected.covered 238 Case253.excludes
  · exact ClassificationProjected.covered 239 Case254.excludes
  · exact ClassificationProjected.covered 240 Case255.excludes
  · exact ClassificationProjected.covered 241 Case256.excludes
  · exact ClassificationProjected.covered 242 Case257.excludes
  · exact ClassificationProjected.covered 243 Case258.excludes
  · exact ClassificationProjected.covered 244 Case259.excludes
end FiveColour.Packed.EnumerationChunks
