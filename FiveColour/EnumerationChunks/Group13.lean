module
public import FiveColour.ClassificationProjection
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
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group13Roots : Fin 20 → Fin 357 := ![147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166]
def group13Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group13Covered : ∀ i, Enumeration.Covers (group13Points i) 14 (Enumeration.families (group13Roots i)) (Archive.root (group13Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 245 Case260.excludes
  · exact ClassificationProjected.covered 246 Case261.excludes
  · exact ClassificationProjected.covered 247 Case262.excludes
  · exact ClassificationProjected.covered 248 Case263.excludes
  · exact ClassificationProjected.covered 249 Case264.excludes
  · exact ClassificationProjected.covered 250 Case265.excludes
  · exact ClassificationProjected.covered 251 Case266.excludes
  · exact ClassificationProjected.covered 252 Case267.excludes
  · exact ClassificationProjected.covered 253 Case268.excludes
  · exact ClassificationProjected.covered 254 Case269.excludes
  · exact ClassificationProjected.covered 255 Case270.excludes
  · exact ClassificationProjected.covered 256 Case271.excludes
  · exact ClassificationProjected.covered 257 Case272.excludes
  · exact ClassificationProjected.covered 258 Case273.excludes
  · exact ClassificationProjected.covered 259 Case274.excludes
  · exact ClassificationProjected.covered 260 Case275.excludes
  · exact ClassificationProjected.covered 261 Case276.excludes
  · exact ClassificationProjected.covered 262 Case277.excludes
  · exact ClassificationProjected.covered 263 Case278.excludes
  · exact ClassificationProjected.covered 264 Case279.excludes
end FiveColour.Packed.EnumerationChunks
