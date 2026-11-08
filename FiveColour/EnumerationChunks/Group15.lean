module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case300
public import FiveColour.EnumerationChunks.Case301
public import FiveColour.EnumerationChunks.Case302
public import FiveColour.EnumerationChunks.Case303
public import FiveColour.EnumerationChunks.Case304
public import FiveColour.EnumerationChunks.Case305
public import FiveColour.EnumerationChunks.Case306
public import FiveColour.EnumerationChunks.Case307
public import FiveColour.EnumerationChunks.Case308
public import FiveColour.EnumerationChunks.Case309
public import FiveColour.EnumerationChunks.Case310
public import FiveColour.EnumerationChunks.Case311
public import FiveColour.EnumerationChunks.Case312
public import FiveColour.EnumerationChunks.Case313
public import FiveColour.EnumerationChunks.Case314
public import FiveColour.EnumerationChunks.Case315
public import FiveColour.EnumerationChunks.Case316
public import FiveColour.EnumerationChunks.Case317
public import FiveColour.EnumerationChunks.Case318
public import FiveColour.EnumerationChunks.Case319
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group15Roots : Fin 20 → Fin 357 := ![187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206]
def group15Points : Fin 20 → List Nat := ![[],[],[],[],Case304.points,[],Case306.points,[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group15Covered : ∀ i, Enumeration.Covers (group15Points i) 14 (Enumeration.families (group15Roots i)) (Archive.root (group15Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 298 Case300.excludes
  · exact ClassificationProjected.covered 299 Case301.excludes
  · exact ClassificationProjected.covered 300 Case302.excludes
  · exact ClassificationProjected.covered 301 Case303.excludes
  · exact Case304.covered
  · exact ClassificationProjected.covered 302 Case305.excludes
  · exact Case306.covered
  · exact ClassificationProjected.covered 303 Case307.excludes
  · exact ClassificationProjected.covered 304 Case308.excludes
  · exact ClassificationProjected.covered 305 Case309.excludes
  · exact ClassificationProjected.covered 306 Case310.excludes
  · exact ClassificationProjected.covered 307 Case311.excludes
  · exact ClassificationProjected.covered 308 Case312.excludes
  · exact ClassificationProjected.covered 309 Case313.excludes
  · exact ClassificationProjected.covered 310 Case314.excludes
  · exact ClassificationProjected.covered 311 Case315.excludes
  · exact ClassificationProjected.covered 312 Case316.excludes
  · exact ClassificationProjected.covered 313 Case317.excludes
  · exact ClassificationProjected.covered 314 Case318.excludes
  · exact ClassificationProjected.covered 315 Case319.excludes
end FiveColour.Packed.EnumerationChunks
