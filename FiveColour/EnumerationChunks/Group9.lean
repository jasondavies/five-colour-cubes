module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case180
public import FiveColour.EnumerationChunks.Case181
public import FiveColour.EnumerationChunks.Case182
public import FiveColour.EnumerationChunks.Case183
public import FiveColour.EnumerationChunks.Case184
public import FiveColour.EnumerationChunks.Case185
public import FiveColour.EnumerationChunks.Case186
public import FiveColour.EnumerationChunks.Case187
public import FiveColour.EnumerationChunks.Case188
public import FiveColour.EnumerationChunks.Case189
public import FiveColour.EnumerationChunks.Case190
public import FiveColour.EnumerationChunks.Case191
public import FiveColour.EnumerationChunks.Case192
public import FiveColour.EnumerationChunks.Case193
public import FiveColour.EnumerationChunks.Case194
public import FiveColour.EnumerationChunks.Case195
public import FiveColour.EnumerationChunks.Case196
public import FiveColour.EnumerationChunks.Case197
public import FiveColour.EnumerationChunks.Case198
public import FiveColour.EnumerationChunks.Case199
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group9Roots : Fin 20 → Fin 357 := ![67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86]
def group9Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group9Covered : ∀ i, Enumeration.Covers (group9Points i) 14 (Enumeration.families (group9Roots i)) (Archive.root (group9Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 180 Case180.excludes
  · exact ClassificationProjected.covered 181 Case181.excludes
  · exact ClassificationProjected.covered 182 Case182.excludes
  · exact ClassificationProjected.covered 183 Case183.excludes
  · exact ClassificationProjected.covered 184 Case184.excludes
  · exact ClassificationProjected.covered 185 Case185.excludes
  · exact ClassificationProjected.covered 186 Case186.excludes
  · exact ClassificationProjected.covered 187 Case187.excludes
  · exact ClassificationProjected.covered 188 Case188.excludes
  · exact ClassificationProjected.covered 189 Case189.excludes
  · exact ClassificationProjected.covered 190 Case190.excludes
  · exact ClassificationProjected.covered 191 Case191.excludes
  · exact ClassificationProjected.covered 192 Case192.excludes
  · exact ClassificationProjected.covered 193 Case193.excludes
  · exact ClassificationProjected.covered 194 Case194.excludes
  · exact ClassificationProjected.covered 195 Case195.excludes
  · exact ClassificationProjected.covered 196 Case196.excludes
  · exact ClassificationProjected.covered 197 Case197.excludes
  · exact ClassificationProjected.covered 198 Case198.excludes
  · exact ClassificationProjected.covered 199 Case199.excludes
end FiveColour.Packed.EnumerationChunks
