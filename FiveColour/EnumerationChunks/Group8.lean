module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case160
public import FiveColour.EnumerationChunks.Case161
public import FiveColour.EnumerationChunks.Case162
public import FiveColour.EnumerationChunks.Case163
public import FiveColour.EnumerationChunks.Case164
public import FiveColour.EnumerationChunks.Case165
public import FiveColour.EnumerationChunks.Case166
public import FiveColour.EnumerationChunks.Case167
public import FiveColour.EnumerationChunks.Case168
public import FiveColour.EnumerationChunks.Case169
public import FiveColour.EnumerationChunks.Case170
public import FiveColour.EnumerationChunks.Case171
public import FiveColour.EnumerationChunks.Case172
public import FiveColour.EnumerationChunks.Case173
public import FiveColour.EnumerationChunks.Case174
public import FiveColour.EnumerationChunks.Case175
public import FiveColour.EnumerationChunks.Case176
public import FiveColour.EnumerationChunks.Case177
public import FiveColour.EnumerationChunks.Case178
public import FiveColour.EnumerationChunks.Case179
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group8Roots : Fin 20 → Fin 357 := ![47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66]
def group8Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group8Covered : ∀ i, Enumeration.Covers (group8Points i) 14 (Enumeration.families (group8Roots i)) (Archive.root (group8Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 160 Case160.excludes
  · exact ClassificationProjected.covered 161 Case161.excludes
  · exact ClassificationProjected.covered 162 Case162.excludes
  · exact ClassificationProjected.covered 163 Case163.excludes
  · exact ClassificationProjected.covered 164 Case164.excludes
  · exact ClassificationProjected.covered 165 Case165.excludes
  · exact ClassificationProjected.covered 166 Case166.excludes
  · exact ClassificationProjected.covered 167 Case167.excludes
  · exact ClassificationProjected.covered 168 Case168.excludes
  · exact ClassificationProjected.covered 169 Case169.excludes
  · exact ClassificationProjected.covered 170 Case170.excludes
  · exact ClassificationProjected.covered 171 Case171.excludes
  · exact ClassificationProjected.covered 172 Case172.excludes
  · exact ClassificationProjected.covered 173 Case173.excludes
  · exact ClassificationProjected.covered 174 Case174.excludes
  · exact ClassificationProjected.covered 175 Case175.excludes
  · exact ClassificationProjected.covered 176 Case176.excludes
  · exact ClassificationProjected.covered 177 Case177.excludes
  · exact ClassificationProjected.covered 178 Case178.excludes
  · exact ClassificationProjected.covered 179 Case179.excludes
end FiveColour.Packed.EnumerationChunks
