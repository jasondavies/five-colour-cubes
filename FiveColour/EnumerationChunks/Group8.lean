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
  · exact ClassificationProjected.covered 159 Case160.excludes
  · exact ClassificationProjected.covered 160 Case161.excludes
  · exact ClassificationProjected.covered 161 Case162.excludes
  · exact ClassificationProjected.covered 162 Case163.excludes
  · exact ClassificationProjected.covered 163 Case164.excludes
  · exact ClassificationProjected.covered 164 Case165.excludes
  · exact ClassificationProjected.covered 165 Case166.excludes
  · exact ClassificationProjected.covered 166 Case167.excludes
  · exact ClassificationProjected.covered 167 Case168.excludes
  · exact ClassificationProjected.covered 168 Case169.excludes
  · exact ClassificationProjected.covered 169 Case170.excludes
  · exact Case171.covered
  · exact Case172.covered
  · exact Case173.covered
  · exact Case174.covered
  · exact Case175.covered
  · exact Case176.covered
  · exact Case177.covered
  · exact Case178.covered
  · exact Case179.covered
end FiveColour.Packed.EnumerationChunks
