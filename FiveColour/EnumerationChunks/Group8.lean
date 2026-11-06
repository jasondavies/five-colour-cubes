module
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
def group8Roots : Fin 20 → Fin 357 := ![47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66]
def group8Points : Fin 20 → List Nat := ![Case160.points,Case161.points,Case162.points,Case163.points,Case164.points,Case165.points,Case166.points,Case167.points,Case168.points,Case169.points,Case170.points,Case171.points,Case172.points,Case173.points,Case174.points,Case175.points,Case176.points,Case177.points,Case178.points,Case179.points]
theorem group8Covered : ∀ i, Enumeration.Covers (group8Points i) 14 (Enumeration.families (group8Roots i)) (Archive.root (group8Roots i)) := by
  intro i
  fin_cases i
  · exact Case160.covered
  · exact Case161.covered
  · exact Case162.covered
  · exact Case163.covered
  · exact Case164.covered
  · exact Case165.covered
  · exact Case166.covered
  · exact Case167.covered
  · exact Case168.covered
  · exact Case169.covered
  · exact Case170.covered
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
