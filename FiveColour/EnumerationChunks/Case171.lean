module
public import FiveColour.EnumerationChunks.Case171.Parts1
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case171
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid 58) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part872.covered
end FiveColour.Packed.EnumerationChunks.Case171
