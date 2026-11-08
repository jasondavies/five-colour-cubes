module
public import FiveColour.EnumerationChunks.Case171.Parts1
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case171
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All empty-root chunks prove exclusion. -/
theorem excludes : Chunks.Excludes 14 families root :=
  excludes_of_covered root (Archive.root_valid 58) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part872.covered
end FiveColour.Packed.EnumerationChunks.Case171
