module
public import FiveColour.EnumerationChunks.Case177.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case177
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All empty-root chunks prove exclusion. -/
theorem excludes : Chunks.Excludes 14 families root :=
  excludes_of_covered root (Archive.root_valid 64) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part660.covered
end FiveColour.Packed.EnumerationChunks.Case177
