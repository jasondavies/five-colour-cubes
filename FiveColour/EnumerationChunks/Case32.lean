module
public import FiveColour.EnumerationChunks.Case32.Parts1
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case32
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid 276) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part782.covered
end FiveColour.Packed.EnumerationChunks.Case32
