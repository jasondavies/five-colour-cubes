module
public import FiveColour.ProjectedChunks.All
public import FiveColour.ProjectedBridge
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem roots_match (i : Fin 279) : roots i = Projected.root i := by
  fin_cases i <;> rfl
theorem families_match (i : Fin 279) : families i = Projected.families i := by
  fin_cases i <;> funext t <;> rfl
theorem goals_match (i : Fin 279) : goals i = Projected.goals i := by
  fin_cases i <;> rfl

theorem archive_exclusions (i : Fin 279) :
    Chunks.Excludes (Projected.goals i) (Projected.families i) (Projected.root i) := by
  rw [← roots_match, ← families_match, ← goals_match]
  exact all_excluded i
end FiveColour.Packed.ProjectedChunks
