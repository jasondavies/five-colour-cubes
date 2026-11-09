module
public import FiveColour.EnumerationChunks.HeaderChecks
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.ClassificationProjected

/-- Both strict and identity projections exclude the original fourteen-copy root. -/
theorem covered (i : Fin 329)
    (h : Chunks.Excludes (goals i) (families i) (root i)) :
    Enumeration.Covers [] 14 (Enumeration.families (caseNumbers i)) (Archive.root (caseNumbers i)) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  exact False.elim (Projection.original_exclusion (header_valid i) h x hx hp)
end FiveColour.Packed.ClassificationProjected
