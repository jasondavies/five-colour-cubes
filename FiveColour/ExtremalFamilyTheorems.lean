module
public import FiveColour.ExtremalFamilyData
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The generalized obstruction family allows five sources in each adjacent cut,
provided their repeated-colour supports are disjoint. -/
theorem generalized_no_solution (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 5) (hy : ∑ i, y i = 5) (hxy : disjointRepeats x y) :
    ¬ HasSolution (generalizedFamily x y) := by
  obtain ⟨i,rfl⟩ := distributions_complete x hx
  obtain ⟨j,rfl⟩ := distributions_complete y hy
  apply (not_hasSolution_iff_hall _).mpr
  intro t
  refine ⟨cornerSet (generalizedDeficit i j t), ?_⟩
  rw [← generalizedMaskNeighbours_eq _ _ _ _ (generalized_deficits i j hxy t).1]
  exact (generalized_deficits i j hxy t).2

lemma generalized_uses_all (x y : Fin 3 → ℕ) :
    ∀ i, UsesAllColours (generalizedFamily x y i) := fun _ => catalogue_uses_all_colours _

end FiveColour.Physical
