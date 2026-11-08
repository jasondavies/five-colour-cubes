module
public import FiveColour.ProjectedChecks
@[expose] public section
namespace FiveColour.Packed.Projected
open Physical

lemma upper_le (i : Fin 279) (j : Fin 75) :
    projectedUpper (caseNumbers i) (budgets i) j ≤ 7 := Projection.upper_le _ _ _

theorem root_valid (i : Fin 279) : (root i).Valid := Projection.root_valid (header_valid i)
theorem root_model (i : Fin 279) :
    (root i).model = projectedBox (caseNumbers i) (budgets i) := Projection.root_model (header_valid i)
lemma budgetCut_model (i : Fin 279) : (budgetCut i).model =
    (⟨rootBad (rootCapacity (caseNumbers i)), budgets i⟩ : Certificate.Cut 75) :=
  Projection.budgetCut_model (header_valid i)
theorem families_models (i : Fin 279) (t : Fin 78) :
    (families i t).map Cut.model = (projectedProblem (caseNumbers i) (budgets i) (goals i)).alternatives t :=
  Projection.families_models (header_valid i) t
theorem problem_model (i : Fin 279) : Verified.problem (goals i) (families i) =
    projectedProblem (caseNumbers i) (budgets i) (goals i) := Projection.problem_model (header_valid i)

/-- Compatibility wrapper for the fifteen-copy threshold route. -/
theorem original_exclusion (i : Fin 279)
    (h : Chunks.Excludes (goals i) (families i) (root i)) :
    ∀ x, (rootBox (rootCapacity (caseNumbers i))).Contains x →
      ¬ (rootProblem (caseNumbers i)).Admissible x :=
  Projection.original_exclusion (header_valid i) h

/-- The physical upper bound is conditional only on the 279 projected exclusions. -/
theorem threshold_of_exclusions
    (h : ∀ i, Chunks.Excludes (goals i) (families i) (root i)) : Threshold15 := by
  apply threshold_of_reduced_root_exclusions
  intro r hr
  obtain ⟨i, rfl⟩ := covers r hr
  exact original_exclusion i (h i)

theorem sharp_threshold_of_exclusions
    (h : ∀ i, Chunks.Excludes (goals i) (families i) (root i)) : SharpThreshold15 :=
  ⟨threshold_of_exclusions h, lower_bound.2⟩

end FiveColour.Packed.Projected
