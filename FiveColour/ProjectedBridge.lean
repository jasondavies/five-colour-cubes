module
public import FiveColour.ProjectedChecks
@[expose] public section
namespace FiveColour.Packed.Projected
open Physical

lemma upper_le (i : Fin 279) (j : Fin 75) :
    projectedUpper (caseNumbers i) (budgets i) j ≤ 7 := by
  unfold projectedUpper
  split
  · exact (min_le_left _ _).trans (Archive.rootUpper_le _ _)
  · exact Archive.rootUpper_le _ _

theorem root_valid (i : Fin 279) : (root i).Valid := by
  constructor
  · rw [(header_valid i).2.1]
    exact valid_encode _ (Archive.rootLower_le _)
  · rw [(header_valid i).2.2.1]
    exact valid_encode _ (upper_le i)

/-- Equality includes both lower and upper bounds, including the fixed anchor. -/
theorem root_model (i : Fin 279) :
    (root i).model = projectedBox (caseNumbers i) (budgets i) := by
  have hl : vectorModel (root i).lower = (projectedBox (caseNumbers i) (budgets i)).lower := by
    funext j
    change (values (root i).lower j : Int) = _
    rw [(header_valid i).2.1, encode_eq_pack, values_pack _ (Archive.rootLower_le _)]
    simp only [Archive.rootLower, projectedBox, Physical.rootBox]
    split_ifs <;> rfl
  have hu : vectorModel (root i).upper = (projectedBox (caseNumbers i) (budgets i)).upper := by
    funext j
    change (values (root i).upper j : Int) = (projectedUpper (caseNumbers i) (budgets i) j : Int)
    rw [(header_valid i).2.2.1, encode_eq_pack, values_pack _ (upper_le i)]
  unfold Box.model
  rw [hl, hu]

lemma budgetCut_model (i : Fin 279) : (budgetCut i).model =
    (⟨rootBad (rootCapacity (caseNumbers i)), budgets i⟩ : Certificate.Cut 75) := by
  unfold Cut.model Cut.member
  rw [(header_valid i).2.2.2.1, (header_valid i).2.2.2.2]
  rfl

/-- All 78 constraint families have their stated integer meaning. -/
theorem families_models (i : Fin 279) (t : Fin 78) :
    (families i t).map Cut.model = (projectedProblem (caseNumbers i) (budgets i) (goals i)).alternatives t := by
  dsimp only [families, projectedProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · have hn := congrArg Certificate.Cut.neighbours Archive.totalCut_model
    have hc : (⟨2^75-1, allWeight, goals i⟩ : Cut).model =
        (⟨Finset.univ, goals i⟩ : Certificate.Cut 75) :=
      congrArg (fun S => (⟨S, (goals i : Int)⟩ : Certificate.Cut 75)) hn
    simp only [List.map_cons, List.map_nil, hc]
  · simp only [List.map_cons, List.map_nil, budgetCut_model]
  · exact hallCuts_models ⟨t.val-3, by omega⟩

/-- Exact admissibility transport: total, budget and every Hall family. -/
theorem problem_model (i : Fin 279) : Verified.problem (goals i) (families i) =
    projectedProblem (caseNumbers i) (budgets i) (goals i) := by
  have he := funext (families_models i)
  unfold Verified.problem
  rw [he]
  rfl

/-- A projected certificate excludes the corresponding original fifteen-copy root. -/
theorem original_exclusion (i : Fin 279)
    (h : Chunks.Excludes (goals i) (families i) (root i)) :
    ∀ x, (rootBox (rootCapacity (caseNumbers i))).Contains x →
      ¬ (rootProblem (caseNumbers i)).Admissible x := by
  intro x hx hp
  obtain ⟨y, hy, hyp⟩ := root_projection _ _ _ (header_valid i).1 hx hp
  have he : ∀ y, (projectedBox (caseNumbers i) (budgets i)).Contains y →
      ¬ (projectedProblem (caseNumbers i) (budgets i) (goals i)).Admissible y := by
    simpa only [Chunks.Excludes, root_model, problem_model] using h
  exact he y hy hyp

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
