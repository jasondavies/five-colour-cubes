module
public import FiveColour.ArchiveChecks
public import FiveColour.LowerBound
@[expose] public section
namespace FiveColour.Packed.Archive
open Physical

/-- All archived bounds satisfy the packed checker's digit and encoding invariants. -/
theorem root_valid (r : Fin 357) : (root r).Valid := by
  constructor
  · rw [(header_valid r).1]
    exact valid_encode _ (rootLower_le r)
  · rw [(header_valid r).2.1]
    exact valid_encode _ (rootUpper_le r)

/-- The concrete packed bounds decode to exactly the physically justified root box. -/
theorem root_model (r : Fin 357) : (root r).model = rootBox (rootCapacity r) := by
  have hl : vectorModel (root r).lower = (rootBox (rootCapacity r)).lower := by
    funext i
    change (values (root r).lower i : Int) = _
    rw [(header_valid r).1, encode_eq_pack, values_pack _ (rootLower_le r)]
    simp only [rootLower, Physical.rootBox]
    split_ifs <;> rfl
  have hu : vectorModel (root r).upper = (rootBox (rootCapacity r)).upper := by
    funext i
    change (values (root r).upper i : Int) = (rootUpper (rootCapacity r) i : Int)
    rw [(header_valid r).2.1, encode_eq_pack, values_pack _ (rootUpper_le r)]
  unfold Box.model
  rw [hl, hu]

lemma emptyCut_model : (⟨0, 0, 0⟩ : Cut).model = (⟨∅, 0⟩ : Certificate.Cut 75) := by
  simp [Cut.model, Cut.member]

lemma totalCut_model : (⟨2^75-1, allWeight, 15⟩ : Cut).model =
    (⟨Finset.univ, 15⟩ : Certificate.Cut 75) := by
  rfl

lemma budgetCut_model (r : Fin 357) : (budgetCut r).model =
    (⟨rootBad (rootCapacity r), (rootCapacity r).budget⟩ : Certificate.Cut 75) := by
  unfold Cut.model Cut.member
  rw [(header_valid r).2.2.1, (header_valid r).2.2.2]
  rfl

/-- Every constraint family, including the three header families, has the
integer meaning used by the complete physical case-reduction theorem. -/
theorem families_models (r : Fin 357) (t : Fin 78) :
    (families r t).map Cut.model = (rootProblem r).alternatives t := by
  dsimp only [families, rootProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, emptyCut_model]
  · simp only [List.map_cons, List.map_nil, totalCut_model]
  · simp only [List.map_cons, List.map_nil, budgetCut_model]
  · exact hallCuts_models ⟨t.val-3, by omega⟩

/-- The full packed case problem agrees with the integer problem, including its goal. -/
theorem problem_model (r : Fin 357) : Verified.problem 15 (families r) = rootProblem r := by
  have he : (fun t => (families r t).map Cut.model) = (rootProblem r).alternatives :=
    funext (families_models r)
  unfold Verified.problem
  rw [he]
  rfl

/-- Transfer a concrete archive exclusion into the integer case-cover interface. -/
theorem integer_exclusion (r : Fin 357) (h : Chunks.Excludes 15 (families r) (root r)) :
    ∀ x, (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x := by
  simpa only [Chunks.Excludes, root_model, problem_model] using h

/-- Only the 357 concrete archive exclusions remain as hypotheses. -/
theorem threshold_of_exclusions (h : ∀ r, Chunks.Excludes 15 (families r) (root r)) : Threshold15 :=
  threshold_of_integer_root_exclusions fun r => integer_exclusion r (h r)

/-- The lower bound is already proved; complete archive replay closes sharpness too. -/
theorem sharp_threshold_of_exclusions (h : ∀ r, Chunks.Excludes 15 (families r) (root r)) :
    SharpThreshold15 :=
  ⟨threshold_of_exclusions h, lower_bound.2⟩

end FiveColour.Packed.Archive
