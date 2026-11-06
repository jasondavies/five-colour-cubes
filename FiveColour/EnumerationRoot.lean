module
public import FiveColour.ArchiveBridge
public import FiveColour.PackedEnumeration
public import FiveColour.PackedCalibration
@[expose] public section
namespace FiveColour.Packed.Enumeration
open Physical

/-- The existing roots with the total changed to fourteen. -/
def families (r : Fin 357) (t : Fin 78) : List Cut :=
  if t.val = 0 then [⟨0, 0, 0⟩]
  else if t.val = 1 then [⟨2^75-1, allWeight, 14⟩]
  else if t.val = 2 then [Archive.budgetCut r]
  else (cuts[t.val-3]!).toList

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budget_weights : ∀ r : Fin 357,
    (Archive.budgetCut r).weight = maskWeight (Archive.budgetCut r).member := by
  decide +kernel

theorem families_valid (r : Fin 357) : ∀ t, ∀ c ∈ families r t, c.Valid := by
  intro t c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        exact cut_valid_of_weight _ (budget_weights r)
      · exact cuts_valid ⟨t.val-3, by omega⟩ c hc

theorem families_models (r : Fin 357) (t : Fin 78) :
    (families r t).map Cut.model =
      (caseProblem r (rootCapacity r).budget 14).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · simp only [List.map_cons, List.map_nil, Archive.totalCut_model]
  · simp only [List.map_cons, List.map_nil, Archive.budgetCut_model]
  · exact hallCuts_models ⟨t.val-3, by omega⟩

theorem problem_model (r : Fin 357) : Verified.problem 14 (families r) =
    caseProblem r (rootCapacity r).budget 14 := by
  have h := funext (families_models r)
  unfold Verified.problem
  rw [h]
  rfl
end FiveColour.Packed.Enumeration
