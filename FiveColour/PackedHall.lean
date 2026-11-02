module
public import FiveColour.PackedHallChecks
@[expose] public section
namespace FiveColour.Packed

/-- The complete packed Hall table decodes to the physical/reference table,
including its order, all 255 neighbourhoods and every deficiency bound. -/
theorem hallCuts_models (t : Fin 75) :
    (cuts[t.val]!).toList.map Cut.model = Replay.hallCuts t := by
  calc
    (cuts[t.val]!).toList.map Cut.model = (actualSignatures t).map signatureModel := by
      simp only [actualSignatures, List.map_map]
      rfl
    _ = (expectedSignatures t).map signatureModel := congrArg _ (hall_signatures t)
    _ = Replay.hallCuts t := by
      simp only [expectedSignatures, List.map_map, Replay.hallCuts]
      apply List.map_congr_left
      intro d hd
      exact expectedSignature_model t (d+1) (by have := List.mem_range.mp hd; omega)

/-- The packed target constraints, before imposing any anchor-case constraints. -/
def targetProblem (n : Nat) : Certificate.Problem 75 75 where
  goal := n
  alternatives t := (cuts[t.val]!).toList.map Cut.model

lemma targetProblem_eq (n : Nat) : targetProblem n = Physical.hallProblem n := by
  have he : (fun t : Fin 75 => (cuts[t.val]!).toList.map Cut.model) = Replay.hallCuts :=
    funext hallCuts_models
  unfold targetProblem Physical.hallProblem
  rw [he]

end FiveColour.Packed

namespace FiveColour.Physical

/-- Exact physical meaning of the target constraints used by the packed checker. -/
theorem counterexample_iff_packed_admissible {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) :
    ¬ HasSolution cubes ↔ (Packed.targetProblem n).Admissible (multiplicityVector cubes) := by
  rw [Packed.targetProblem_eq]
  exact counterexample_iff_admissible cubes hc

/-- Packing the multiplicities of a counterexample preserves every coordinate. -/
theorem multiplicity_packed_model {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) :
    Packed.vectorModel (Packed.pack (multiplicity cubes)) = multiplicityVector cubes := by
  funext i
  simp only [Packed.vectorModel, Packed.values_pack _ (multiplicity_le_seven cubes hc h)]
  rfl

/-- Every physical counterexample supplies a valid packed vector satisfying
all target constraints. The remaining reduction is to the 357 anchor cases. -/
theorem counterexample_packed_vector {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) :
    Packed.ValidVector (Packed.pack (multiplicity cubes)) ∧
      (Packed.targetProblem n).Admissible (Packed.vectorModel (Packed.pack (multiplicity cubes))) := by
  refine ⟨Packed.valid_pack _ (multiplicity_le_seven cubes hc h), ?_⟩
  rw [multiplicity_packed_model cubes hc h]
  exact (counterexample_iff_packed_admissible cubes hc).mp h

end FiveColour.Physical
