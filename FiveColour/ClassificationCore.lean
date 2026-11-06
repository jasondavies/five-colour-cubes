module
public import FiveColour.ClassificationChecks
@[expose] public section
namespace FiveColour.Physical.Classification
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators

def representative (j : Fin 56) : Fin 14 → Cube := fun i => catalogue (representativeVariety j i)
def terminal (j : Fin 81) : Fin 14 → Cube := fun i => catalogue (terminalVariety j i)
lemma representative_valid (j : Fin 56) : ∀ i, UsesAllColours (representative j i) :=
  fun _ => catalogue_uses_all_colours _
lemma terminal_valid (j : Fin 81) : ∀ i, UsesAllColours (terminal j i) :=
  fun _ => catalogue_uses_all_colours _

lemma indexed_multiplicity {n : ℕ} (v : Fin n → Fin 75) (a : Fin 75) :
    multiplicity (fun i => catalogue (v i)) a = (Finset.univ.filter (fun i => v i = a)).card := by
  simp only [multiplicity, catalogue_index_faces]

lemma terminal_model (j : Fin 81) :
    Packed.vectorModel (terminalPacked j) = multiplicityVector (terminal j) := by
  funext a
  change (Packed.values (terminalPacked j) a : Int) =
    (multiplicity (fun i => catalogue (terminalVariety j i)) a : Int)
  rw [indexed_multiplicity, terminal_counts]

/-- Each representative carries a Hall deficiency for every possible target. -/
theorem representative_fails (j : Fin 56) : ¬ HasSolution (representative j) := by
  apply (not_hasSolution_iff_hall _).mpr
  intro t
  refine ⟨cornerSet (hallDeficit j t), lt_of_le_of_lt (Finset.card_le_card ?_) (deficits j t).2⟩
  intro i hi
  obtain ⟨k,hk,hfit⟩ := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (mask_overlap_iff _ _ (deficits j t).1).mpr
    ⟨k, (Finset.mem_filter.mp hk).2, (incidence_fits _ _ _).mpr hfit⟩⟩
end FiveColour.Physical.Classification
