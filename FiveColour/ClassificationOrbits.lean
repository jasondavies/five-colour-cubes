module
public import FiveColour.ClassificationCore
public import FiveColour.ClassificationOrbitChecks
@[expose] public section
namespace FiveColour.Physical.Classification
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators

lemma indexed_apply {n : ℕ} (v : Fin n → Fin 75) (g : Fin 240) :
    SameInventory (fun i => (symmetry g).apply (catalogue (v i)))
      (fun i => catalogue (action g (v i))) := by
  intro a
  have ha (i : Fin 75) : varietyAction (symmetry g) i = action g i := action_eq g i
  simp only [multiplicity, catalogueIndex_apply _ _ (catalogue_uses_all_colours _),
    catalogue_index_faces, ha]

lemma terminal_equivalent (j : Fin 81) :
    SymmetryEquivalent (terminal j) (representative (terminalClass j)) := by
  refine ⟨symmetry (terminalSymmetry j), fun a => ?_⟩
  change multiplicity (fun i => (symmetry (terminalSymmetry j)).apply (catalogue (terminalVariety j i))) a =
    multiplicity (fun i => catalogue (representativeVariety (terminalClass j) i)) a
  rw [indexed_apply (terminalVariety j) (terminalSymmetry j) a]
  simp only [indexed_multiplicity]
  exact terminal_orbit_counts j a

/-- Equal inventories have equal base-sixteen weighted sums. Only this direction
is needed to distinguish orbits, so no uniqueness theorem for radix digits is assumed. -/
def inventoryCode {n : ℕ} (cubes : Fin n → Cube) : ℕ :=
  ∑ a : Fin 75, multiplicity cubes a * 16^a.val

lemma indexed_code {n : ℕ} (v : Fin n → Fin 75) :
    inventoryCode (fun i => catalogue (v i)) = indexCode v := by
  unfold inventoryCode
  simp only [indexed_multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [indexCode]

/-- The fifty-six representatives are pairwise inequivalent under the full
colour/reflection group, not only under the stabilizer of one anchor. -/
theorem representative_inequivalent (j k : Fin 56)
    (h : SymmetryEquivalent (representative j) (representative k)) : j = k := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨g,rfl⟩ := complete s
  have hi : SameInventory (fun i => catalogue (action g (representativeVariety j i)))
      (representative k) := fun a =>
    (indexed_apply (representativeVariety j) g a).symm.trans (hs a)
  have hc : indexCode (fun i => action g (representativeVariety j i)) =
      indexCode (representativeVariety k) := by
    rw [← indexed_code, ← indexed_code]
    unfold inventoryCode
    exact Finset.sum_congr rfl (fun a _ => congrArg (fun n => n * 16^a.val) (hi a))
  rw [orbit_code, representative_code] at hc
  exact orbit_separation j k g hc
end FiveColour.Physical.Classification
