module
public import FiveColour.ExtremalLocalData
public import FiveColour.AnchorNormalisation
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

lemma six_group_anchor : ∀ (k : Fin 8) (i : Fin 75),
    sixGroup k i = some 0 ↔ i = 3 := by decide +kernel

lemma six_group_empty : ∀ i : Fin 75,
    sixGroup 0 i = none ↔ i ∈ anchorBad 3 ∅ := by decide +kernel

lemma six_group_single (k : Fin 8) : ∀ i : Fin 75,
    sixGroup k i = none ↔ i ∈ anchorBad 3 {k} := by
  fin_cases k <;> decide +kernel

lemma opposite_bad_empty : anchorBad 0 ∅ = Finset.univ.erase 0 := by decide +kernel
lemma opposite_bad_single (k : Fin 8) : anchorBad 0 {k} = Finset.univ.erase 0 := by
  fin_cases k <;> decide +kernel

def localPools {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :=
  sourcePools (fun i => sixGroup k (catalogueIndex (cubes i)))

lemma localPools_anchor {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    (localPools cubes k 0).card = multiplicity cubes 3 := by
  simp only [localPools, sourcePools, six_group_anchor, multiplicity]

lemma localPools_empty_total {n : ℕ} (cubes : Fin n → Cube) :
    (∑ g, ((localPools cubes 0) g).card : ℕ) +
      Certificate.mass (multiplicityVector cubes) (anchorBad 3 ∅) = (n : Int) := by
  rw [mass_multiplicity]
  have h := sourcePools_total (fun i => sixGroup 0 (catalogueIndex (cubes i)))
  simp only [six_group_empty] at h
  exact_mod_cast h

lemma localPools_single_total {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    (∑ g, ((localPools cubes k) g).card : ℕ) +
      Certificate.mass (multiplicityVector cubes) (anchorBad 3 {k}) = (n : Int) := by
  rw [mass_multiplicity]
  have h := sourcePools_total (fun i => sixGroup k (catalogueIndex (cubes i)))
  simp only [six_group_single k] at h
  exact_mod_cast h

end FiveColour.Physical
