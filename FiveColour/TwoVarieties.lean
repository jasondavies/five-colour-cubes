module
public import FiveColour.Multiplicity
@[expose] public section
namespace FiveColour.Physical

/-- Target positions that one source cube can supply. -/
def usableSlots (source target : Cube) : Finset (Fin 8) :=
  Finset.univ.filter fun k => Fits source target k

/-- The three conditions used by the two-variety capacity calculation. -/
def PairCriterion (i j t : Fin 75) (a : Nat) : Prop :=
  (∀ k, Fits (catalogue i) (catalogue t) k ∨ Fits (catalogue j) (catalogue t) k) ∧
    a ≤ (usableSlots (catalogue i) (catalogue t)).card ∧
    8-a ≤ (usableSlots (catalogue j) (catalogue t)).card

/-- All copies of a variety are neighbours as soon as it fits one selected corner. -/
lemma copy_fibre_subset_neighbours {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (i t : Fin 75) (K : Finset (Fin 8))
    (hi : ∃ k ∈ K, Fits (catalogue i) (catalogue t) k) :
    (Finset.univ.filter fun q => catalogueIndex (cubes q) = i) ⊆ neighbours cubes (catalogue t) K := by
  obtain ⟨k, hk, hfit⟩ := hi
  intro q hq
  have he := (Finset.mem_filter.mp hq).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, ?_⟩
  apply (fits_catalogueIndex _ (hc q) _ _).mpr
  simpa only [he] using hfit

lemma one_variety_neighbour_bound {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (i t : Fin 75) (K : Finset (Fin 8))
    (hi : ∃ k ∈ K, Fits (catalogue i) (catalogue t) k) :
    multiplicity cubes i ≤ (neighbours cubes (catalogue t) K).card :=
  Finset.card_le_card (copy_fibre_subset_neighbours cubes hc i t K hi)

lemma two_variety_neighbour_bound {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (i j t : Fin 75) (hij : i ≠ j)
    (K : Finset (Fin 8)) (hi : ∃ k ∈ K, Fits (catalogue i) (catalogue t) k)
    (hj : ∃ k ∈ K, Fits (catalogue j) (catalogue t) k) :
    multiplicity cubes i + multiplicity cubes j ≤ (neighbours cubes (catalogue t) K).card := by
  have hd : Disjoint (Finset.univ.filter fun q => catalogueIndex (cubes q) = i)
      (Finset.univ.filter fun q => catalogueIndex (cubes q) = j) := by
    apply Finset.disjoint_left.mpr
    intro q hqi hqj
    exact hij ((Finset.mem_filter.mp hqi).2.symm.trans (Finset.mem_filter.mp hqj).2)
  have hu := Finset.union_subset
    (copy_fibre_subset_neighbours cubes hc i t K hi)
    (copy_fibre_subset_neighbours cubes hc j t K hj)
  simpa only [Finset.card_union_of_disjoint hd, multiplicity] using Finset.card_le_card hu

/-- If a source fits no corner in K, K lies in the complement of its usable slots. -/
lemma card_le_unusable (source target : Cube) (K : Finset (Fin 8))
    (h : ¬ ∃ k ∈ K, Fits source target k) :
    K.card + (usableSlots source target).card ≤ 8 := by
  have hs : K ⊆ (usableSlots source target)ᶜ := by
    intro k hk
    simp only [Finset.mem_compl, usableSlots, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hf => h ⟨k, hk, hf⟩
  have hb := Finset.card_le_card hs
  have ht := Finset.card_compl_add_card (usableSlots source target)
  simp only [Fintype.card_fin] at ht
  omega

/-- The two-variety criterion supplies a physical solution even in a larger collection. -/
theorem two_varieties_suffice {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (i j t : Fin 75) (hij : i ≠ j)
    (a : Nat) (hcrit : PairCriterion i j t a)
    (hi : a ≤ multiplicity cubes i) (hj : 8-a ≤ multiplicity cubes j) :
    SolvesTarget cubes (catalogue t) := by
  obtain ⟨hcover, ha, hb⟩ := hcrit
  have ha8 : a ≤ 8 := ha.trans (by simpa using Finset.card_le_univ (usableSlots (catalogue i) (catalogue t)))
  apply (solvesTarget_iff_hall _ _).mpr
  intro K
  by_cases hAi : ∃ k ∈ K, Fits (catalogue i) (catalogue t) k
  · by_cases hBj : ∃ k ∈ K, Fits (catalogue j) (catalogue t) k
    · have hn := two_variety_neighbour_bound cubes hc i j t hij K hAi hBj
      have hk : K.card ≤ 8 := by simpa using Finset.card_le_univ K
      omega
    · have hk := card_le_unusable (catalogue j) (catalogue t) K hBj
      have hn := one_variety_neighbour_bound cubes hc i t K hAi
      omega
  · by_cases hBj : ∃ k ∈ K, Fits (catalogue j) (catalogue t) k
    · have hk := card_le_unusable (catalogue i) (catalogue t) K hAi
      have hn := one_variety_neighbour_bound cubes hc j t K hBj
      omega
    · have he : K = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        rcases hcover k with h | h
        · exact hAi ⟨k, hk, h⟩
        · exact hBj ⟨k, hk, h⟩
      simp [he]

/-- Contrapositive of the physical construction: the capacity used by the search. -/
theorem two_variety_capacity {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (i j t : Fin 75) (hij : i ≠ j) (a : Nat) (ha7 : a ≤ 7)
    (hcrit : PairCriterion i j t a) (hi : a ≤ multiplicity cubes i) :
    multiplicity cubes j ≤ 7-a := by
  by_contra hj
  have hs := two_varieties_suffice cubes hc i j t hij a hcrit hi (by omega)
  exact h ((hasSolution_iff_catalogue cubes).mpr ⟨t, hs⟩)

end FiveColour.Physical
