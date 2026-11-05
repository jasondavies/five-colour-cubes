module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import FiveColour.Matching
public import FiveColour.PhysicalIncidence
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Replace any valid physical cube by its representative without changing compatibility. -/
theorem fits_catalogueIndex (c : Cube) (hc : UsesAllColours c) (t : Cube) (k : Fin 8) :
    Fits c t k ↔ Fits (catalogue (catalogueIndex c)) t k := by
  obtain ⟨i, r, hr⟩ := catalogue_complete c hc
  have hi : catalogueIndex c = i := by
    rw [funext hr]
    exact catalogue_index_rotations i r
  rw [hi]
  have he : c = rotate (catalogue i) r := funext hr
  conv_lhs => rw [he]
  exact fits_rotate_source _ _ _ _

/-- Count physical copies in each proper-rotation variety. -/
def multiplicity {n : Nat} (cubes : Fin n → Cube) (i : Fin 75) : Nat :=
  (Finset.univ.filter fun j => catalogueIndex (cubes j) = i).card

/-- The integer vector used by the certificate checker. -/
def multiplicityVector {n : Nat} (cubes : Fin n → Cube) : Certificate.Vector 75 :=
  fun i => multiplicity cubes i

/-- Summing multiplicities counts each physical copy exactly once. -/
theorem mass_multiplicity {n : Nat} (cubes : Fin n → Cube) (S : Finset (Fin 75)) :
    Certificate.mass (multiplicityVector cubes) S =
      ((Finset.univ.filter fun j => catalogueIndex (cubes j) ∈ S).card : Int) := by
  unfold Certificate.mass multiplicityVector multiplicity
  rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]

@[simp] theorem multiplicity_total {n : Nat} (cubes : Fin n → Cube) :
    Certificate.mass (multiplicityVector cubes) Finset.univ = n := by
  rw [mass_multiplicity]
  simp

theorem multiplicity_nonneg {n : Nat} (cubes : Fin n → Cube) (i : Fin 75) :
    0 ≤ multiplicityVector cubes i := Int.natCast_nonneg _

/-- Varieties that can supply some corner in K of the representative target. -/
def varietyNeighbours (t : Fin 75) (K : Finset (Fin 8)) : Finset (Fin 75) :=
  Finset.univ.filter fun i => ∃ k ∈ K, Fits (catalogue i) (catalogue t) k

/-- The physical Hall neighbourhood is exactly the sum of its variety multiplicities. -/
theorem mass_varietyNeighbours {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (t : Fin 75) (K : Finset (Fin 8)) :
    Certificate.mass (multiplicityVector cubes) (varietyNeighbours t K) =
      ((neighbours cubes (catalogue t) K).card : Int) := by
  rw [mass_multiplicity]
  congr 2
  ext j
  simp only [varietyNeighbours, neighbours, Finset.mem_filter, Finset.mem_univ, true_and,
    fits_catalogueIndex (cubes j) (hc j)]

/-- Exact correspondence between physical failure and integer Hall deficiencies. -/
theorem counterexample_iff_deficient_mass {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) :
    ¬ HasSolution cubes ↔ ∀ t : Fin 75, ∃ K : Finset (Fin 8), K.Nonempty ∧
      Certificate.mass (multiplicityVector cubes) (varietyNeighbours t K) ≤ (K.card : Int) - 1 := by
  rw [not_hasSolution_iff_hall]
  constructor
  · intro h t
    obtain ⟨K, hK⟩ := h t
    refine ⟨K, ?_, ?_⟩
    · by_contra he
      have : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp [this] at hK
    · rw [mass_varietyNeighbours cubes hc]
      omega
  · intro h t
    obtain ⟨K, _, hK⟩ := h t
    rw [mass_varietyNeighbours cubes hc] at hK
    exact ⟨K, by omega⟩

lemma fits_self (c : Cube) (k : Fin 8) : Fits c c k := by
  apply (fits_iff_corner _ _ _).mpr
  exact ⟨k, 0, by intro f; simp⟩

lemma multiplicity_le_neighbours {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (i : Fin 75)
    (K : Finset (Fin 8)) (hK : K.Nonempty) :
    multiplicity cubes i ≤ (neighbours cubes (catalogue i) K).card := by
  obtain ⟨k, hk⟩ := hK
  apply Finset.card_le_card
  intro j hj
  have hi := (Finset.mem_filter.mp hj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, k, hk, ?_⟩
  apply (fits_catalogueIndex _ (hc j) _ _).mpr
  rw [hi]
  exact fits_self _ _

/-- Eight copies of any one variety already solve that variety. -/
theorem solvesTarget_of_eight_copies {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (i : Fin 75) (hi : 8 ≤ multiplicity cubes i) :
    SolvesTarget cubes (catalogue i) := by
  apply (solvesTarget_iff_hall _ _).mpr
  intro K
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp
  · calc
      K.card ≤ 8 := by simpa using Finset.card_le_univ K
      _ ≤ multiplicity cubes i := hi
      _ ≤ (neighbours cubes (catalogue i) K).card := multiplicity_le_neighbours cubes hc i K hK

/-- Every physical counterexample lies in the checker's coordinate range 0,...,7. -/
theorem multiplicity_le_seven {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) (i : Fin 75) :
    multiplicity cubes i ≤ 7 := by
  by_contra hi
  apply h
  exact (hasSolution_iff_catalogue cubes).mpr
    ⟨i, solvesTarget_of_eight_copies cubes hc i (by omega)⟩

end FiveColour.Physical
