module
public import FiveColour.Multiplicity
@[expose] public section
namespace FiveColour.Physical

/-- Non-anchor varieties that supply a corner outside K of the anchor target. -/
def anchorBad (a : Fin 75) (K : Finset (Fin 8)) : Finset (Fin 75) :=
  (varietyNeighbours a Kᶜ).erase a

/-- The root budget follows from a Hall deficiency for the anchor target.
This holds for every chosen anchor, before symmetry or capacity reductions. -/
theorem anchor_cover {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) (a : Fin 75) :
    ∃ K : Finset (Fin 8), K.card + multiplicity cubes a ≤ 7 ∧
      Certificate.mass (multiplicityVector cubes) (anchorBad a K) ≤
        (7 : Int) - multiplicity cubes a - K.card := by
  obtain ⟨D, hD, hcut⟩ := (counterexample_iff_deficient_mass cubes hc).mp h a
  have ha : a ∈ varietyNeighbours a D := by
    obtain ⟨k, hk⟩ := hD
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, fits_self _ _⟩
  have hsum : Certificate.mass (multiplicityVector cubes) ((varietyNeighbours a D).erase a) +
      multiplicityVector cubes a = Certificate.mass (multiplicityVector cubes) (varietyNeighbours a D) :=
    Finset.sum_erase_add _ _ ha
  have hnonneg : 0 ≤ Certificate.mass (multiplicityVector cubes) ((varietyNeighbours a D).erase a) :=
    Finset.sum_nonneg fun i _ => multiplicity_nonneg cubes i
  change _ + (multiplicity cubes a : Int) = _ at hsum
  have hcards : D.card + Dᶜ.card = 8 := by
    simp
  refine ⟨Dᶜ, ?_, ?_⟩
  · omega
  · simpa only [anchorBad, compl_compl] using
      (show Certificate.mass (multiplicityVector cubes) ((varietyNeighbours a D).erase a) ≤
        (7 : Int) - multiplicity cubes a - Dᶜ.card from by
          omega)

end FiveColour.Physical
