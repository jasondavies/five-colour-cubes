module
public import FiveColour.SymmetryAction
public import FiveColour.Anchor
@[expose] public section
namespace FiveColour.Physical

/-- The orientation chosen for a transformed target only permutes its eight corners. -/
theorem fits_variety_transport (s : PuzzleSymmetry) (t : Fin 75) :
    ∃ e : Equiv.Perm (Fin 8), ∀ (i : Fin 75) (k : Fin 8),
      Fits (catalogue (varietyEquiv s i)) (catalogue (varietyEquiv s t)) (e k) ↔
        Fits (catalogue i) (catalogue t) k := by
  obtain ⟨r, hr⟩ := catalogueIndex_spec (s.apply (catalogue t))
    ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours t))
  refine ⟨s.slots.symm.trans (ColourCubes.Geometry.slotEquiv r), fun i k => ?_⟩
  have h := s.fits_apply (catalogue i) (catalogue t) (s.slots.symm k)
  rw [fits_catalogueIndex _ ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours i))] at h
  rw [hr, fits_rotate_target] at h
  change Fits (catalogue (catalogueIndex (s.apply (catalogue i))))
    (catalogue (catalogueIndex (s.apply (catalogue t))))
    (ColourCubes.Geometry.slotEquiv r (s.slots.symm k)) ↔ Fits (catalogue i) (catalogue t) k
  simpa only [Equiv.apply_symm_apply] using h

/-- Hall neighbourhoods transform by the induced permutation of varieties. -/
theorem varietyNeighbours_transport (s : PuzzleSymmetry) (t : Fin 75) :
    ∃ e : Equiv.Perm (Fin 8), ∀ K : Finset (Fin 8),
      varietyNeighbours (varietyEquiv s t) (K.image e) =
        (varietyNeighbours t K).image (varietyEquiv s) := by
  obtain ⟨e, he⟩ := fits_variety_transport s t
  refine ⟨e, fun K => ?_⟩
  ext j
  obtain ⟨i, rfl⟩ := (varietyEquiv s).surjective j
  constructor
  · intro h
    obtain ⟨k', hk', hf⟩ := (Finset.mem_filter.mp h).2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, (he i k).mp hf⟩, rfl⟩
  · intro h
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp h
    have hji := (varietyEquiv s).injective hij
    subst j
    obtain ⟨k, hk, hf⟩ := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, e k, Finset.mem_image_of_mem e hk, (he i k).mpr hf⟩

/-- Complementing a corner set commutes with a permutation of all eight corners. -/
lemma image_complement (e : Equiv.Perm (Fin 8)) (K : Finset (Fin 8)) :
    (K.image e)ᶜ = Kᶜ.image e := by
  ext j
  obtain ⟨k, rfl⟩ := e.surjective j
  simp [Finset.mem_image, e.injective.eq_iff]

/-- The anchor's excluded neighbourhood transforms exactly, including removal
of the anchor itself. This justifies reducing cover constraints by stabilisers. -/
theorem anchorBad_transport (s : PuzzleSymmetry) (a : Fin 75) :
    ∃ e : Equiv.Perm (Fin 8), ∀ K : Finset (Fin 8),
      (K.image e).card = K.card ∧
      anchorBad (varietyEquiv s a) (K.image e) = (anchorBad a K).image (varietyEquiv s) := by
  obtain ⟨e, he⟩ := varietyNeighbours_transport s a
  refine ⟨e, fun K => ⟨Finset.card_image_of_injective K e.injective, ?_⟩⟩
  simp only [anchorBad, image_complement, he, Finset.image_erase (varietyEquiv s).injective]

/-- Root neighbourhood sums, and hence Hall budgets, survive global symmetry. -/
theorem anchor_budget_transport {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (a : Fin 75) :
    ∃ e : Equiv.Perm (Fin 8), ∀ K : Finset (Fin 8),
      (K.image e).card = K.card ∧
      Certificate.mass (multiplicityVector (fun j => s.apply (cubes j)))
          (anchorBad (varietyEquiv s a) (K.image e)) =
        Certificate.mass (multiplicityVector cubes) (anchorBad a K) := by
  obtain ⟨e, he⟩ := anchorBad_transport s a
  refine ⟨e, fun K => ⟨(he K).1, ?_⟩⟩
  rw [(he K).2]
  exact mass_apply s cubes hc _

end FiveColour.Physical
