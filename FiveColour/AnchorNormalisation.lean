module
public import FiveColour.NormalisationData
public import FiveColour.SymmetryConstraints
@[expose] public section
namespace FiveColour.Physical

/-- Colour relabelling alone suffices to normalise an anchor. -/
def anchorSymmetry (i : Fin 75) : PuzzleSymmetry := ⟨normalisingColour i, false⟩

/-- Every variety reaches the representative of its repeated-face class. -/
theorem normalise_variety (i : Fin 75) : varietyEquiv (anchorSymmetry i) i = anchorFor i := by
  change catalogueIndex (recolour (normalisingColour i) (catalogue i)) = anchorFor i
  rw [funext (normalisation_faces i)]
  exact catalogue_index_rotations _ _

lemma varietyEquiv_colour_trans (p q : Equiv.Perm (Fin 5)) (i : Fin 75) :
    varietyEquiv ⟨p.trans q, false⟩ i = varietyEquiv ⟨q, false⟩ (varietyEquiv ⟨p, false⟩ i) := by
  exact catalogueIndex_apply ⟨q, false⟩ (recolour p (catalogue i))
    ((usesAllColours_recolour p _).mpr (catalogue_uses_all_colours i))

/-- There are exactly two colour-permutation orbits: adjacent and opposite repeats. -/
theorem same_colour_orbit_iff (i j : Fin 75) :
    (∃ p : Equiv.Perm (Fin 5), varietyEquiv ⟨p, false⟩ i = j) ↔
      (OppositeRepeat (catalogue i) ↔ OppositeRepeat (catalogue j)) := by
  constructor
  · rintro ⟨p, hp⟩
    have h := oppositeRepeat_varietyEquiv ⟨p, false⟩ i
    rw [hp] at h
    exact h.symm
  · intro h
    have ha : anchorFor i = anchorFor j := by simp only [anchorFor, h]
    refine ⟨(normalisingColour i).trans (normalisingColour j).symm, ?_⟩
    rw [varietyEquiv_colour_trans]
    change varietyEquiv ⟨(normalisingColour j).symm, false⟩
      (varietyEquiv (anchorSymmetry i) i) = j
    rw [normalise_variety, ha]
    have hj := (varietyEquiv (anchorSymmetry j)).symm_apply_apply j
    rw [normalise_variety] at hj
    exact hj

/-- A chosen anchor can be normalised without changing solvability, its
multiplicity, or any physical-copy distinction. -/
theorem normalised_counterexample {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) (a : Fin 75) :
    (∀ j, UsesAllColours ((anchorSymmetry a).apply (cubes j))) ∧
      ¬ HasSolution (fun j => (anchorSymmetry a).apply (cubes j)) ∧
      multiplicity (fun j => (anchorSymmetry a).apply (cubes j)) (anchorFor a) = multiplicity cubes a := by
  refine ⟨fun j => ((anchorSymmetry a).usesAllColours_apply _).mpr (hc j), ?_, ?_⟩
  · exact fun hs => h (((anchorSymmetry a).hasSolution_apply cubes).mp hs)
  · rw [← normalise_variety a]
    exact multiplicity_apply _ cubes hc a

/-- The anchor-cover lemma may be applied after normalisation, using the
original anchor's multiplicity and the generator's representative index. -/
theorem normalised_anchor_cover {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) (a : Fin 75) :
    ∃ K : Finset (Fin 8), K.card + multiplicity cubes a ≤ 7 ∧
      Certificate.mass (multiplicityVector (fun j => (anchorSymmetry a).apply (cubes j)))
          (anchorBad (anchorFor a) K) ≤
        (7 : Int) - multiplicity cubes a - K.card := by
  obtain ⟨hc', h', hm⟩ := normalised_counterexample cubes hc h a
  simpa only [hm] using anchor_cover (fun j => (anchorSymmetry a).apply (cubes j)) hc' h' (anchorFor a)

end FiveColour.Physical
