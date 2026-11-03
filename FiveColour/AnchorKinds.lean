module
public import FiveColour.SymmetryAction
@[expose] public section
namespace FiveColour.Physical

/-- The repeated colour occurs on opposite faces. -/
def OppositeRepeat (c : Cube) : Prop := ∃ f : Fin 6, c f = c (ColourCubes.opposite f)

instance (c : Cube) : Decidable (OppositeRepeat c) := by
  unfold OppositeRepeat
  infer_instance

lemma rotation_opposite : ∀ (r : Fin 24) (f : Fin 6),
    ColourCubes.rotations r (ColourCubes.opposite f) = ColourCubes.opposite (ColourCubes.rotations r f) := by
  decide +kernel

lemma reflection_opposite : ∀ f : Fin 6,
    reflectFace (ColourCubes.opposite f) = ColourCubes.opposite (reflectFace f) := by
  decide +kernel

theorem oppositeRepeat_rotate (c : Cube) (r : Fin 24) :
    OppositeRepeat (rotate c r) ↔ OppositeRepeat c := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨ColourCubes.rotations r f, by simpa only [rotate, ColourCubes.rotate, rotation_opposite] using hf⟩
  · rintro ⟨g, hg⟩
    obtain ⟨f, rfl⟩ := (ColourCubes.rotations_bijective r).surjective g
    exact ⟨f, by simpa only [rotate, ColourCubes.rotate, rotation_opposite] using hg⟩

theorem oppositeRepeat_recolour (p : Equiv.Perm (Fin 5)) (c : Cube) :
    OppositeRepeat (recolour p c) ↔ OppositeRepeat c := by
  simp only [OppositeRepeat, recolour, p.injective.eq_iff]

theorem oppositeRepeat_reflect (c : Cube) :
    OppositeRepeat (reflectCube c) ↔ OppositeRepeat c := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨reflectFace f, by simpa only [reflectCube, reflection_opposite] using hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨reflectFace f, by simpa only [reflectCube, reflection_opposite, reflectFace_involutive] using hf⟩

theorem oppositeRepeat_apply (s : PuzzleSymmetry) (c : Cube) :
    OppositeRepeat (s.apply c) ↔ OppositeRepeat c := by
  cases s with
  | mk p b => cases b <;> simp [PuzzleSymmetry.apply, oppositeRepeat_recolour, oppositeRepeat_reflect]

theorem oppositeRepeat_varietyEquiv (s : PuzzleSymmetry) (i : Fin 75) :
    OppositeRepeat (catalogue (varietyEquiv s i)) ↔ OppositeRepeat (catalogue i) := by
  obtain ⟨r, hr⟩ := catalogueIndex_spec (s.apply (catalogue i))
    ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours i))
  have ht : OppositeRepeat (s.apply (catalogue i)) ↔
      OppositeRepeat (catalogue (varietyEquiv s i)) := by
    conv_lhs => rw [hr]
    exact oppositeRepeat_rotate _ _
  exact ht.symm.trans (oppositeRepeat_apply s _)

/-- The representative indices used by the case generator: opposite 0, adjacent 3. -/
def anchorFor (i : Fin 75) : Fin 75 := if OppositeRepeat (catalogue i) then 0 else 3

lemma anchor_kinds : OppositeRepeat (catalogue 0) ∧ ¬ OppositeRepeat (catalogue 3) := by
  decide +kernel

lemma catalogue_kind_counts :
    (Finset.univ.filter fun i : Fin 75 => OppositeRepeat (catalogue i)).card = 15 ∧
    (Finset.univ.filter fun i : Fin 75 => ¬ OppositeRepeat (catalogue i)).card = 60 := by
  decide +kernel

/-- Symmetries preserve the stronger bound on adjacent-repeat varieties
used when an opposite-repeat anchor has maximum multiplicity. -/
theorem kind_capacity_apply {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (adjacent opposite : Nat) :
    (∀ i, multiplicity (fun j => s.apply (cubes j)) i ≤
      if OppositeRepeat (catalogue i) then opposite else adjacent) ↔
    (∀ i, multiplicity cubes i ≤ if OppositeRepeat (catalogue i) then opposite else adjacent) := by
  constructor
  · intro h i
    have hi := h (varietyEquiv s i)
    simpa only [multiplicity_apply s cubes hc, oppositeRepeat_varietyEquiv] using hi
  · intro h j
    obtain ⟨i, rfl⟩ := (varietyEquiv s).surjective j
    simpa only [multiplicity_apply s cubes hc, oppositeRepeat_varietyEquiv] using h i

end FiveColour.Physical
