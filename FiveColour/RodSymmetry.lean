module
public import FiveColour.BoxDirectional
public import FiveColour.RodAxes
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000

lemma rotatedAxis_faces : ∀ (r : Fin 24) (a : Fin 3),
    (ColourCubes.rotations r ⟨2*a.val,by omega⟩ = ⟨2*(axisEquiv r a).val,by omega⟩ ∧
      ColourCubes.rotations r ⟨2*a.val+1,by omega⟩ = ⟨2*(axisEquiv r a).val+1,by omega⟩) ∨
    (ColourCubes.rotations r ⟨2*a.val,by omega⟩ = ⟨2*(axisEquiv r a).val+1,by omega⟩ ∧
      ColourCubes.rotations r ⟨2*a.val+1,by omega⟩ = ⟨2*(axisEquiv r a).val,by omega⟩) := by decide +kernel

lemma axial_rotate (t : Cube) (r : Fin 24) (a : Fin 3) :
    Axial (rotate t r) a ↔ Axial t (axisEquiv r a) := by
  rcases rotatedAxis_faces r a with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simp only [Axial,rotate,ColourCubes.rotate,h0,h1]
  · simp only [Axial,rotate,ColourCubes.rotate,h0,h1,eq_comm]

lemma normalised_axial (t : Fin 75) (a : Fin 3) :
    Axial (catalogue t) a ↔ Axial (catalogue (anchorFor t))
      (axisEquiv (normalisationRotation t) a) := by
  have h : Axial (recolour (normalisingColour t) (catalogue t)) a ↔ Axial (catalogue t) a := by
    simp only [Axial,recolour,(normalisingColour t).injective.eq_iff]
  rw [← h]
  rw [normalisation_cube t]
  exact axial_rotate _ _ _
end FiveColour.Physical
