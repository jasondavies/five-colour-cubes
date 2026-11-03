module
public import FiveColour.BoxCounts
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

lemma rectFits_iff_physical (c t : Cube) {l : Fin 3 → ℕ} (p : RectSlot l) :
    RectFits c t p ↔ FacesFit c t (rectExposed l p) := by
  refine ⟨rectFits_physical c t p,?_⟩
  rintro ⟨r,hr,hfit⟩
  obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
  cases p with
  | inl k => exact ⟨r,fun j => hfit _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
  | inr p => exact ⟨_,_,rotation_adjacent r _ _ (edge_adjacent p.1),hfit _ (by simp [rectExposed]),hfit _ (by simp [rectExposed])⟩
end FiveColour.Physical
