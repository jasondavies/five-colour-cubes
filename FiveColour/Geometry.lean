module
public import FiveColour.Problem
public import ThreeColour.FamilyGeometry
@[expose] public section
namespace FiveColour.Physical
open ThreeColour.Geometry

/-- Rotate a face assignment; face colours themselves remain fixed. -/
def rotate (c : Cube) (r : Fin 24) : Cube := fun f => c (MacMahon.rotations r f)

/-- Rotating a source preserves the corners it can supply. -/
theorem fits_rotate_source (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits (rotate c r) t k ↔ Fits c t k := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := MacMahon.rotation_composition r s
    refine ⟨u, fun f => ?_⟩
    rw [hu]
    exact hs f
  · rintro ⟨s, hs⟩
    obtain ⟨v, hv⟩ := MacMahon.rotation_inverse r
    obtain ⟨u, hu⟩ := MacMahon.rotation_composition v s
    refine ⟨u, fun f => ?_⟩
    change c (MacMahon.rotations r (MacMahon.rotations u (MacMahon.exposedFaces k f))) = _
    rw [hu, hv]
    exact hs f

lemma cyclicEq_trans {a b c : Fin 3 → Fin 5} (hab : CyclicEq a b)
    (hbc : CyclicEq b c) : CyclicEq a c := by
  obtain ⟨s, hs⟩ := hab
  obtain ⟨t, ht⟩ := hbc
  refine ⟨t + s, fun f => ?_⟩
  rw [← add_assoc, hs, ht]

lemma cyclicEq_symm {a b : Fin 3 → Fin 5} (h : CyclicEq a b) : CyclicEq b a := by
  obtain ⟨s, hs⟩ := h
  refine ⟨-s, fun f => ?_⟩
  simpa using (hs (f + -s)).symm

lemma rotated_corner (t : Cube) (r : Fin 24) (k : Fin 8) :
    CyclicEq (corner t (slotEquiv r k)) (corner (rotate t r) k) := by
  obtain ⟨s, hs⟩ := rotatedSlot_frame r k
  exact ⟨s, fun f => congrArg t (hs f).symm⟩

/-- Rotating a target only permutes its eight requirements. -/
theorem fits_rotate_target (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits c (rotate t r) k ↔ Fits c t (slotEquiv r k) := by
  rw [fits_iff_corner, fits_iff_corner]
  constructor
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (cyclicEq_symm (rotated_corner t r k))⟩
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (rotated_corner t r k)⟩

/-- A solution of a rotated target gives a solution of its representative,
with the same eight distinct physical copies. -/
theorem unrotate_solution {n : Nat} (cubes : Fin n → Cube) (t : Cube) (r : Fin 24)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, Fits (cubes (copies k)) (rotate t r) k) :
    ∃ copies' : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (copies' k)) t k := by
  refine ⟨(slotEquiv r).symm.toEmbedding.trans copies, fun k => ?_⟩
  have hk := (fits_rotate_target _ _ _ _).mp (h ((slotEquiv r).symm k))
  simpa using hk

end FiveColour.Physical
