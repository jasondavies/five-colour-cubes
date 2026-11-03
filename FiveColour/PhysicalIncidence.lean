module
public import FiveColour.Catalogue
public import FiveColour.CornerKeyData
public import FiveColour.Incidence
@[expose] public section
namespace FiveColour.Physical
open ColourCubes.Geometry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The compact keys are checked against all 600 physical corners. -/
lemma catalogueCornerKey_correct : ∀ (i : Fin 75) (k : Fin 8),
    catalogueCornerKey i k = cornerKey (corner (catalogue i) k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaustive incidence checking only compares small integer corner keys. -/
lemma incidence_keys (t : Fin 75) : ∀ (i : Fin 75) (k : Fin 8),
    (Replay.fits t i).testBit k.val = true ↔
      ∃ l, catalogueCornerKey i l = catalogueCornerKey t k := by
  fin_cases t <;> decide +kernel

/-- Each stored bit agrees with cyclic corner equality on actual faces. -/
lemma incidence_corners (t i : Fin 75) (k : Fin 8) :
    (Replay.fits t i).testBit k.val = true ↔
      ∃ l, CyclicEq (corner (catalogue i) l) (corner (catalogue t) k) := by
  simpa only [catalogueCornerKey_correct, cornerKey_eq_iff] using incidence_keys t i k

/-- The search incidence matrix exactly records physical corner compatibility. -/
theorem incidence_fits (t i : Fin 75) (k : Fin 8) :
    (Replay.fits t i).testBit k.val = true ↔ Fits (catalogue i) (catalogue t) k := by
  rw [fits_iff_corner]
  exact incidence_corners t i k

end FiveColour.Physical
