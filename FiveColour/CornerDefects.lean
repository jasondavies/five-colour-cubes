module
public import FiveColour.SharpGeometry
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma corner_defect_symm (s : Fin 75) : ∀ t,
    cornerMissBits s t = cornerMissBits t s := by
  fin_cases s <;> decide +kernel
lemma opposite_source_corners (s t : Fin 75) (hs : OppositeRepeat (catalogue s)) :
    cornerMissBits s t ≤ 6 := by
  rw [corner_defect_symm]
  exact opposite_corner_bits t s hs
end FiveColour.Physical
