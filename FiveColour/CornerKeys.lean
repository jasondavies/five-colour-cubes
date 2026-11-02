module
public import FiveColour.CatalogueData
@[expose] public section
namespace FiveColour.Physical
open ThreeColour.Geometry

/-- A cyclic triple encoded by the least of its three base-five readings. -/
def cornerKey (a : Fin 3 → Fin 5) : Nat :=
  min (25 * (a 0).val + 5 * (a 1).val + (a 2).val)
    (min (25 * (a 1).val + 5 * (a 2).val + (a 0).val)
      (25 * (a 2).val + 5 * (a 0).val + (a 1).val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The key preserves orientation: equality is precisely cyclic equality. -/
theorem cornerKey_eq_iff : ∀ a b : Fin 3 → Fin 5,
    cornerKey a = cornerKey b ↔ CyclicEq a b := by
  decide +kernel

end FiveColour.Physical
