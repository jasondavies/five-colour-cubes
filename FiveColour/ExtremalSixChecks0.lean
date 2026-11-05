module
public import FiveColour.ExtremalLocalData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

def sixInventories0 : List LocalInventory := [
]

theorem six_inventories_cover_0 :
    sixInventories0.map LocalInventory.counts = sixCompositionDomain 0 := by decide +kernel

theorem six_inventories_valid_0 :
    ∀ w ∈ sixInventories0, w.Valid 0 6 := by decide +kernel

end FiveColour.Physical
