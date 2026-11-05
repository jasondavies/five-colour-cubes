module
public import FiveColour.ExtremalLocalData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

def sixInventories1 : List LocalInventory := [
]

theorem six_inventories_cover_1 :
    sixInventories1.map LocalInventory.counts = sixCompositionDomain 1 := by decide +kernel

theorem six_inventories_valid_1 :
    ∀ w ∈ sixInventories1, w.Valid 1 6 := by decide +kernel

end FiveColour.Physical
