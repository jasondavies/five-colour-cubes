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

theorem six_masks_valid_0 : ∀ (t i : Fin 75) (g : Fin 8),
    sixGroup 0 i = some g → ∀ q : Fin 8, (sixMasks 0 t g).testBit q.val = true →
        (Replay.fits t i).testBit q.val = true := by decide +kernel

end FiveColour.Physical
