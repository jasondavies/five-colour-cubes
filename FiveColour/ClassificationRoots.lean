module
public import FiveColour.ClassificationData
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Physical.Classification
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma roots_complete : ∀ r : Fin 357, (rootCapacity r).copies.val ≤ 5 →
    ∃ i : Fin 349, rootIndex i = r := by decide +kernel

end FiveColour.Physical.Classification
