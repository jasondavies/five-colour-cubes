module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_70 : actualSignatures 70 = expectedSignatures 70 := by decide +kernel
lemma hall_signatures_71 : actualSignatures 71 = expectedSignatures 71 := by decide +kernel
lemma hall_signatures_72 : actualSignatures 72 = expectedSignatures 72 := by decide +kernel
lemma hall_signatures_73 : actualSignatures 73 = expectedSignatures 73 := by decide +kernel
lemma hall_signatures_74 : actualSignatures 74 = expectedSignatures 74 := by decide +kernel
end FiveColour.Packed
