module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_0 : actualSignatures 0 = expectedSignatures 0 := by decide +kernel
lemma hall_signatures_1 : actualSignatures 1 = expectedSignatures 1 := by decide +kernel
lemma hall_signatures_2 : actualSignatures 2 = expectedSignatures 2 := by decide +kernel
lemma hall_signatures_3 : actualSignatures 3 = expectedSignatures 3 := by decide +kernel
lemma hall_signatures_4 : actualSignatures 4 = expectedSignatures 4 := by decide +kernel
lemma hall_signatures_5 : actualSignatures 5 = expectedSignatures 5 := by decide +kernel
lemma hall_signatures_6 : actualSignatures 6 = expectedSignatures 6 := by decide +kernel
lemma hall_signatures_7 : actualSignatures 7 = expectedSignatures 7 := by decide +kernel
lemma hall_signatures_8 : actualSignatures 8 = expectedSignatures 8 := by decide +kernel
lemma hall_signatures_9 : actualSignatures 9 = expectedSignatures 9 := by decide +kernel
end FiveColour.Packed
