module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_20 : actualSignatures 20 = expectedSignatures 20 := by decide +kernel
lemma hall_signatures_21 : actualSignatures 21 = expectedSignatures 21 := by decide +kernel
lemma hall_signatures_22 : actualSignatures 22 = expectedSignatures 22 := by decide +kernel
lemma hall_signatures_23 : actualSignatures 23 = expectedSignatures 23 := by decide +kernel
lemma hall_signatures_24 : actualSignatures 24 = expectedSignatures 24 := by decide +kernel
lemma hall_signatures_25 : actualSignatures 25 = expectedSignatures 25 := by decide +kernel
lemma hall_signatures_26 : actualSignatures 26 = expectedSignatures 26 := by decide +kernel
lemma hall_signatures_27 : actualSignatures 27 = expectedSignatures 27 := by decide +kernel
lemma hall_signatures_28 : actualSignatures 28 = expectedSignatures 28 := by decide +kernel
lemma hall_signatures_29 : actualSignatures 29 = expectedSignatures 29 := by decide +kernel
end FiveColour.Packed
