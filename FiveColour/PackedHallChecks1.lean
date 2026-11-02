module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_10 : actualSignatures 10 = expectedSignatures 10 := by decide +kernel
lemma hall_signatures_11 : actualSignatures 11 = expectedSignatures 11 := by decide +kernel
lemma hall_signatures_12 : actualSignatures 12 = expectedSignatures 12 := by decide +kernel
lemma hall_signatures_13 : actualSignatures 13 = expectedSignatures 13 := by decide +kernel
lemma hall_signatures_14 : actualSignatures 14 = expectedSignatures 14 := by decide +kernel
lemma hall_signatures_15 : actualSignatures 15 = expectedSignatures 15 := by decide +kernel
lemma hall_signatures_16 : actualSignatures 16 = expectedSignatures 16 := by decide +kernel
lemma hall_signatures_17 : actualSignatures 17 = expectedSignatures 17 := by decide +kernel
lemma hall_signatures_18 : actualSignatures 18 = expectedSignatures 18 := by decide +kernel
lemma hall_signatures_19 : actualSignatures 19 = expectedSignatures 19 := by decide +kernel
end FiveColour.Packed
