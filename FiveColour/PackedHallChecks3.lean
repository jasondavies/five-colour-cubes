module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_30 : actualSignatures 30 = expectedSignatures 30 := by decide +kernel
lemma hall_signatures_31 : actualSignatures 31 = expectedSignatures 31 := by decide +kernel
lemma hall_signatures_32 : actualSignatures 32 = expectedSignatures 32 := by decide +kernel
lemma hall_signatures_33 : actualSignatures 33 = expectedSignatures 33 := by decide +kernel
lemma hall_signatures_34 : actualSignatures 34 = expectedSignatures 34 := by decide +kernel
lemma hall_signatures_35 : actualSignatures 35 = expectedSignatures 35 := by decide +kernel
lemma hall_signatures_36 : actualSignatures 36 = expectedSignatures 36 := by decide +kernel
lemma hall_signatures_37 : actualSignatures 37 = expectedSignatures 37 := by decide +kernel
lemma hall_signatures_38 : actualSignatures 38 = expectedSignatures 38 := by decide +kernel
lemma hall_signatures_39 : actualSignatures 39 = expectedSignatures 39 := by decide +kernel
end FiveColour.Packed
