module
public import FiveColour.PackedHallCore
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed
lemma hall_signatures_60 : actualSignatures 60 = expectedSignatures 60 := by decide +kernel
lemma hall_signatures_61 : actualSignatures 61 = expectedSignatures 61 := by decide +kernel
lemma hall_signatures_62 : actualSignatures 62 = expectedSignatures 62 := by decide +kernel
lemma hall_signatures_63 : actualSignatures 63 = expectedSignatures 63 := by decide +kernel
lemma hall_signatures_64 : actualSignatures 64 = expectedSignatures 64 := by decide +kernel
lemma hall_signatures_65 : actualSignatures 65 = expectedSignatures 65 := by decide +kernel
lemma hall_signatures_66 : actualSignatures 66 = expectedSignatures 66 := by decide +kernel
lemma hall_signatures_67 : actualSignatures 67 = expectedSignatures 67 := by decide +kernel
lemma hall_signatures_68 : actualSignatures 68 = expectedSignatures 68 := by decide +kernel
lemma hall_signatures_69 : actualSignatures 69 = expectedSignatures 69 := by decide +kernel
end FiveColour.Packed
