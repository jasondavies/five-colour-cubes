module
public import FiveColour.PackedCalibration0
public import FiveColour.PackedCalibration1
public import FiveColour.PackedCalibration2
public import FiveColour.PackedCalibration3
public import FiveColour.PackedCalibration4
public import FiveColour.PackedCalibration5
public import FiveColour.PackedCalibration6
public import FiveColour.PackedCalibration7
@[expose] public section
namespace FiveColour.Packed
set_option maxRecDepth 100000

theorem cuts_weights : cuts.toList.all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true := by
  change [cutRow0,cutRow1,cutRow2,cutRow3,cutRow4,cutRow5,cutRow6,cutRow7,cutRow8,cutRow9,cutRow10,cutRow11,cutRow12,cutRow13,cutRow14,cutRow15,cutRow16,cutRow17,cutRow18,cutRow19,cutRow20,cutRow21,cutRow22,cutRow23,cutRow24,cutRow25,cutRow26,cutRow27,cutRow28,cutRow29,cutRow30,cutRow31,cutRow32,cutRow33,cutRow34,cutRow35,cutRow36,cutRow37,cutRow38,cutRow39,cutRow40,cutRow41,cutRow42,cutRow43,cutRow44,cutRow45,cutRow46,cutRow47,cutRow48,cutRow49,cutRow50,cutRow51,cutRow52,cutRow53,cutRow54,cutRow55,cutRow56,cutRow57,cutRow58,cutRow59,cutRow60,cutRow61,cutRow62,cutRow63,cutRow64,cutRow65,cutRow66,cutRow67,cutRow68,cutRow69,cutRow70,cutRow71,cutRow72,cutRow73,cutRow74].all (fun row => row.toList.all (fun c => decide (c.weight = maskWeight c.member))) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, cutRow0_weights,cutRow1_weights,cutRow2_weights,cutRow3_weights,cutRow4_weights,cutRow5_weights,cutRow6_weights,cutRow7_weights,cutRow8_weights,cutRow9_weights,cutRow10_weights,cutRow11_weights,cutRow12_weights,cutRow13_weights,cutRow14_weights,cutRow15_weights,cutRow16_weights,cutRow17_weights,cutRow18_weights,cutRow19_weights,cutRow20_weights,cutRow21_weights,cutRow22_weights,cutRow23_weights,cutRow24_weights,cutRow25_weights,cutRow26_weights,cutRow27_weights,cutRow28_weights,cutRow29_weights,cutRow30_weights,cutRow31_weights,cutRow32_weights,cutRow33_weights,cutRow34_weights,cutRow35_weights,cutRow36_weights,cutRow37_weights,cutRow38_weights,cutRow39_weights,cutRow40_weights,cutRow41_weights,cutRow42_weights,cutRow43_weights,cutRow44_weights,cutRow45_weights,cutRow46_weights,cutRow47_weights,cutRow48_weights,cutRow49_weights,cutRow50_weights,cutRow51_weights,cutRow52_weights,cutRow53_weights,cutRow54_weights,cutRow55_weights,cutRow56_weights,cutRow57_weights,cutRow58_weights,cutRow59_weights,cutRow60_weights,cutRow61_weights,cutRow62_weights,cutRow63_weights,cutRow64_weights,cutRow65_weights,cutRow66_weights,cutRow67_weights,cutRow68_weights,cutRow69_weights,cutRow70_weights,cutRow71_weights,cutRow72_weights,cutRow73_weights,cutRow74_weights]

theorem cuts_valid (r : Fin 75) : ∀ c ∈ (cuts[r.val]!).toList, c.Valid := by
  apply list_valid_of_weights
  apply List.all_eq_true.mp cuts_weights
  have hsize : cuts.size = 75 := by decide +kernel
  have hr : r.val < cuts.size := by omega
  simpa only [getElem!_pos cuts r.val hr] using Array.getElem_mem_toList hr
end FiveColour.Packed
