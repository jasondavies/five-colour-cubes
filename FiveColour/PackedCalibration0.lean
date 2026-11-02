module
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow0_weights : cutRow0.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow1_weights : cutRow1.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow2_weights : cutRow2.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow3_weights : cutRow3.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow4_weights : cutRow4.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow5_weights : cutRow5.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow6_weights : cutRow6.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow7_weights : cutRow7.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow8_weights : cutRow8.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow9_weights : cutRow9.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
end FiveColour.Packed
