module
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow60_weights : cutRow60.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow61_weights : cutRow61.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow62_weights : cutRow62.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow63_weights : cutRow63.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow64_weights : cutRow64.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow65_weights : cutRow65.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow66_weights : cutRow66.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow67_weights : cutRow67.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow68_weights : cutRow68.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow69_weights : cutRow69.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
end FiveColour.Packed
