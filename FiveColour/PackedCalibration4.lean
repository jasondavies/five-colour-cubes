module
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow40_weights : cutRow40.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow41_weights : cutRow41.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow42_weights : cutRow42.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow43_weights : cutRow43.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow44_weights : cutRow44.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow45_weights : cutRow45.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow46_weights : cutRow46.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow47_weights : cutRow47.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow48_weights : cutRow48.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow49_weights : cutRow49.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
end FiveColour.Packed
