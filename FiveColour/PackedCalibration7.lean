module
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow70_weights : cutRow70.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow71_weights : cutRow71.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow72_weights : cutRow72.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow73_weights : cutRow73.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow74_weights : cutRow74.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
end FiveColour.Packed
