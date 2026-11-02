module
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow20_weights : cutRow20.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow21_weights : cutRow21.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow22_weights : cutRow22.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow23_weights : cutRow23.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow24_weights : cutRow24.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow25_weights : cutRow25.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow26_weights : cutRow26.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow27_weights : cutRow27.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow28_weights : cutRow28.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
theorem cutRow29_weights : cutRow29.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by decide +kernel
end FiveColour.Packed
