module
public import FiveColour.PackedData
public import FiveColour.PackedComputations
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow30_weights : cutRow30.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow31_weights : cutRow31.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow32_weights : cutRow32.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow33_weights : cutRow33.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow34_weights : cutRow34.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow35_weights : cutRow35.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow36_weights : cutRow36.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow37_weights : cutRow37.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow38_weights : cutRow38.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow39_weights : cutRow39.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
end FiveColour.Packed
