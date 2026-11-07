module
public import FiveColour.PackedData
public import FiveColour.PackedComputations
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow50_weights : cutRow50.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow51_weights : cutRow51.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow52_weights : cutRow52.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow53_weights : cutRow53.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow54_weights : cutRow54.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow55_weights : cutRow55.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow56_weights : cutRow56.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow57_weights : cutRow57.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow58_weights : cutRow58.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow59_weights : cutRow59.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
end FiveColour.Packed
