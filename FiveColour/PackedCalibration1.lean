module
public import FiveColour.PackedData
public import FiveColour.PackedComputations
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed
theorem cutRow10_weights : cutRow10.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow11_weights : cutRow11.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow12_weights : cutRow12.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow13_weights : cutRow13.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow14_weights : cutRow14.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow15_weights : cutRow15.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow16_weights : cutRow16.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow17_weights : cutRow17.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow18_weights : cutRow18.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
theorem cutRow19_weights : cutRow19.toList.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  apply FastWeight.list_weights_of_fast
  decide +kernel
end FiveColour.Packed
