module
import FiveColour.Chunked.Case78
open FiveColour.Packed

-- A changed lower or upper checkpoint must fail, even with a valid index.
example : Chunks.check 15 (fun _ => []) (fun _ : Fin 1 => ⟨0, 1⟩)
    ⟨1, 1⟩ (.reuse 0) = false := by decide +kernel
example : Chunks.check 15 (fun _ => []) (fun _ : Fin 1 => ⟨0, 1⟩)
    ⟨0, 2⟩ (.reuse 0) = false := by decide +kernel

-- Branches that would break the bounded-digit invariant must also fail.
example : Chunks.check 15 (fun _ => []) (Fin.elim0 : Fin 0 → Box)
    ⟨0, 0⟩ (.split 0 (-1) (.run .mass) (.run .mass)) = false := by decide +kernel
example : Chunks.check 15 (fun _ => []) (Fin.elim0 : Fin 0 → Box)
    ⟨0, 0⟩ (.split 0 7 (.run .mass) (.run .mass)) = false := by decide +kernel

-- Corrupt every referenced checkpoint in the root chunk of a real certificate.
-- The original root chunk is accepted; the altered references must be rejected.
namespace FiveColour.Packed.Chunked.Case78
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private def wrongReferences (i : Fin 2) : Box :=
  { Part4.references i with lower := (Part4.references i).lower + 1 }
example : Chunks.check 15 families wrongReferences Part4.root Part4.proof = false := by
  decide +kernel
end FiveColour.Packed.Chunked.Case78
