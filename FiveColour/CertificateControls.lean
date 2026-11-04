module
public import FiveColour.PackedChunks
open FiveColour.Packed

-- Checkpoint reuse requires exact agreement of both bounds.
example : Chunks.check 15 (fun _ => []) (fun _ : Fin 1 => ⟨0, 1⟩)
    ⟨0, 1⟩ (.reuse 0) = true := by decide +kernel
example : Chunks.check 15 (fun _ => []) (fun _ : Fin 1 => ⟨0, 1⟩)
    ⟨1, 1⟩ (.reuse 0) = false := by decide +kernel
example : Chunks.check 15 (fun _ => []) (fun _ : Fin 1 => ⟨0, 1⟩)
    ⟨0, 2⟩ (.reuse 0) = false := by decide +kernel

-- Branches that break the bounded-digit invariant must fail.
example : Chunks.check 15 (fun _ => []) (Fin.elim0 : Fin 0 → Box)
    ⟨0, 0⟩ (.split 0 (-1) (.run .mass) (.run .mass)) = false := by decide +kernel
example : Chunks.check 15 (fun _ => []) (Fin.elim0 : Fin 0 → Box)
    ⟨0, 0⟩ (.split 0 7 (.run .mass) (.run .mass)) = false := by decide +kernel
