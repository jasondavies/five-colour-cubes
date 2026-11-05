module
public import FiveColour.PackedPruning
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

-- Root reduction must cover every possible original alternative. These
-- cuts use coordinate 74, whose calibrated packed weight is 1.
private def pruningRoot : Box := ⟨place 74, 2 * place 74⟩
private def pruningCut : Cut := ⟨2^74, 1, 2⟩
example : covers pruningRoot 2 #[pruningCut] [pruningCut] [0] = true := by decide +kernel
example : covers pruningRoot 2 #[] [pruningCut] [0] = false := by decide +kernel
example : covers pruningRoot 2 #[pruningCut] [pruningCut] [1] = false := by decide +kernel
example : covers pruningRoot 2 #[pruningCut] [pruningCut] [] = false := by decide +kernel
-- The lower bound is only one: dropping that coordinate cannot subtract two.
example : covers pruningRoot 2 #[⟨0,0,0⟩] [pruningCut] [0] = false := by decide +kernel
-- A replacement cannot introduce an unconstrained extra coordinate.
example : covers pruningRoot 2 #[⟨2^74+1,place 74+1,2⟩] [pruningCut] [0] = false := by decide +kernel
