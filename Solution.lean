module
public import FiveColour.ComparatorBridge
public import FiveColour.ReplayChunks.Threshold
@[expose] public section

/-! Final comparator solution. Build only after complete archive replay.
This module contains no statement holes and does not import Challenge. -/
namespace FiveColour.Puzzle

theorem threshold15 (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : HasSolution cubes :=
  solution_of_threshold Packed.ReplayChunks.threshold15 cubes hc le_rfl

theorem sharp_threshold15 :
    (∀ cubes : Fin 15 → Cube, (∀ i, UsesAllColours (cubes i)) → HasSolution cubes) ∧
    ∃ cubes : Fin 14 → Cube, (∀ i, UsesAllColours (cubes i)) ∧ ¬ HasSolution cubes :=
  sharp_of_threshold Packed.ReplayChunks.threshold15

theorem least_guaranteed_size :
    IsLeast {m : Nat | ∀ n, ∀ cubes : Fin n → Cube,
      (∀ i, UsesAllColours (cubes i)) → m ≤ n → HasSolution cubes} 15 :=
  least_of_threshold Packed.ReplayChunks.threshold15

end FiveColour.Puzzle
