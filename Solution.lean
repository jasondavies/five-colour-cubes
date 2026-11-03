module
public import FiveColour.ComparatorBridge
public import FiveColour.FrameResults
public import FiveColour.SmallSupport
public import FiveColour.ProjectedChunks.Threshold
@[expose] public section

/-! Final comparator solution. Build only after complete archive replay.
This module contains no statement holes and does not import Challenge. -/
namespace FiveColour.Puzzle

theorem threshold15 (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : HasSolution cubes :=
  solution_of_threshold Packed.ProjectedChunks.threshold15 cubes hc le_rfl

theorem sharp_threshold15 :
    (∀ cubes : Fin 15 → Cube, (∀ i, UsesAllColours (cubes i)) → HasSolution cubes) ∧
    ∃ cubes : Fin 14 → Cube, (∀ i, UsesAllColours (cubes i)) ∧ ¬ HasSolution cubes :=
  sharp_of_threshold Packed.ProjectedChunks.threshold15

theorem least_guaranteed_size :
    IsLeast {m : Nat | ∀ n, ∀ cubes : Fin n → Cube,
      (∀ i, UsesAllColours (cubes i)) → m ≤ n → HasSolution cubes} 15 :=
  least_of_threshold Packed.ProjectedChunks.threshold15

/-- The sharp frame bound for every side length at least three. -/
theorem frame_bound {m : ℕ} (n : ℕ) (hn : 3 ≤ n) (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hm : 12*n-16 ≤ m) :
    Physical.FrameSolvable (n-2) cubes :=
  Physical.frame_bound_of_threshold Packed.ProjectedChunks.threshold15 n hn cubes hc hm

/-- For n ≥ 3, a frame needs no spare cubes. -/
theorem frame_threshold (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → Physical.FrameSolvable (n-2) cubes} (12*n-16) :=
  Physical.frame_threshold_of_threshold Packed.ProjectedChunks.threshold15 n hn

/-- All twenty supplied cubes form a 3-frame. -/
theorem frame20 (cubes : Fin 20 → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    Physical.FrameSolvable 1 cubes := frame_bound 3 le_rfl cubes hc le_rfl

/-- The complete frame function, including n = 2. -/
theorem frame_threshold_all (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → Physical.FrameSolvable (n-2) cubes}
      (max (12*n-16) 15) :=
  Physical.frame_threshold_all_of_threshold Packed.ProjectedChunks.threshold15 n hn

/-- Every n³ cubes can all be assembled, for n ≥ 3. -/
theorem full_cube (n : ℕ) (hn : 3 ≤ n) (cubes : Fin (n^3) → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : Physical.FullSolvable (n-2) cubes :=
  Physical.full_cube_of_threshold Packed.ProjectedChunks.threshold15 n hn cubes hc

theorem full_cube27 (cubes : Fin 27 → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    Physical.FullSolvable 1 cubes := full_cube 3 le_rfl cubes hc

theorem full_cube64 (cubes : Fin 64 → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    Physical.FullSolvable 2 cubes := full_cube 4 (by decide) cubes hc

/-- The exact guaranteed pool size for a complete cube. -/
theorem complete_cube_threshold (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → Physical.FullSolvable (n-2) cubes} (max (n^3) 15) :=
  Physical.complete_threshold_of_threshold Packed.ProjectedChunks.threshold15 n hn

/-- Exact corner thresholds for collections using at most k varieties. -/
theorem support_threshold (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {v | Physical.SupportGuarantee k v} (if k = 1 then 8 else if k = 2 then 13 else 15) :=
  Physical.support_threshold_of_threshold Packed.ProjectedChunks.threshold15 k hk

end FiveColour.Puzzle
