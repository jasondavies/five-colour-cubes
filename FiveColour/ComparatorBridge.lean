module
public import FiveColour.Puzzle
public import FiveColour.LowerBound
@[expose] public section
namespace FiveColour.Puzzle

/-- The enumerated rotations in the proof describe exactly the geometric moves. -/
theorem hasSolution_iff {n : Nat} (cubes : Fin n → Cube) :
    HasSolution cubes ↔ Physical.HasSolution cubes := by
  simp only [HasSolution, ColourCubes.HasSolution, Physical.HasSolution,
    ColourCubes.builds_iff_tableFits, UsesAllColours, Physical.UsesAllColours,
    Physical.Fits]

/-- The geometric lower bound is unconditional and already kernel checked. -/
theorem lower_bound :
    (∀ i, UsesAllColours (lowerFamily i)) ∧ ¬ HasSolution lowerFamily :=
  ⟨Physical.lower_bound.1, fun h => Physical.lower_bound.2 (hasSolution_iff _ |>.mp h)⟩

/-- Selecting a subcollection and then eight copies preserves distinctness. -/
theorem hasSolution_of_subfamily {m n : Nat} (cubes : Fin n → Cube)
    (selection : Fin m ↪ Fin n) (h : HasSolution (fun i => cubes (selection i))) :
    HasSolution cubes := by
  obtain ⟨target, ht, copies, hfaces⟩ := h
  exact ⟨target, ht, copies.trans selection, hfaces⟩

/-- Transfer a physical threshold proof to arbitrary larger geometric collections. -/
theorem solution_of_threshold (h : Physical.Threshold15) {n : Nat}
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) :
    HasSolution cubes := by
  let selection : Fin 15 ↪ Fin n := Fin.castLEEmb hn
  apply hasSolution_of_subfamily cubes selection
  exact (hasSolution_iff _).mpr (h _ (fun i => hc (selection i)))

theorem sharp_of_threshold (h : Physical.Threshold15) :
    (∀ cubes : Fin 15 → Cube, (∀ i, UsesAllColours (cubes i)) → HasSolution cubes) ∧
    ∃ cubes : Fin 14 → Cube, (∀ i, UsesAllColours (cubes i)) ∧ ¬ HasSolution cubes :=
  ⟨fun cubes hc => solution_of_threshold h cubes hc le_rfl, lowerFamily, lower_bound⟩

theorem least_of_threshold (h : Physical.Threshold15) :
    IsLeast {m : Nat | ∀ n, ∀ cubes : Fin n → Cube,
      (∀ i, UsesAllColours (cubes i)) → m ≤ n → HasSolution cubes} 15 := by
  refine ⟨fun _ cubes hc hn => solution_of_threshold h cubes hc hn, ?_⟩
  intro m hm
  by_contra hn
  have hm14 : m ≤ 14 := by omega
  exact lower_bound.2 (hm 14 lowerFamily lower_bound.1 hm14)

end FiveColour.Puzzle
