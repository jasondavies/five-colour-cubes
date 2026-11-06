module
public import FiveColour.Classification56
public import FiveColour.SubmissionBridge
@[expose] public section
namespace FiveColour.Submission

/-- There are exactly fifty-six classes of failing fourteen-cube collections
under common colour relabelling and simultaneous reflection. -/
theorem complete_extremal_classification :
    ∃ representatives : Fin 56 → Fin 14 → Cube,
      (∀ j i, UsesAllColours (representatives j i)) ∧
      (∀ j, ¬ HasSolution (representatives j)) ∧
      (∀ cubes : Fin 14 → Cube, (∀ i, UsesAllColours (cubes i)) →
        (¬ HasSolution cubes ↔ ∃! j : Fin 56, Equivalent cubes (representatives j))) := by
  refine ⟨Physical.Classification.representative,
    Physical.Classification.representative_valid, ?_, ?_⟩
  · intro j h
    exact Physical.Classification.representative_fails j ((Puzzle.hasSolution_iff _).mp h)
  · intro cubes hc
    simpa only [Puzzle.hasSolution_iff,
      equivalent_iff cubes _ hc (Physical.Classification.representative_valid _)] using
      Physical.Classification.classification_iff cubes hc
end FiveColour.Submission
