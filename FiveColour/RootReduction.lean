module
public import FiveColour.RootReductionChecks
public import FiveColour.ArchiveBridge
@[expose] public section

namespace FiveColour.Physical

/-- Recover the original 357-root interface from just the 279 remaining exclusions. -/
theorem root_exclusions_of_reduced
    (h : ∀ r ∈ replayRoots, ∀ x, (rootBox (rootCapacity r)).Contains x →
      ¬ (rootProblem r).Admissible x) :
    ∀ r x, (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x := by
  intro r
  apply (representative_contains r).exclusion
  by_cases ha : rootRepresentative r ∈ arithmeticRoots
  · exact arithmetic_root_excluded _ ha
  · exact h _ (Finset.mem_sdiff.mpr ⟨representative_mem r, ha⟩)

/-- A physical counterexample must lie in one of the 279 remaining integer roots. -/
theorem counterexample_reduced_root (cubes : Fin 15 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes) :
    ∃ r ∈ replayRoots, ∃ x : Certificate.Vector 75,
      (rootBox (rootCapacity r)).Contains x ∧ (rootProblem r).Admissible x := by
  obtain ⟨r, x, hx, hp⟩ := counterexample_integer_root cubes hc h
  obtain ⟨hx', hp'⟩ := (representative_contains r).transport hx hp
  have ha : rootRepresentative r ∉ arithmeticRoots := by
    intro ha
    exact arithmetic_root_excluded _ ha x hx' hp'
  exact ⟨_, Finset.mem_sdiff.mpr ⟨representative_mem r, ha⟩, x, hx', hp'⟩

/-- The same physical threshold now has only 279 finite exclusion hypotheses. -/
theorem threshold_of_reduced_root_exclusions
    (h : ∀ r ∈ replayRoots, ∀ x, (rootBox (rootCapacity r)).Contains x →
      ¬ (rootProblem r).Admissible x) : Threshold15 :=
  threshold_of_integer_root_exclusions (root_exclusions_of_reduced h)

end FiveColour.Physical

namespace FiveColour.Packed.Archive
open Physical

/-- Reuse unchanged archive headers and any completed certificates for the 279 roots. -/
theorem threshold_of_reduced_exclusions
    (h : ∀ r ∈ replayRoots, Chunks.Excludes 15 (families r) (root r)) : Threshold15 :=
  threshold_of_reduced_root_exclusions fun r hr => integer_exclusion r (h r hr)

/-- The physical lower bound combines with the reduced upper-bound interface. -/
theorem sharp_threshold_of_reduced_exclusions
    (h : ∀ r ∈ replayRoots, Chunks.Excludes 15 (families r) (root r)) : SharpThreshold15 :=
  ⟨threshold_of_reduced_exclusions h, lower_bound.2⟩

end FiveColour.Packed.Archive
