module
public import FiveColour.CaseProblem
public import FiveColour.ExtremalMultiplicity
@[expose] public section
namespace FiveColour.Physical.Classification

def eligibleRoots : Finset (Fin 357) :=
  Finset.univ.filter fun r => (rootCapacity r).copies.val ≤ 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eligibleRoots_card : eligibleRoots.card = 349 := by decide +kernel

/-- Existing physical coverage applies at fourteen, independently of Threshold15.
The independent multiplicity lemma discards precisely the eight roots with
anchor multiplicity six or seven. The symmetry-transformed physical copies
are retained explicitly for the eventual orbit-classification bridge. -/
theorem physical_reduction (cubes : Fin 14 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes) :
    ∃ (a : Fin 75) (s : PuzzleSymmetry) (r : Fin 357),
      let transformed := fun q => s.apply ((anchorSymmetry a).apply (cubes q))
      (∀ q, UsesAllColours (transformed q)) ∧
      ¬ HasSolution transformed ∧
      (rootCapacity r).copies.val ≤ 5 ∧
      (rootBox (rootCapacity r)).Contains (multiplicityVector transformed) ∧
      (caseProblem r (rootCapacity r).budget 14).Admissible
        (multiplicityVector transformed) := by
  obtain ⟨a, s, r, hc', h', hp, hb⟩ := physical_root_cover cubes hc (by decide) h
  refine ⟨a, s, r, hc', h', ?_, hb, ?_⟩
  · rw [← hp.1]
    exact fourteen_multiplicity_le_five _ hc' h' _
  · exact (caseProblem_admissible_iff r _ _ _).mpr
      ⟨multiplicity_total _, hp.2.2, (counterexample_iff_hallCuts _ hc').mp h'⟩


end FiveColour.Physical.Classification
