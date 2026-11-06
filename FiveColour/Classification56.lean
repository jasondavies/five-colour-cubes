module
public import FiveColour.EnumerationCoverage
public import FiveColour.ClassificationReduction
public import FiveColour.ClassificationOrbits
@[expose] public section
namespace FiveColour.Physical.Classification

/-- Exhaustive physical classification, independent of the fifteen-cube
threshold: every failing fourteen-copy pool belongs to one of these classes. -/
theorem complete_classification (cubes : Fin 14 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes) :
    ∃ j : Fin 56, SymmetryEquivalent cubes (representative j) := by
  obtain ⟨a,s,r,hc',h',hr,hb,hp⟩ := physical_reduction cubes hc h
  obtain ⟨i, rfl⟩ := roots_complete r hr
  have hb' := hb
  rw [← Packed.Archive.root_model] at hb'
  have hp' := hp
  rw [← Packed.Enumeration.problem_model] at hp'
  obtain ⟨p,hp,he⟩ := all_roots_covered i _ hb' hp'
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  have hi : SameInventory (fun q => s.apply ((anchorSymmetry a).apply (cubes q)))
      (terminal j) := by
    rw [terminal_model] at he
    intro k
    have hk := congrFun he k
    simp only [multiplicityVector] at hk
    exact_mod_cast hk
  have ht : SymmetryEquivalent cubes (terminal j) :=
    ⟨(anchorSymmetry a).trans s, by simpa only [PuzzleSymmetry.trans_apply] using hi⟩
  exact ⟨terminalClass j, symmetryEquivalent_trans cubes (terminal j) _ hc (terminal_valid j)
    ht (terminal_equivalent j)⟩

/-- A collection fails exactly when it is equivalent to a unique member of
the fifty-six-class list. Copies are physical and equivalence is global. -/
theorem classification_iff (cubes : Fin 14 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) :
    ¬ HasSolution cubes ↔ ∃! j : Fin 56, SymmetryEquivalent cubes (representative j) := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := complete_classification cubes hc h
    refine ⟨j,hj,fun k hk => ?_⟩
    exact representative_inequivalent k j (symmetryEquivalent_trans _ cubes _
      (representative_valid k) hc
      (symmetryEquivalent_symm _ _ hc (representative_valid k) hk) hj)
  · rintro ⟨j,hj,_⟩ hsol
    exact representative_fails j ((symmetryEquivalent_hasSolution cubes _ hc
      (representative_valid j) hj).mp hsol)
end FiveColour.Physical.Classification
