module
public import FiveColour.CaseCoverage
@[expose] public section
namespace FiveColour.Physical

/-- The integer problem for one root: the empty and total-mass constraints,
the anchor Hall budget, and the 75 target Hall families, in archive order. -/
def rootProblem (r : Fin 357) : Certificate.Problem 75 78 where
  goal := 15
  alternatives t :=
    if h0 : t.val = 0 then [⟨∅, 0⟩]
    else if h1 : t.val = 1 then [⟨Finset.univ, 15⟩]
    else if h2 : t.val = 2 then [⟨rootBad (rootCapacity r), (rootCapacity r).budget⟩]
    else Replay.hallCuts ⟨t.val-3, by omega⟩

/-- A physical counterexample satisfying a root's premises satisfies all 78
families of its integer problem, not merely its coordinate bounds. -/
theorem counterexample_root_admissible (cubes : Fin 15 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (r : Fin 357) (hp : RootPremises cubes r) :
    (rootProblem r).Admissible (multiplicityVector cubes) := by
  refine ⟨multiplicity_total cubes, ?_⟩
  intro t
  dsimp only [rootProblem]
  split
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp [Certificate.Cut.Holds, Certificate.mass]
  · split
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact (multiplicity_total cubes).le
    · split
      · exact ⟨_, List.mem_singleton_self _, hp.2.2⟩
      · exact (counterexample_iff_hallCuts cubes hc).mp h ⟨t.val-3, by omega⟩

/-- Every hypothetical fifteen-cube counterexample produces an admissible
integer vector in one of the 357 exported root boxes, with no selection premises. -/
theorem counterexample_integer_root (cubes : Fin 15 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes) :
    ∃ (r : Fin 357) (x : Certificate.Vector 75),
      (rootBox (rootCapacity r)).Contains x ∧ (rootProblem r).Admissible x := by
  obtain ⟨a, s, r, hc', h', hp, hb⟩ := physical_root_cover cubes hc (by decide) h
  exact ⟨r, _, hb, counterexample_root_admissible _ hc' h' r hp⟩

/-- The remaining finite obligation is exclusion of these integer root problems.
Together with case coverage, their exclusion implies the physical threshold. -/
theorem threshold_of_integer_root_exclusions
    (hexclude : ∀ (r : Fin 357) (x : Certificate.Vector 75),
      (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x) :
    Threshold15 := by
  intro cubes hc
  by_contra h
  obtain ⟨r, x, hb, hp⟩ := counterexample_integer_root cubes hc h
  exact hexclude r x hb hp

end FiveColour.Physical
