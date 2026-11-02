module
public import FiveColour.CaseCoverage
@[expose] public section
namespace FiveColour.Physical

/-- The shared integer problem for an original or projected root. The empty
and total cuts, anchor budget and 75 Hall families retain archive order. -/
def caseProblem (r : Fin 357) (budget total : Nat) : Certificate.Problem 75 78 where
  goal := total
  alternatives t :=
    if h0 : t.val = 0 then [⟨∅, 0⟩]
    else if h1 : t.val = 1 then [⟨Finset.univ, total⟩]
    else if h2 : t.val = 2 then [⟨rootBad (rootCapacity r), budget⟩]
    else Replay.hallCuts ⟨t.val-3, by omega⟩

/-- Admissibility consists of the prescribed total, budget and target failures. -/
lemma caseProblem_admissible_iff (r : Fin 357) (budget total : Nat)
    (x : Certificate.Vector 75) :
    (caseProblem r budget total).Admissible x ↔
      Certificate.mass x Finset.univ = (total : Int) ∧
      Certificate.mass x (rootBad (rootCapacity r)) ≤ (budget : Int) ∧
      ∀ t, ∃ c ∈ Replay.hallCuts t, c.Holds x := by
  constructor
  · rintro ⟨ht, hc⟩
    refine ⟨ht, ?_, ?_⟩
    · have h := hc 2
      change ∃ c : Certificate.Cut 75,
        c ∈ [⟨rootBad (rootCapacity r), budget⟩] ∧ c.Holds x at h
      simpa only [List.mem_singleton, exists_eq_left, Certificate.Cut.Holds] using h
    · intro t
      have h := hc ⟨t.val + 3, by omega⟩
      have h0 : t.val + 3 ≠ 0 := by omega
      have h1 : t.val + 3 ≠ 1 := by omega
      have h2 : t.val + 3 ≠ 2 := by omega
      simpa only [caseProblem, h0, h1, h2, ↓reduceDIte, Nat.add_sub_cancel, Fin.eta] using h
  · rintro ⟨ht, hb, hh⟩
    refine ⟨ht, fun t => ?_⟩
    dsimp only [caseProblem]
    split
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp [Certificate.Cut.Holds, Certificate.mass]
    · split
      · exact ⟨_, List.mem_singleton_self _, ht.le⟩
      · split
        · exact ⟨_, List.mem_singleton_self _, hb⟩
        · exact hh ⟨t.val - 3, by omega⟩

/-- The original fifteen-copy problem is a specialisation of `caseProblem`. -/
def rootProblem (r : Fin 357) : Certificate.Problem 75 78 :=
  caseProblem r (rootCapacity r).budget 15

/-- A physical counterexample satisfying a root's premises satisfies all 78
families of its integer problem, not merely its coordinate bounds. -/
theorem counterexample_root_admissible (cubes : Fin 15 → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (r : Fin 357) (hp : RootPremises cubes r) :
    (rootProblem r).Admissible (multiplicityVector cubes) := by
  exact (caseProblem_admissible_iff r _ _ _).mpr
    ⟨multiplicity_total cubes, hp.2.2, (counterexample_iff_hallCuts cubes hc).mp h⟩

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
