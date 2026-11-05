module
public import FiveColour.ExtremalTripleData
@[expose] public section
namespace FiveColour.Physical

def extremalFamily (j : Fin 5) : Fin 14 → Cube :=
  tripleFamily 0 (extremalB j) (extremalC j)

lemma extremal_uses_all (j : Fin 5) : ∀ i, UsesAllColours (extremalFamily j i) :=
  triple_uses_all _ _ _

lemma extremal_distinct : ∀ j : Fin 5,
    (0 : Fin 75) ≠ extremalB j ∧ (0 : Fin 75) ≠ extremalC j ∧ extremalB j ≠ extremalC j := by
  decide +kernel

lemma extremal_multiplicity (j : Fin 5) (i : Fin 75) :
    multiplicity (extremalFamily j) i =
      if i = 0 then 4 else if i = extremalB j then 5 else if i = extremalC j then 5 else 0 :=
  triple_multiplicity _ _ _ (extremal_distinct j).1 (extremal_distinct j).2.1
    (extremal_distinct j).2.2 i

def tripleMaskNeighbours (a b c t : Fin 75) (d : ℕ) : Finset (Fin 14) :=
  Finset.univ.filter fun i => (Replay.fits t (tripleVariety a b c i)).land d ≠ 0

lemma tripleMaskNeighbours_eq (a b c t : Fin 75) (d : ℕ) (hd : d < 256) :
    tripleMaskNeighbours a b c t d = neighbours (tripleFamily a b c) (catalogue t) (cornerSet d) := by
  ext i
  simp only [tripleMaskNeighbours, neighbours, Finset.mem_filter, Finset.mem_univ, true_and,
    mask_overlap_iff _ _ hd, cornerSet, tripleFamily, incidence_fits]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extremal_deficits (j : Fin 5) : ∀ t : Fin 75,
    extremalDeficit j t < 256 ∧
    (tripleMaskNeighbours 0 (extremalB j) (extremalC j) t (extremalDeficit j t)).card <
      (cornerSet (extremalDeficit j t)).card := by
  fin_cases j <;> decide +kernel

/-- Each of the five representatives fails, with a Hall deficiency at every target. -/
theorem extremal_no_solution (j : Fin 5) : ¬ HasSolution (extremalFamily j) := by
  apply (not_hasSolution_iff_hall _).mpr
  intro t
  refine ⟨cornerSet (extremalDeficit j t), ?_⟩
  unfold extremalFamily
  rw [← tripleMaskNeighbours_eq _ _ _ _ _ (extremal_deficits j t).1]
  exact (extremal_deficits j t).2

set_option maxRecDepth 100000 in
lemma extremal_support (j : Fin 5) : (varietySupport (extremalFamily j)).card = 3 := by
  unfold varietySupport extremalFamily tripleFamily
  simp only [catalogue_index_faces]
  fin_cases j <;> decide +kernel

end FiveColour.Physical
