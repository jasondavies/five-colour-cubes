module
public import FiveColour.ExtremalFamilyTheorems
public import FiveColour.SmallSupport
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

/-- The five concentrated distributions are instances of the uniform support patterns. -/
theorem extremal_no_solution (j : Fin 5) : ¬ HasSolution (extremalFamily j) := by
  let p : Fin 4 := ![0,1,0,2,2] j
  apply uniform_no_solution p (tripleVariety 0 (extremalB j) (extremalC j))
  fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
lemma extremal_support (j : Fin 5) : (varietySupport (extremalFamily j)).card = 3 := by
  unfold varietySupport extremalFamily tripleFamily
  simp only [catalogue_index_faces]
  fin_cases j <;> decide +kernel

end FiveColour.Physical
