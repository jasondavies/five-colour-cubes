module
public import FiveColour.Matching
public import FiveColour.LowerData
@[expose] public section
namespace FiveColour.Physical

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The 75 small Hall obstructions are verified on physical faces. -/
theorem lower_hall_deficit (t : Fin 75) :
    (neighbours lowerFamily (catalogue t) (lowerCut t)).card < (lowerCut t).card := by
  fin_cases t <;> decide +kernel

/-- Four copies of A, five of B and five of C admit no five-colour target. -/
theorem lower_no_solution : ¬ HasSolution lowerFamily := by
  rintro ⟨target, ht, copies, hfits⟩
  obtain ⟨t, r, hr⟩ := catalogue_complete target ht
  have he : target = rotate (catalogue t) r := funext hr
  rw [he] at hfits
  obtain ⟨copies', hfits'⟩ := unrotate_solution lowerFamily (catalogue t) r copies hfits
  exact (Nat.not_le_of_gt (lower_hall_deficit t))
    (solution_card_le lowerFamily (catalogue t) copies' hfits' (lowerCut t))

/-- A physical fourteen-cube counterexample, including palette validity. -/
theorem lower_bound : (∀ i, UsesAllColours (lowerFamily i)) ∧ ¬ HasSolution lowerFamily :=
  ⟨lower_uses_all_colours, lower_no_solution⟩

end FiveColour.Physical
