module
public import FiveColour.Catalogue
public import FiveColour.Geometry
public import FiveColour.LowerData
@[expose] public section
namespace FiveColour.Physical
open ThreeColour.Geometry

/-- Compute compatibility through the verified corner criterion. -/
instance (c t : Cube) (k : Fin 8) : Decidable (Fits c t k) :=
  decidable_of_iff (∃ l, CyclicEq (corner c l) (corner t k)) (fits_iff_corner c t k).symm

/-- Physical copies that can serve at least one corner in K. -/
def neighbours {n : Nat} (cubes : Fin n → Cube) (t : Cube) (K : Finset (Fin 8)) :
    Finset (Fin n) := Finset.univ.filter fun i => ∃ k ∈ K, Fits (cubes i) t k

/-- Any assignment of distinct physical copies satisfies Hall's necessary inequality. -/
theorem solution_card_le {n : Nat} (cubes : Fin n → Cube) (t : Cube)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, Fits (cubes (copies k)) t k)
    (K : Finset (Fin 8)) : K.card ≤ (neighbours cubes t K).card := by
  apply Finset.card_le_card_of_injOn copies
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, h k⟩
  · exact fun _ _ _ _ he => copies.injective he

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
