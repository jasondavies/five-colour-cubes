module
public import Mathlib.Data.Fintype.Prod
public import FiveColour.SmallSupport
@[expose] public section
namespace FiveColour.Physical

/-- Four A-copies, five C-copies and five copies drawn from the B-group.
When x + y ≤ 5, their B-group multiplicities are x, y and 5-x-y. -/
def mixedFamily (x y : ℕ) (i : Fin 14) : Cube := catalogue (mixedRepresentatives
  (if i.val < 4 then 0 else if i.val < 9 then 1 else
   if i.val < 9+x then 2 else if i.val < 9+x+y then 3 else 4))

/-- Overestimate neighbours by allowing each of the last five copies to be
any of the three B-varieties. This proves every distribution at once. -/
def mixedNeighbours (t : Fin 75) : Finset (Fin 14) := Finset.univ.filter fun i =>
  if i.val < 4 then ∃ k ∈ mixedLowerCut t, Fits (catalogue (mixedRepresentatives 0)) (catalogue t) k
  else if i.val < 9 then ∃ k ∈ mixedLowerCut t, Fits (catalogue (mixedRepresentatives 1)) (catalogue t) k
  else ∃ b : Fin 5, 2 ≤ b.val ∧ ∃ k ∈ mixedLowerCut t,
    Fits (catalogue (mixedRepresentatives b)) (catalogue t) k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_deficit (t : Fin 75) : (mixedNeighbours t).card < (mixedLowerCut t).card := by
  fin_cases t <;> decide +kernel

lemma mixed_neighbours_subset (x y : ℕ) (t : Fin 75) :
    neighbours (mixedFamily x y) (catalogue t) (mixedLowerCut t) ⊆ mixedNeighbours t := by
  intro i hi
  obtain ⟨k,hk,hfit⟩ := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  unfold mixedFamily at hfit
  split_ifs at hfit ⊢ with h4 h9 hx hxy
  · exact ⟨k,hk,hfit⟩
  · exact ⟨k,hk,hfit⟩
  · exact ⟨2,by decide,k,hk,hfit⟩
  · exact ⟨3,by decide,k,hk,hfit⟩
  · exact ⟨4,by decide,k,hk,hfit⟩

theorem mixed_no_solution (x y : ℕ) : ¬ HasSolution (mixedFamily x y) := by
  intro h
  obtain ⟨t,p,hp⟩ := (hasSolution_iff_catalogue _).mp h
  have hle := (solution_card_le _ _ p hp (mixedLowerCut t)).trans
    (Finset.card_le_card (mixed_neighbours_subset x y t))
  exact Nat.not_le_of_gt (mixed_deficit t) hle

theorem mixed_uses_all (x y : ℕ) : ∀ i, UsesAllColours (mixedFamily x y i) :=
  fun _ => catalogue_uses_all_colours _

set_option maxRecDepth 100000 in
theorem mixed_representatives_faces :
    (fun i => catalogue (mixedRepresentatives i)) =
      ![![0,0,1,2,3,4],![0,3,1,2,4,1],![0,1,2,3,2,4],![0,1,2,3,3,4],![0,1,2,4,3,4]] := by
  decide +kernel

theorem mixed_distribution_count :
    ((Finset.univ : Finset (Fin 6 × Fin 6)).filter fun p => p.1.val+p.2.val ≤ 5).card = 21 := by
  decide +kernel

end FiveColour.Physical
