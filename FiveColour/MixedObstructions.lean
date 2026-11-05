module
public import Mathlib.Data.Fintype.Prod
public import FiveColour.ExtremalFamilyTheorems
public import FiveColour.SupportData
@[expose] public section
namespace FiveColour.Physical

/-- Four A-copies, five C-copies and five copies drawn from the B-group.
When x + y ≤ 5, their B-group multiplicities are x, y and 5-x-y. -/
def mixedFamily (x y : ℕ) (i : Fin 14) : Cube := catalogue (mixedRepresentatives
  (if i.val < 4 then 0 else if i.val < 9 then 1 else
   if i.val < 9+x then 2 else if i.val < 9+x+y then 3 else 4))

private def swapFamilyBlocks : Fin 14 → Fin 14 :=
  ![0,1,2,3,9,10,11,12,13,4,5,6,7,8]

private lemma swapFamilyBlocks_involution : Function.Involutive swapFamilyBlocks := by
  intro i
  fin_cases i <;> rfl

/-- The original family is the first uniform support pattern, for arbitrary x,y.
The definition itself clamps the B blocks to the five available physical copies. -/
theorem mixed_no_solution (x y : ℕ) : ¬ HasSolution (mixedFamily x y) := by
  let v := fun i : Fin 14 => mixedRepresentatives
    (if i.val < 4 then 0 else if i.val < 9 then 1 else
      if i.val < 9+x then 2 else if i.val < 9+x+y then 3 else 4)
  have hu : ¬ HasSolution (fun i => catalogue (v (swapFamilyBlocks i))) := by
    apply uniform_no_solution 0
    intro i
    fin_cases i <;> simp only [familyAllowed, swapFamilyBlocks, v, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
      Fin.isValue, Nat.reduceLT, ↓reduceIte]
    all_goals simp [familyBAllowed, familyCAllowed, mixedRepresentatives,
      extremalBGroup, extremalCGroup]
    all_goals split_ifs <;> decide +kernel
  intro h
  obtain ⟨t,p,hp⟩ := (hasSolution_iff_catalogue _).mp h
  apply hu
  apply (hasSolution_iff_catalogue _).mpr
  let e : Fin 14 ↪ Fin 14 := ⟨swapFamilyBlocks, swapFamilyBlocks_involution.injective⟩
  refine ⟨t,p.trans e,?_⟩
  intro k
  change Fits (catalogue (v (swapFamilyBlocks (swapFamilyBlocks (p k))))) (catalogue t) k
  rw [swapFamilyBlocks_involution]
  exact hp k

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
