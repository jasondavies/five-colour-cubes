module
public import FiveColour.UniversalGeometry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Distinct suppliers for any two bicoloured demands of a fixed repeated colour. -/
lemma universal_pair_suppliers {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes)
    (r : Fin 5) (z : Fin 6) :
    ∃ i j : Fin n, i ≠ j ∧
      universalPairFirst z ∈ universalBiTypes (catalogueIndex (cubes i)) r ∧
      universalPairSecond z ∈ universalBiTypes (catalogueIndex (cubes j)) r := by
  obtain ⟨ha, hk, hg⟩ := universal_pair_geometry r z
  obtain ⟨copies, hfits⟩ := (ColourCubes.builds_iff_tableFits _ _).mp
    (hu _ (catalogue_uses_all_colours _) ha)
  refine ⟨copies (universalPairPosition r z 0), copies (universalPairPosition r z 1),
    fun h => hk (copies.injective h), ?_, ?_⟩
  · exact (hg _).1.mp ((incidence_fits _ _ _).mpr
      ((fits_catalogueIndex _ (hc _) _ _).mp (hfits _)))
  · exact (hg _).2.mp ((incidence_fits _ _ _).mpr
      ((fits_catalogueIndex _ (hc _) _ _).mp (hfits _)))

/-- At least three adjacent-repeat sources of each repeated colour are necessary. -/
theorem universal_three_per_colour {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes)
    (r : Fin 5) :
    3 ≤ (Finset.univ.filter fun i => universalSourceClass (catalogueIndex (cubes i)) = r.castSucc).card := by
  classical
  let S := Finset.univ.filter fun i => universalSourceClass (catalogueIndex (cubes i)) = r.castSucc
  have mem (i : Fin n) (p : Fin 4) (hp : p ∈ universalBiTypes (catalogueIndex (cubes i)) r) :
      i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (universal_bi_types _ r).2 ⟨p,hp⟩⟩
  by_contra hn
  change ¬ 3 ≤ S.card at hn
  have hcard : S.card ≤ 2 := by omega
  obtain ⟨i,j,hij,hi,hj⟩ := universal_pair_suppliers cubes hc hu r 0
  have he : ({i,j} : Finset (Fin n)) = S := Finset.eq_of_subset_of_card_le
    (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem _ _ hi
        · exact mem _ _ hj)
    (by simpa [hij] using hcard)
  have cover (x : Fin n) (p : Fin 4) (hp : p ∈ universalBiTypes (catalogueIndex (cubes x)) r) :
      x = i ∨ x = j := by
    have hx := mem x p hp
    rw [← he] at hx
    simpa using hx
  obtain ⟨z,h₁,h₂⟩ := universal_two_insufficient
    (universalBiTypes (catalogueIndex (cubes i)) r)
    (universalBiTypes (catalogueIndex (cubes j)) r)
    (universal_bi_types _ r).1 (universal_bi_types _ r).1
  obtain ⟨x,y,hxy,hx,hy⟩ := universal_pair_suppliers cubes hc hu r z
  rcases cover x _ hx with rfl | rfl <;> rcases cover y _ hy with rfl | rfl
  · exact hxy rfl
  · exact h₁ ⟨hx,hy⟩
  · exact h₂ ⟨hx,hy⟩
  · exact hxy rfl

/-- The lower bound already holds when only adjacent-repeat targets are prescribed. -/
theorem adjacent_universal_minimum {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes) : 15 ≤ n := by
  let count (r : Fin 6) :=
    (Finset.univ.filter fun i => universalSourceClass (catalogueIndex (cubes i)) = r).card
  have total : ∑ r : Fin 6, count r = n := by
    dsimp [count]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have lower : 15 ≤ ∑ r : Fin 5, count r.castSucc := by
    calc
      15 = ∑ _ : Fin 5, 3 := by decide
      _ ≤ _ := Finset.sum_le_sum fun r _ => universal_three_per_colour cubes hc hu r
  rw [Fin.sum_univ_castSucc] at total
  omega

/-- All prescribed targets, with arbitrary proper orientation, are built by the cyclic pool. -/
theorem universal_family_builds : Submission.Universal Submission.universalFamily := by
  intro target ht
  obtain ⟨t,r,hr⟩ := catalogue_complete target ht
  have solved : ColourCubes.Builds Submission.universalFamily (catalogue t) := by
    apply (ColourCubes.builds_iff_tableFits _ _).mpr
    refine ⟨⟨universalPlacement t, (universal_placements t).1⟩, fun k => ?_⟩
    apply (fits_catalogueIndex _ (universal_sources _).1 _ _).mpr
    rw [(universal_sources _).2.1]
    exact (incidence_fits _ _ _).mp ((universal_placements t).2 k)
  have he : target = rotate (catalogue t) r := funext hr
  rw [he]
  exact (ColourCubes.builds_rotate _ _ _).mpr solved

end FiveColour.Physical
