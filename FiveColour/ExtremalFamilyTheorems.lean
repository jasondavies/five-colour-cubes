module
public import FiveColour.ExtremalFamilyData
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- A single deficient enlarged graph covers all distributions in each support pattern. -/
theorem uniform_no_solution (p : Fin 4) (v : Fin 14 → Fin 75)
    (hv : ∀ i, familyAllowed p i (v i)) : ¬ HasSolution (fun i => catalogue (v i)) := by
  apply (not_hasSolution_iff_hall _).mpr
  intro t
  refine ⟨cornerSet (uniformDeficit p t), lt_of_le_of_lt (Finset.card_le_card ?_) (uniform_deficits p t).2⟩
  intro i hi
  obtain ⟨k,hk,hfit⟩ := (Finset.mem_filter.mp hi).2
  have hm : (Replay.fits t (v i)).land (uniformDeficit p t) ≠ 0 :=
    (mask_overlap_iff _ _ (uniform_deficits p t).1).mpr
      ⟨k, (Finset.mem_filter.mp hk).2, (incidence_fits _ _ _).mpr hfit⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have h := hv i
  unfold familyAllowed at h
  split_ifs at h ⊢ with h4 h9
  · simpa only [h] using hm
  · obtain ⟨r,hr,he⟩ := h
    exact ⟨r,hr,by simpa only [he] using hm⟩
  · obtain ⟨r,hr,he⟩ := h
    exact ⟨r,hr,by simpa only [he] using hm⟩

lemma disjoint_patterns (x y : Fin 3 → ℕ) (hxy : disjointRepeats x y) :
    ∃ p : Fin 4, (∀ r, 0 < x r → r ∈ familyBAllowed p) ∧
      (∀ r, 0 < y r → r ∈ familyCAllowed p) := by
  obtain ⟨h2,h4⟩ := hxy
  by_cases h0 : x 0 = 0 <;> by_cases h2' : x 2 = 0
  · refine ⟨3, ?_, ?_⟩ <;> intro r hr <;> fin_cases r <;> simp_all [familyBAllowed, familyCAllowed]
  · refine ⟨2, ?_, ?_⟩ <;> intro r hr <;> fin_cases r <;> simp_all [familyBAllowed, familyCAllowed]
  · refine ⟨1, ?_, ?_⟩ <;> intro r hr <;> fin_cases r <;> simp_all [familyBAllowed, familyCAllowed]
  · refine ⟨0, ?_, ?_⟩ <;> intro r hr <;> fin_cases r <;> simp_all [familyBAllowed, familyCAllowed]

/-- Five sources in each adjacent cut fail when their repeat supports are disjoint. -/
theorem generalized_no_solution (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 5) (hy : ∑ i, y i = 5) (hxy : disjointRepeats x y) :
    ¬ HasSolution (generalizedFamily x y) := by
  obtain ⟨p,hb,hc⟩ := disjoint_patterns x y hxy
  apply uniform_no_solution p (generalizedVariety x y)
  intro i
  unfold familyAllowed generalizedVariety
  split_ifs with h4 h9
  · rfl
  · exact ⟨_, hb _ (distributionType_positive x hx _ (by omega)), rfl⟩
  · exact ⟨_, hc _ (distributionType_positive y hy _ (by omega)), rfl⟩

lemma generalized_uses_all (x y : Fin 3 → ℕ) :
    ∀ i, UsesAllColours (generalizedFamily x y i) := fun _ => catalogue_uses_all_colours _

/-- A shared repeat supplies the two bicolours; the other four B copies and two
anchor copies fill the six tricoloured positions. Only two geometric templates are needed. -/
lemma generalized_shared_solves (x y : Fin 3 → ℕ) (hx : ∑ i, x i = 5)
    (hy : ∑ i, y i = 5) (r : Fin 2)
    (hb : 0 < x (completionB r)) (hc : 0 < y (completionC r)) :
    HasSolution (generalizedFamily x y) := by
  obtain ⟨b,hb⟩ := distributionType_witness x hx _ hb
  obtain ⟨c,hc⟩ := distributionType_witness y hy _ hc
  obtain ⟨f,hf⟩ := Reserve.allocate (familyCompletion r).group
    (sourcePools (completionTag b c)) (sourcePools_disjoint _) (fun g => by
      simpa only [Fintype.card_subtype, completion_pools_card] using family_completion_capacity r g)
  apply (hasSolution_iff_catalogue _).mpr
  refine ⟨(familyCompletion r).target, f, ?_⟩
  intro k
  apply (incidence_fits _ _ _).mp
  apply family_completion_fits r k
  have htag := (Finset.mem_filter.mp (hf k)).2
  unfold completionTag at htag
  unfold generalizedVariety
  split_ifs at htag ⊢ with h4 h9 hbe hce
  · exact Or.inl ⟨(Option.some.inj htag).symm, rfl⟩
  · exact Or.inr (Or.inl ⟨(Option.some.inj htag).symm, by rw [hbe,hb]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(Option.some.inj htag).symm, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(Option.some.inj htag).symm, by rw [hce,hc]⟩))

/-- Exact classification within the two-cut, four-anchor family. -/
theorem generalized_no_solution_iff (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 5) (hy : ∑ i, y i = 5) :
    ¬ HasSolution (generalizedFamily x y) ↔ disjointRepeats x y := by
  refine ⟨?_, generalized_no_solution x y hx hy⟩
  intro hno
  by_contra h
  simp only [disjointRepeats, not_and_or, Nat.mul_eq_zero, not_or] at h
  rcases h with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · exact hno (generalized_shared_solves x y hx hy 0 (by simpa [completionB] using Nat.pos_of_ne_zero hb)
      (by simpa [completionC] using Nat.pos_of_ne_zero hc))
  · exact hno (generalized_shared_solves x y hx hy 1 (by simpa [completionB] using Nat.pos_of_ne_zero hb)
      (by simpa [completionC] using Nat.pos_of_ne_zero hc))

end FiveColour.Physical
