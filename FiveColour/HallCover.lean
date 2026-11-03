module
public import FiveColour.FiniteHall
@[expose] public section
namespace FiveColour.FrameHall
open scoped BigOperators

/-- A failed corner matching produces the small cover used in the
unbalanced eight-plus-three argument, directly from Hall's theorem. -/
theorem cover_of_failure {I : Type*} [Fintype I] [DecidableEq I]
    (fits : I → Fin 8 → Prop) [DecidableRel fits]
    (common : Fin 6 ↪ Fin 8) (pool strong : Finset I)
    (hstrong : 2 ≤ strong.card)
    (hp : ∀ i ∈ pool, ∀ j, fits i (common j))
    (hs : ∀ i ∈ strong, ∀ k, fits i k)
    (hfail : ¬ ∃ f : Fin 8 ↪ I, ∀ k, fits (f k) k) :
    ∃ U : Finset (Fin 6), ∃ R : Finset I,
      R ⊆ Finset.univ \ pool ∧ R.card + U.card + pool.card ≤ 7 ∧
      ∀ i ∈ Finset.univ \ (pool ∪ R), ∀ j, fits i (common j) → j ∈ U := by
  classical
  have hbad : ∃ D : Finset (Fin 8), (neighbours fits D).card < D.card := by
    by_contra hh
    push Not at hh
    exact hfail (match_of_hall fits hh)
  obtain ⟨D,hD⟩ := hbad
  have hn : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k,hk⟩ := hn
  have hS : strong ⊆ neighbours fits D := by
    intro i hi
    simp only [neighbours,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨k,hk,hs i hi k⟩
  have hcommon : ∃ j, common j ∈ D := by
    by_contra hh
    push Not at hh
    have hd : Disjoint D (Finset.univ.image common) := by
      apply Finset.disjoint_left.mpr
      intro k hk he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
      exact hh j hk
    have hbound := Finset.card_le_univ (D ∪ Finset.univ.image common)
    rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ common.injective] at hbound
    simp only [Finset.card_univ,Fintype.card_fin] at hbound
    have := Finset.card_le_card hS
    omega
  obtain ⟨j,hj⟩ := hcommon
  have hP : pool ⊆ neighbours fits D := by
    intro i hi
    simp only [neighbours,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨common j,hj,hp i hi j⟩
  let U := Finset.univ.filter fun j => common j ∉ D
  let R := neighbours fits D \ pool
  have hR : R ⊆ Finset.univ \ pool := fun i hi =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hi).2⟩
  have hcardR : R.card + pool.card = (neighbours fits D).card := Finset.card_sdiff_add_card_eq_card hP
  have hdu : D.card + U.card ≤ 8 := by
    have hd : Disjoint D (U.image common) := by
      apply Finset.disjoint_left.mpr
      intro k hk he
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hj).2 hk
    have hbound := Finset.card_le_univ (D ∪ U.image common)
    rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ common.injective] at hbound
    exact hbound
  refine ⟨U,R,hR,by omega,?_⟩
  intro i hi j hf
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro hj
  have hn : i ∈ neighbours fits D := by
    simp only [neighbours,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨common j,hj,hf⟩
  have hip : i ∉ pool := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)
  exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hn,hip⟩))
end FiveColour.FrameHall
