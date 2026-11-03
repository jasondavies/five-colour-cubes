module
public import FiveColour.ProjectionPool
public import FiveColour.HallCover
@[expose] public section
namespace FiveColour.Physical.Projection

/-- The unbalanced eight-plus-three case, expressed in terms of source copies. -/
theorem unbalanced {I : Type*} [Fintype I] [DecidableEq I]
    (p : Fin 10) (source : I → Fin 75) (F : Finset I) (typeOf : I → Fin 9)
    (hF : F.card = 8) (hI : 11 ≤ Fintype.card I)
    (htype : ∀ i ∈ F, source i = Ring.variety p (typeOf i))
    (sign : Fin 2) (t : Fin 9) (ht : side sign t)
    (hP : 5 ≤ (F.filter fun i => side sign (typeOf i)).card)
    (hstrong : 2 ≤ (F.filter fun i => typeOf i = t).card) :
    ∃ target : Fin 9, ∃ f : Fin 8 ↪ I,
      ∀ k, Physical.Fits (catalogue (source (f k))) (catalogue (Ring.variety p target)) k := by
  classical
  let P := F.filter fun i => side sign (typeOf i)
  change 5 ≤ P.card at hP
  let strong := F.filter fun i => typeOf i = t
  let fits := fun i k => Physical.Fits (catalogue (source i)) (catalogue (Ring.variety p t)) k
  by_cases hmatch : ∃ f : Fin 8 ↪ I, ∀ k, fits (f k) k
  · exact ⟨t,hmatch⟩
  have hPs : P ⊆ F := Finset.filter_subset _ _
  have hpos : ∀ i ∈ P, ∀ j, Fits p sign (source i) j := by
    intro i hi j
    rw [htype i (Finset.mem_filter.mp hi).1]
    exact family_side p sign _ (Finset.mem_filter.mp hi).2 j
  obtain ⟨U,R,hR,hbound,hcover⟩ := FrameHall.cover_of_failure fits
    (adjacentEmbedding p sign t ht) P strong hstrong
    (fun i hi j => (fits_correct p sign t j (Or.inl ht) _).mp (hpos i hi j))
    (by
      intro i hi k
      have hi' := Finset.mem_filter.mp hi
      dsimp [fits]
      rw [htype i hi'.1,hi'.2]
      exact fits_self _ k) hmatch
  have hu : U.card < 3 := by omega
  let u : Fin 3 := ⟨U.card,hu⟩
  let A := Finset.univ \ (P ∪ R)
  let J := F \ (P ∪ R)
  have hJA : J ⊆ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hi).2⟩
  have hcardUnion : (P ∪ R).card ≤ P.card+R.card := Finset.card_union_le _ _
  have hA : 4+u.val ≤ A.card := by
    have hc := Finset.card_sdiff_of_subset (Finset.subset_univ (P ∪ R))
    simp only [Finset.card_univ] at hc
    change 4+U.card ≤ (Finset.univ \ (P ∪ R)).card
    omega
  have hJ : u.val+1 ≤ J.card := by
    have hc := Finset.card_sdiff_add_card (s := F) (t := P ∪ R)
    have hl := Finset.card_le_card (Finset.subset_union_left (s₁ := F) (s₂ := P ∪ R))
    change U.card+1 ≤ (F \ (P ∪ R)).card
    omega
  have hcount : ∀ i ∈ A, count p sign (source i) ≤ u.val := by
    intro i hi
    apply Finset.card_le_card
    intro j hj
    apply hcover i hi j
    exact (fits_correct p sign t j (Or.inl ht) _).mp (Finset.mem_filter.mp hj).2
  have hnegative : ∀ i ∈ J, side (other sign) (typeOf i) := by
    intro i hi
    have hiF := (Finset.mem_sdiff.mp hi).1
    have hiP : i ∉ P := fun hp => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hp)
    have hs : ¬ side sign (typeOf i) := fun hs => hiP (Finset.mem_filter.mpr ⟨hiF,hs⟩)
    rcases family_not_side sign _ hs with ho | hn
    · have hh := hcount i (hJA hi)
      rw [htype i hiF,family_opposite_count p sign _ ho] at hh
      have := u.isLt; omega
    · exact hn
  obtain ⟨r,f,hf⟩ := match_half p (other sign) source A J u hJA hA hJ
    (by intro i hi j; rw [htype i (Finset.mem_sdiff.mp hi).1]; exact family_side p _ _ (hnegative i hi) j)
    (fun i hi => profile_bounds p sign _ u (hcount i hi))
  let positions : Half r ↪ Fin 8 :=
    ⟨fun j => halfSlot p sign r (.inr j),fun a b he => Sum.inr_injective ((halfSlot_bijective p sign r).injective he)⟩
  have hfphysical (j) : Physical.Fits (catalogue (source (f j)))
      (catalogue (Ring.variety p (target r))) (positions j) :=
    (fits_correct p (other sign) (target r) j.val (present_half _ _ j) _).mp (hf j).2
  have hpool : ∀ i ∈ P, ∀ k : Fin 8, k ∉ Set.range positions →
      Physical.Fits (catalogue (source i)) (catalogue (Ring.variety p (target r))) k := by
    intro i hi k hk
    obtain ⟨z,hz⟩ := (halfSlot_bijective p sign r).surjective k
    cases z with
    | inl j =>
      rw [← hz]
      exact (fits_correct p sign (target r) j.val (present_half _ _ j) _).mp (hpos i hi j.val)
    | inr j => exact False.elim (hk ⟨j,hz⟩)
  obtain ⟨g,hg⟩ := FrameHall.complete_with_pool
    (fun i k => Physical.Fits (catalogue (source i)) (catalogue (Ring.variety p (target r))) k)
    positions f hfphysical P (by rw [Fintype.card_fin,half_card]; omega) hpool
    (fun j hp => (Finset.mem_sdiff.mp (hf j).1).2 (Finset.mem_union_left _ hp))
  exact ⟨target r,g,hg⟩
end FiveColour.Physical.Projection
