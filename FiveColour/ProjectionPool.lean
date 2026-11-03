module
public import FiveColour.HalfMasks
public import FiveColour.ProjectionGeometry
public import FiveColour.MatchingCompletion
@[expose] public section
namespace FiveColour.Physical.Projection
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma bits_lt : ∀ p sign w, bits p sign w < 64 := by decide +kernel
lemma bounds_antitone : ∀ u j : Fin 3, u ≤ j → ![4,2,1] j ≤ ![4,2,1] u := by decide +kernel

/-- A pool with a few universal negative copies fills one opposite-repeat half.
The other copies need only the signed projection bounds. -/
lemma match_half {I : Type*} [Fintype I] [DecidableEq I]
    (p : Fin 10) (sign : Fin 2) (source : I → Fin 75)
    (A J : Finset I) (u : Fin 3) (hJA : J ⊆ A)
    (hA : 4 + u.val ≤ A.card) (hJ : u.val + 1 ≤ J.card)
    (hall : ∀ i ∈ J, ∀ j, Fits p sign (source i) j)
    (hcounts : ∀ i ∈ A, ![4,2,1] u ≤ count p sign (source i)) :
    ∃ r : Fin 3, ∃ f : Half r ↪ I,
      ∀ j, f j ∈ A ∧ Fits p sign (source (f j)) j.val := by
  classical
  by_cases hj4 : 4 ≤ J.card
  · have hn : Fintype.card (Half (0 : Fin 3)) ≤ Fintype.card J := by rw [half_card,Fintype.card_coe]; exact hj4
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hn
    exact ⟨0,f.trans (Function.Embedding.subtype _),fun j => ⟨hJA (f j).property,hall _ (f j).property _⟩⟩
  let j : Fin 3 := ⟨J.card-1,by omega⟩
  have hj : J.card = j.val+1 := by dsimp [j]; omega
  have hu : u ≤ j := by change u.val ≤ j.val; omega
  have hrest : Fintype.card (Fin (3-j.val)) ≤ Fintype.card ↥(A \ J) := by
    simp only [Fintype.card_fin,Fintype.card_coe,Finset.card_sdiff_of_subset hJA]
    omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le hrest
  let copies : Fin (3-j.val) ↪ I := pick.trans (Function.Embedding.subtype _)
  let masks (i : Fin (3-j.val)) : Fin 64 := ⟨bits p sign (source (copies i)),bits_lt _ _ _⟩
  have hm (i) : ![4,2,1] j ≤ maskCount (masks i) :=
    (bounds_antitone u j hu).trans (hcounts _ (Finset.mem_sdiff.mp (pick i).property).1)
  obtain ⟨r,positions,hfits⟩ := place_masks j masks hm
  obtain ⟨f,hf⟩ := FrameHall.complete_with_pool
    (fun i (k : Half r) => i ∈ A ∧ Fits p sign (source i) k.val)
    positions copies (fun i => ⟨(Finset.mem_sdiff.mp (pick i).property).1,hfits i⟩) J
    (by rw [half_card,Fintype.card_fin]; have := j.isLt; omega)
    (fun i hi k _ => ⟨hJA hi,hall i hi k.val⟩)
    (fun i => (Finset.mem_sdiff.mp (pick i).property).2)
  exact ⟨r,f,hf⟩
end FiveColour.Physical.Projection
