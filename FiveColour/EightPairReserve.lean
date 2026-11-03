module
public import FiveColour.EightPlusThree
public import FiveColour.FixedPairReserve
public import FiveColour.MissingPairCopies
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Reserve the three possible monochromatic colours in the whole collection,
then apply eight-plus-three to the surviving missing-pair family. -/
lemma reserve_eight_pair {n : ℕ} (q : ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (p : Fin 10)
    (hn : 11+3*q ≤ n) (hfamily : 8+3*q ≤ (missingPairCopies cubes p).card) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot q // CorePosition (catalogue t) pos} ↪ Fin n,
        ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
  classical
  let cap := avoidingQuota p q
  obtain ⟨R,hR,hsat⟩ := Reserve.exists_saturated (Finset.univ : Finset (Fin n))
    (fun a : Fin 5 => fun i => HasEdge (cubes i) a a) cap
  have hused : (Reserve.used R).card ≤ 3*q := by
    calc
      _ ≤ ∑ a,cap a := (Reserve.used_card_le R).trans (Finset.sum_le_sum fun a _ => hR.2.1 a)
      _ = _ := avoidingQuota_sum p q
  let rest := Finset.univ \ Reserve.used R
  have hrest : 11 ≤ rest.card := by
    have he : rest.card = n-(Reserve.used R).card := by simp [rest,Finset.card_sdiff]
    omega
  let F : Finset rest := Finset.univ.filter fun i => ¬ HasPair (cubes i.val) p
  have hFcard : F.card = (missingPairCopies cubes p \ Reserve.used R).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨(mem_missingPairCopies cubes p _).mpr (Finset.mem_filter.mp hi).2,
        (Finset.mem_sdiff.mp i.property).2⟩
    · intro i _ j _ he; exact Subtype.ext he
    · intro i hi
      let j : rest := ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hi).2⟩⟩
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (mem_missingPairCopies cubes p i).mp (Finset.mem_sdiff.mp hi).1⟩,rfl⟩
  have hF : 8 ≤ F.card := by
    have hcard := Finset.card_sdiff_add_card (s := missingPairCopies cubes p) (t := Reserve.used R)
    have hsub := Finset.card_le_card (Finset.subset_union_left (s₁ := missingPairCopies cubes p) (s₂ := Reserve.used R))
    omega
  obtain ⟨t,ht,f,hf⟩ := eight_plus_three_available p (fun i : rest => cubes i.val) (fun _ => hc _)
    F hF (by simpa using hrest) (fun i hi => (Finset.mem_filter.mp hi).2)
  let corners := f.trans (Function.Embedding.subtype (· ∈ rest))
  have hfit (k) : Fits (cubes (corners k)) (catalogue t) k := hf k
  have hout (k) : corners k ∉ Reserve.used R := (Finset.mem_sdiff.mp (f k).property).2
  refine ⟨t,ht,?_⟩
  apply core_placement q cubes t corners R hfit hout hR.2.2 (fun a i hi => (hR.1 a i hi).2)
  intro e he
  have hedge := edge_of_corner _ _ e (hfit (cornerOfEdge e))
  have htarget := edge_of_corner (catalogue t) (catalogue t) e (fits_self _ _)
  rw [← he] at hedge htarget
  exact (hsat _ _ (Finset.mem_univ _) (hout _) hedge).trans
    (avoidingQuota_full _ (catalogue_uses_all_colours t) p ht q _ htarget)
end FiveColour.Physical
