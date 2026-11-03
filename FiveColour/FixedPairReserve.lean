module
public import FiveColour.FixedPair
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Apply the eleven-cube corner lemma after reserving monochromatic edges. -/
lemma reserve_fixed_pair {m : ℕ} (q : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (p : Fin 10) (available : Finset (Fin m))
    (hp : ∀ i ∈ available, ¬ HasPair (cubes i) p)
    (hsize : 11 + 3*q ≤ available.card) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot q // CorePosition (catalogue t) pos} ↪ Fin m,
        ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
  classical
  let cap := avoidingQuota p q
  obtain ⟨R,hR,hsat⟩ := Reserve.exists_saturated available
    (fun a : Fin 5 => fun i => HasEdge (cubes i) a a) cap
  have hused : (Reserve.used R).card ≤ 3*q := by
    calc
      _ ≤ ∑ a, cap a := (Reserve.used_card_le R).trans (Finset.sum_le_sum fun a _ => hR.2.1 a)
      _ = _ := avoidingQuota_sum p q
  let rest := available \ Reserve.used R
  have hrest : 11 ≤ rest.card := by
    have hsub : available ⊆ rest ∪ Reserve.used R := by
      intro i hi
      by_cases hr : i ∈ Reserve.used R
      · exact Finset.mem_union_right _ hr
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,hr⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 11)
    (show 11 ≤ Fintype.card rest by simpa using hrest)
  let selected := fun i : Fin 11 => cubes (pick i).val
  obtain ⟨t,ht,f,hf⟩ := fixed_pair_corners selected (fun i => hc _) (by simp) p
    (fun i => hp _ (Finset.mem_sdiff.mp (pick i).property).1)
  let corners : Fin 8 ↪ Fin m := (f.trans pick).trans (Function.Embedding.subtype (· ∈ rest))
  have havail (k) : corners k ∈ available := (Finset.mem_sdiff.mp (pick (f k)).property).1
  have hout (k) : corners k ∉ Reserve.used R := (Finset.mem_sdiff.mp (pick (f k)).property).2
  have hfit (k) : Fits (cubes (corners k)) (catalogue t) k := hf k
  refine ⟨t,ht,?_⟩
  apply core_placement q cubes t corners R hfit hout hR.2.2 (fun a i hi => (hR.1 a i hi).2)
  intro e he
  have hedge := edge_of_corner _ _ e (hfit (cornerOfEdge e))
  rw [← he] at hedge
  exact (hsat _ _ (havail _) (hout _) hedge).trans
    (avoidingQuota_full _ (hc _) p (hp _ (havail _)) q _ hedge)

/-- Select eleven copies while retaining a specified copy. -/
lemma eleven_subset_with {I : Type*} [DecidableEq I] (A : Finset I) (hA : 11 ≤ A.card)
    (i : I) (hi : i ∈ A) : ∃ S ⊆ A, S.card = 11 ∧ i ∈ S := by
  have h10 : 10 ≤ (A.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq h10
  have hnot : i ∉ T := fun h => (Finset.mem_erase.mp (hT h)).1 rfl
  refine ⟨insert i T,Finset.insert_subset hi (hT.trans (Finset.erase_subset _ _)),?_,by simp⟩
  simp [Finset.card_insert_of_notMem hnot,hcard]

lemma fixed_pair_core_available {m : ℕ} (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (p : Fin 10) (available : Finset (Fin m))
    (hp : ∀ i ∈ available, ¬ HasPair (cubes i) p) (hsize : 11 ≤ available.card)
    (ho : ∃ i ∈ available, OppositeRepeat (catalogue (catalogueIndex (cubes i)))) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot 1 // CorePosition (catalogue t) pos} ↪ Fin m,
        ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
  classical
  obtain ⟨i,hi,hoi⟩ := ho
  obtain ⟨S,hSA,hSc,hiS⟩ := eleven_subset_with available hsize i hi
  obtain ⟨t,ht,f,hf⟩ := fixed_pair_core (fun j : S => cubes j.val) (fun j => hc _)
    (by simpa using hSc) p (fun j => hp _ (hSA j.property)) ⟨⟨i,hiS⟩,hoi⟩
  exact ⟨t,ht,f.trans (Function.Embedding.subtype _),hf⟩

lemma fixed_pair_extra_available {m : ℕ} (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (p : Fin 10) (available : Finset (Fin m))
    (hp : ∀ i ∈ available, ¬ HasPair (cubes i) p) (hsize : 11 ≤ available.card)
    (hm : 12 ≤ m) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot 1 // CorePosition (catalogue t) pos} ↪ Fin m,
        ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
  classical
  obtain ⟨S,hSA,hSc⟩ := Finset.exists_subset_card_eq hsize
  have hne : S ≠ Finset.univ := by intro he; have := congrArg Finset.card he; simp_all
  have hex : ∃ w, w ∉ S := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_of_forall h)
  obtain ⟨w,hw⟩ := hex
  obtain ⟨t,ht,f,hf⟩ := fixed_pair_extra (fun j : S => cubes j.val) (fun j => hc _)
    (by simpa using hSc) p (fun j => hp _ (hSA j.property)) (cubes w) (hc w)
  let g : Option S → Fin m := fun i => Option.elim i w Subtype.val
  have hg : Function.Injective g := by
    intro a b he
    cases a with
    | none => cases b with
      | none => rfl
      | some b =>
        change w = b.val at he
        exact False.elim (hw (he.symm ▸ b.property))
    | some a => cases b with
      | none =>
        change a.val = w at he
        exact False.elim (hw (he ▸ a.property))
      | some b => exact congrArg Option.some (Subtype.ext he)
  refine ⟨t,ht,f.trans ⟨g,hg⟩,?_⟩
  intro pos
  have he : cubes (g (f pos)) = Option.elim (f pos) (cubes w) (fun j : S => cubes j.val) := by
    cases f pos <;> rfl
  simpa only [Function.Embedding.trans_apply,Function.Embedding.coeFn_mk,he] using hf pos
end FiveColour.Physical
