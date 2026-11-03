module
public import FiveColour.RingEight
public import FiveColour.ProjectionExtension
public import FiveColour.FixedPair
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

lemma eight_plus_three_catalogue (p : Fin 10) (family : Fin 8 → Fin 9)
    (extra : Fin 3 → Fin 75) :
    ∃ t : Fin 9, ∃ f : Fin 8 ↪ (Fin 8 ⊕ Fin 3),
      ∀ k, Fits (catalogue (Sum.elim (fun i => Ring.variety p (family i)) extra (f k)))
        (catalogue (Ring.variety p t)) k := by
  classical
  let source := Sum.elim (fun i => Ring.variety p (family i)) extra
  have hx : Ring.O (Ring.counts family)+Ring.P (Ring.counts family)+Ring.M (Ring.counts family)=8 :=
    Ring.counts_total family
  rcases Ring.choose_eight (Ring.counts family) hx with ⟨t,_,hb⟩ | ⟨t,ht⟩
  · obtain ⟨f,hf⟩ := Ring.match_of_bounds family false t (Ring.corners_of_core_bounds _ _ hb)
    let e : Fin 8 ↪ Ring.Positions false t :=
      ⟨fun k => ⟨k.castSucc,Or.inl k.isLt⟩,fun a b he => Fin.ext (congrArg (fun z => z.val.val) he)⟩
    let g := (Ring.cornerEquiv p t).symm.toEmbedding.trans (e.trans f)
    refine ⟨t,g.trans ⟨Sum.inl,Sum.inl_injective⟩,?_⟩
    intro k
    have hfit := (Ring.corner_fits p t (family (g k)) ((Ring.cornerEquiv p t).symm k)).mpr
      (hf (e ((Ring.cornerEquiv p t).symm k)))
    have he := (Ring.cornerEquiv p t).apply_symm_apply k
    have he' : Ring.cornerMap p t ((Ring.cornerEquiv p t).symm k) = k := he
    change Fits (catalogue (Ring.variety p (family (g k)))) (catalogue (Ring.variety p t)) k
    simpa only [he'] using hfit
  let incl : Fin 8 ↪ (Fin 8 ⊕ Fin 3) := ⟨Sum.inl,Sum.inl_injective⟩
  let F := Finset.univ.map incl
  let typeOf := Sum.elim family (fun _ : Fin 3 => (0 : Fin 9))
  have hc (pred : Fin 9 → Prop) [DecidablePred pred] :
      (F.filter fun i => pred (typeOf i)).card = (Finset.univ.filter fun i => pred (family i)).card := by
    simp only [F,Finset.filter_map,Finset.card_map]
    rfl
  have hs (sign : Fin 2) : (Finset.univ.filter fun i => Projection.side sign (family i)).card =
      ![Ring.P (Ring.counts family),Ring.M (Ring.counts family)] sign := by
    have he := FrameHall.count_types family (Finset.univ.filter (Projection.side sign))
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he
    rw [← he]
    fin_cases sign <;> simp [Projection.side,Fin.sum_univ_succ,Finset.sum_filter,Ring.P,Ring.M,Ring.counts,Nat.add_assoc]
  have hstrong : 2 ≤ (F.filter fun i => typeOf i = t).card := by
    rw [hc (fun s => s = t)]
    change 2 ≤ Ring.counts family t
    rcases ht with h | h
    · exact h.2.2.2
    · exact h.2.2
  have major : ∃ sign, Projection.side sign t ∧
      5 ≤ (F.filter fun i => Projection.side sign (typeOf i)).card := by
    rcases ht with h | h
    · refine ⟨0,⟨h.1,h.2.1⟩,?_⟩
      rw [hc,hs]; exact h.2.2.1
    · refine ⟨1,⟨h.1,t.isLt⟩,?_⟩
      rw [hc,hs]; exact h.2.1
  obtain ⟨sign,hside,hP⟩ := major
  apply Projection.unbalanced p source F typeOf (by simp [F]) (by simp) ?_ sign t hside hP hstrong
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
  rfl

/-- Eight cubes lacking a prescribed pair and any three additional cubes
have a corner solution whose target still lacks that pair. -/
theorem eight_plus_three (p : Fin 10) (cubes : (Fin 8 ⊕ Fin 3) → Cube)
    (hc : ∀ i, UsesAllColours (cubes i))
    (hp : ∀ i : Fin 8, ¬ HasPair (cubes (.inl i)) p) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : Fin 8 ↪ (Fin 8 ⊕ Fin 3), ∀ k, Fits (cubes (f k)) (catalogue t) k := by
  classical
  obtain ⟨family,htype⟩ := fixed_pair_types (fun i => cubes (.inl i)) (fun i => hc _) p hp
  obtain ⟨t,f,hf⟩ := eight_plus_three_catalogue p family (fun i => catalogueIndex (cubes (.inr i)))
  refine ⟨Ring.variety p t,Ring.family_missing p t,f,?_⟩
  intro k
  apply (fits_catalogueIndex _ (hc _) _ _).mpr
  have hh := hf k
  cases he : f k with
  | inl i => simpa only [he,Sum.elim_inl,htype] using hh
  | inr i => simpa only [he,Sum.elim_inr] using hh
theorem eight_plus_three_available {I : Type*} [Fintype I] [DecidableEq I]
    (p : Fin 10) (cubes : I → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (F : Finset I) (hF : 8 ≤ F.card) (hI : 11 ≤ Fintype.card I)
    (hp : ∀ i ∈ F, ¬ HasPair (cubes i) p) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : Fin 8 ↪ I, ∀ k, Fits (cubes (f k)) (catalogue t) k := by
  classical
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 8) ≤ Fintype.card F by simpa using hF)
  let selected : Fin 8 ↪ I := pick.trans (Function.Embedding.subtype _)
  let used := Finset.univ.image selected
  have hused : used.card = 8 := by
    rw [Finset.card_image_of_injective _ selected.injective]; rfl
  have hrest : Fintype.card (Fin 3) ≤ Fintype.card ↥(Finset.univ \ used) := by
    simp only [Fintype.card_fin,Fintype.card_coe,Finset.card_sdiff_of_subset (Finset.subset_univ used),
      Finset.card_univ,hused]
    omega
  obtain ⟨extra⟩ := Function.Embedding.nonempty_of_card_le hrest
  let all : (Fin 8 ⊕ Fin 3) ↪ I :=
    ⟨Sum.elim selected (fun i => (extra i).val),
      selected.injective.sumElim (Subtype.val_injective.comp extra.injective)
        (fun i j he => (Finset.mem_sdiff.mp (extra j).property).2
          (he ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))⟩
  obtain ⟨t,ht,f,hf⟩ := eight_plus_three p (fun i => cubes (all i)) (fun i => hc _)
    (fun i => hp _ (pick i).property)
  exact ⟨t,ht,f.trans all,hf⟩
end FiveColour.Physical
