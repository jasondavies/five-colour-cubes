module
public import FiveColour.BoxLowerGeometry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

abbrev BoxLowerCopies (S : ℕ) := Fin 1 ⊕ (Fin (S+5) ⊕ Fin (S+6))
def boxLowerSource (S : ℕ) : BoxLowerCopies S → Cube :=
  Sum.elim (fun _ => catalogue 3) (Sum.elim (fun _ => catalogue 9) (fun _ => catalogue 56))
def lowerPool (S : ℕ) (j : Fin 3) : BoxLowerCopies S → Prop :=
  Sum.elim (fun _ => j ≠ 2) (Sum.elim (fun _ => j=1) (fun _ => j=2))
instance (S : ℕ) (j : Fin 3) : DecidablePred (lowerPool S j) := by
  intro i; unfold lowerPool; cases i with
  | inl i => simp only [Sum.elim_inl]; infer_instance
  | inr i => cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> infer_instance
lemma lowerPool_card (S : ℕ) (j : Fin 3) :
    (Finset.univ.filter (lowerPool S j)).card = ![1,S+6,S+6] j := by
  rw [← Fintype.card_subtype,Fintype.card_congr (Equiv.subtypeSum),Fintype.card_sum]
  rw [Fintype.card_congr (Equiv.subtypeSum),Fintype.card_sum]
  fin_cases j <;> simp [lowerPool]
  omega

lemma private_bound {I P : Type*} [Fintype I] [Fintype P] [DecidableEq I] [DecidableEq P]
    (f : P ↪ I) (D : P → Prop) [DecidablePred D] (pool : I → Prop) [DecidablePred pool]
    (hf : ∀ p, D p → pool (f p)) :
    (Finset.univ.filter D).card ≤ (Finset.univ.filter pool).card := by
  let e : {p // D p} ↪ {i // pool i} :=
    ⟨fun p => ⟨f p.val,hf p.val p.property⟩,fun a b he => Subtype.ext (f.injective (congrArg Subtype.val he))⟩
  simpa only [Fintype.card_subtype] using Fintype.card_le_of_embedding e

/-- The obstruction works for every assignment of edge lengths, including
zero lengths. Its private demands are 2, S+7 and S+7. -/
theorem box_lower_no_matching (l : Fin 3 → ℕ) (t : Cube) (ht : UsesAllColours t)
    (f : RectSlot l ↪ BoxLowerCopies (∑ a,l a))
    (hf : ∀ p, RectFits (boxLowerSource _ (f p)) t p) : False := by
  classical
  let S := ∑ a,l a
  obtain ⟨r,hr⟩ := catalogueIndex_spec t ht
  have hfits : ∀ p, RectFits (boxLowerSource S (f p)) (rotate (catalogue (catalogueIndex t)) r) p := by
    simpa only [← hr] using hf
  have hsupported : catalogueIndex t = 3 ∨ catalogueIndex t = 9 ∨ catalogueIndex t = 56 := by
    apply box_supported
    intro k
    let k' := (ColourCubes.Geometry.slotEquiv r).symm k
    have hfit := (fits_rotate_target _ _ r k').mp (hfits (.inl k'))
    simp only [k',Equiv.apply_symm_apply] at hfit
    change Fits (boxLowerSource S (f (.inl k'))) (catalogue (catalogueIndex t)) k at hfit
    cases hi : f (.inl k') with
    | inl i => exact Or.inl (by simpa only [hi,boxLowerSource,Sum.elim_inl,RectFits] using hfit)
    | inr i => cases i with
      | inl i => exact Or.inr (Or.inl (by simpa only [hi,boxLowerSource,Sum.elim_inr,Sum.elim_inl,RectFits] using hfit))
      | inr i => exact Or.inr (Or.inr (by simpa only [hi,boxLowerSource,Sum.elim_inr,RectFits] using hfit))
  rcases hsupported with htA | htB | htC
  · rw [htA] at hfits
    have hle := private_bound (Function.Embedding.inl.trans f)
      (fun k => ¬ Fits (catalogue 9) (rotate (catalogue 3) r) k) (lowerPool S 0) (by
        intro k hk
        have hfit := hfits (.inl k)
        change lowerPool S 0 (f (.inl k))
        cases hi : f (.inl k) with
        | inl i => norm_num [lowerPool]
        | inr i => cases i with
          | inl i => exact False.elim (hk (by simpa only [hi,boxLowerSource,Sum.elim_inr,Sum.elim_inl,RectFits] using hfit))
          | inr i =>
            have hh : Fits (catalogue 56) (rotate (catalogue 3) r) k := by
              simpa only [hi,boxLowerSource,Sum.elim_inr,RectFits] using hfit
            exact False.elim (hk ((fits_rotate_target _ _ r k).mpr
              (box_A_corner_subset _ ((fits_rotate_target _ _ r k).mp hh)))))
    change missingCorners (catalogue 9) (rotate (catalogue 3) r) ≤ _ at hle
    rw [missingCorners_rotate_target,box_private_corners.1,lowerPool_card] at hle
    norm_num at hle
  · rw [htB] at hfits
    have hle := private_bound f (fun p => ¬ RectFits (catalogue 56) (rotate (catalogue 9) r) p)
      (lowerPool S 1) (by
        intro p hp
        have hfit := hfits p
        cases hi : f p with
        | inl i => norm_num [lowerPool]
        | inr i => cases i with
          | inl i => norm_num [lowerPool]
          | inr i => exact False.elim (hp (by simpa only [hi,boxLowerSource,Sum.elim_inr,RectFits] using hfit)))
    rw [rect_missing_card,missingCorners_rotate_target,box_private_corners.2.1,lowerPool_card] at hle
    simp only [(box_private_edges r _).1,one_mul] at hle
    change 7+S ≤ S+6 at hle
    omega
  · rw [htC] at hfits
    have hle := private_bound f (fun p => ¬ RectFits (catalogue 3) (rotate (catalogue 56) r) p)
      (lowerPool S 2) (by
        intro p hp
        have hfit := hfits p
        cases hi : f p with
        | inl i => exact False.elim (hp (by simpa only [hi,boxLowerSource,Sum.elim_inl,RectFits] using hfit))
        | inr i => cases i with
          | inr i => norm_num [lowerPool]
          | inl i =>
            have hh : RectFits (catalogue 9) (rotate (catalogue 56) r) p := by
              simpa only [hi,boxLowerSource,Sum.elim_inr,Sum.elim_inl,RectFits] using hfit
            apply False.elim; apply hp
            cases p with
            | inl k =>
              change Fits (catalogue 3) (rotate (catalogue 56) r) k
              change Fits (catalogue 9) (rotate (catalogue 56) r) k at hh
              exact (fits_rotate_target _ _ r k).mpr
                (box_C_corner_subset _ ((fits_rotate_target _ _ r k).mp hh))
            | inr e => exact box_C_edge_subset r e.1 hh)
    rw [rect_missing_card,missingCorners_rotate_target,box_private_corners.2.2,lowerPool_card] at hle
    simp only [(box_private_edges r _).2,one_mul] at hle
    change 7+S ≤ S+6 at hle
    omega

noncomputable def boxLowerEquiv (S : ℕ) : Fin (2*S+12) ≃ BoxLowerCopies S :=
  Fintype.equivOfCardEq (by simp [BoxLowerCopies]; omega)
noncomputable def boxLowerFamily (S : ℕ) (i : Fin (2*S+12)) : Cube :=
  boxLowerSource S (boxLowerEquiv S i)
lemma boxLower_uses_all (S : ℕ) : ∀ i, UsesAllColours (boxLowerFamily S i) := by
  intro i
  unfold boxLowerFamily boxLowerSource
  cases boxLowerEquiv S i with
  | inl i => exact catalogue_uses_all_colours _
  | inr i => cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> exact catalogue_uses_all_colours _

theorem rect_lower_no_solution (l : Fin 3 → ℕ) :
    ¬ RectSolvable l (boxLowerFamily (∑ a,l a)) := by
  rintro ⟨t,ht,f,hf⟩
  exact box_lower_no_matching l t ht (f.trans (boxLowerEquiv _).toEmbedding)
    (fun p => (rectFits_iff_physical _ _ p).mpr (hf p))

lemma box_length_sum (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (axes : Equiv.Perm (Fin 3)) :
    (∑ i, ![a-2,b-2,c-2] (axes i)) = a+b+c-6 := by
  rw [Equiv.sum_comp axes (fun i => ![a-2,b-2,c-2] i)]
  simp [Fin.sum_univ_succ]
  omega

theorem box_lower_no_solution (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ BoxFrameSolvable a b c (boxLowerFamily (a+b+c-6)) := by
  rintro ⟨axes,h⟩
  have he := box_length_sum a b c ha hb hc axes
  rw [← he] at h
  exact rect_lower_no_solution _ h

/-- A collection of 2(a+b+c) cubes that fails in every orientation. -/
theorem box_obstruction (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ∃ cubes : Fin (2*(a+b+c)) → Cube,
      (∀ i, UsesAllColours (cubes i)) ∧ ¬ BoxFrameSolvable a b c cubes := by
  have he : 2*(a+b+c-6)+12 = 2*(a+b+c) := by omega
  let e := finCongr he
  refine ⟨fun i => boxLowerFamily _ (e.symm i),fun _ => boxLower_uses_all _ _,?_⟩
  rintro ⟨axes,t,ht,f,hf⟩
  apply box_lower_no_solution a b c ha hb hc
  exact ⟨axes,t,ht,f.trans e.symm.toEmbedding,hf⟩
end FiveColour.Physical
