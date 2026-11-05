module
public import FiveColour.ExtremalMatching
public import FiveColour.StabiliserData
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Four copies of a and five each of b and c, indexed as distinct physical pieces. -/
def tripleVariety (a b c : Fin 75) (i : Fin 14) : Fin 75 :=
  if i.val < 4 then a else if i.val < 9 then b else c

def tripleFamily (a b c : Fin 75) (i : Fin 14) : Cube :=
  catalogue (tripleVariety a b c i)

lemma triple_uses_all (a b c : Fin 75) : ∀ i, UsesAllColours (tripleFamily a b c i) :=
  fun _ => catalogue_uses_all_colours _

lemma triple_multiplicity (a b c : Fin 75) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 75) : multiplicity (tripleFamily a b c) i =
      if i = a then 4 else if i = b then 5 else if i = c then 5 else 0 := by
  unfold multiplicity tripleFamily
  simp only [catalogue_index_faces]
  by_cases ha : i = a
  · subst i
    simp [tripleVariety, ite_eq_iff, Ne.symm hab, Ne.symm hac]
    decide +kernel
  · by_cases hb : i = b
    · subst i
      simp [tripleVariety, ite_eq_iff, ha, hab, Ne.symm hbc]
      decide +kernel
    · by_cases hc : i = c
      · subst i
        simp [tripleVariety, ite_eq_iff, ha, hb, hac, hbc]
        decide +kernel
      · simp [tripleVariety, ite_eq_iff, ha, hb, hc, Ne.symm ha, Ne.symm hb, Ne.symm hc]

/-- For 4+5+5 copies, any two source groups already exceed the eight positions.
Thus Hall reduces to coverage and three private-position bounds. -/
def TripleCriterion (a b c t : Fin 75) : Prop :=
  (Replay.fits t a).lor ((Replay.fits t b).lor (Replay.fits t c)) = 255 ∧
  (cornerSet (Replay.fits t a) \ (cornerSet (Replay.fits t b) ∪ cornerSet (Replay.fits t c))).card ≤ 4 ∧
  (cornerSet (Replay.fits t b) \ (cornerSet (Replay.fits t a) ∪ cornerSet (Replay.fits t c))).card ≤ 5 ∧
  (cornerSet (Replay.fits t c) \ (cornerSet (Replay.fits t a) ∪ cornerSet (Replay.fits t b))).card ≤ 5
instance (a b c t : Fin 75) : Decidable (TripleCriterion a b c t) := by
  unfold TripleCriterion; infer_instance

private lemma private_hall (A B C K : Finset (Fin 8))
    (hcover : ∀ k, k ∈ A ∨ k ∈ B ∨ k ∈ C)
    (ha : (A \ (B ∪ C)).card ≤ 4) (hb : (B \ (A ∪ C)).card ≤ 5)
    (hc : (C \ (A ∪ B)).card ≤ 5) :
    K.card ≤ (if (K ∩ A).Nonempty then 4 else 0) +
      (if (K ∩ B).Nonempty then 5 else 0) + (if (K ∩ C).Nonempty then 5 else 0) := by
  have h8 : K.card ≤ 8 := by simpa using Finset.card_le_univ K
  have hsub (X Y Z : Finset (Fin 8)) (hcov : ∀ k, k ∈ X ∨ k ∈ Y ∨ k ∈ Z)
      (hy : ¬ (K ∩ Y).Nonempty) (hz : ¬ (K ∩ Z).Nonempty) : K ⊆ X \ (Y ∪ Z) := by
    intro k hk
    have hny : k ∉ Y := fun h => hy ⟨k,Finset.mem_inter.mpr ⟨hk,h⟩⟩
    have hnz : k ∉ Z := fun h => hz ⟨k,Finset.mem_inter.mpr ⟨hk,h⟩⟩
    exact Finset.mem_sdiff.mpr ⟨(hcov k).resolve_right (fun h => h.elim hny hnz),
      by simpa using And.intro hny hnz⟩
  by_cases hA : (K ∩ A).Nonempty <;> by_cases hB : (K ∩ B).Nonempty <;>
    by_cases hC : (K ∩ C).Nonempty <;> simp only [hA,hB,hC,↓reduceIte] <;> try omega
  · exact (Finset.card_le_card (hsub A B C hcover hB hC)).trans ha
  · exact (Finset.card_le_card (hsub B A C (fun k => by have := hcover k; tauto) hA hC)).trans hb
  · exact (Finset.card_le_card (hsub C A B (fun k => by have := hcover k; tauto) hA hB)).trans hc
  · have he : K = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      rcases hcover k with h | h | h
      · exact hA ⟨k,Finset.mem_inter.mpr ⟨hk,h⟩⟩
      · exact hB ⟨k,Finset.mem_inter.mpr ⟨hk,h⟩⟩
      · exact hC ⟨k,Finset.mem_inter.mpr ⟨hk,h⟩⟩
    simp [he]

lemma triple_neighbours_card (a b c t : Fin 75) (K : Finset (Fin 8)) :
    (neighbours (tripleFamily a b c) (catalogue t) K).card =
      (if (K ∩ usableSlots (catalogue a) (catalogue t)).Nonempty then 4 else 0) +
      (if (K ∩ usableSlots (catalogue b) (catalogue t)).Nonempty then 5 else 0) +
      (if (K ∩ usableSlots (catalogue c) (catalogue t)).Nonempty then 5 else 0) := by
  have he : neighbours (tripleFamily a b c) (catalogue t) K = Finset.univ.filter
      (fun i : Fin 14 => if i.val < 4 then (K ∩ usableSlots (catalogue a) (catalogue t)).Nonempty
        else if i.val < 9 then (K ∩ usableSlots (catalogue b) (catalogue t)).Nonempty
        else (K ∩ usableSlots (catalogue c) (catalogue t)).Nonempty) := by
    ext i
    simp only [neighbours, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h4 : i.val < 4 <;> by_cases h9 : i.val < 9 <;>
      simp [tripleFamily, tripleVariety, h4, h9, usableSlots,
        Finset.Nonempty, Finset.mem_inter]
  rw [he]
  by_cases ha : (K ∩ usableSlots (catalogue a) (catalogue t)).Nonempty <;>
    by_cases hb : (K ∩ usableSlots (catalogue b) (catalogue t)).Nonempty <;>
    by_cases hc : (K ∩ usableSlots (catalogue c) (catalogue t)).Nonempty <;>
    simp only [ha,hb,hc,↓reduceIte] <;> decide +kernel

lemma triple_criterion_solves (a b c t : Fin 75) (h : TripleCriterion a b c t) :
    HasSolution (tripleFamily a b c) := by
  obtain ⟨hu,ha,hb,hc⟩ := h
  have hcover : ∀ k, k ∈ cornerSet (Replay.fits t a) ∨
      k ∈ cornerSet (Replay.fits t b) ∨ k ∈ cornerSet (Replay.fits t c) := by
    intro k
    have hfull : ∀ k : Fin 8, (255 : Nat).testBit k.val = true := by decide +kernel
    have hk := congrArg (fun mask => mask.testBit k.val) hu
    simpa only [Nat.lor_eq, Nat.testBit_lor, hfull k, Bool.or_eq_true,
      cornerSet, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  apply (hasSolution_iff_catalogue _).mpr
  refine ⟨t,(solvesTarget_iff_hall _ _).mpr ?_⟩
  intro K
  rw [triple_neighbours_card, ← cornerSet_fits, ← cornerSet_fits, ← cornerSet_fits]
  exact private_hall _ _ _ K hcover ha hb hc

end FiveColour.Physical
