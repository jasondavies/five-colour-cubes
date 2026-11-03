module
public import FiveColour.BoxMatching
public import FiveColour.RectCounting
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

def RodLengths (a : Fin 3) (M : ℕ) : Fin 3 → ℕ := fun b => if b=a then M else 0
lemma rodSlot_card (a : Fin 3) (M : ℕ) : Fintype.card (RectSlot (RodLengths a M)) = 4*M+8 := by
  rw [rectSlot_card]
  simp [RodLengths,Nat.add_comm]
lemma rod_missing_card (c t : Cube) (a : Fin 3) (M : ℕ) :
    (Finset.univ.filter fun p : RectSlot (RodLengths a M) => ¬ RectFits c t p).card =
      missingCorners c t + missingAlong c t a*M := by
  rw [rect_missing_card]
  simp [RodLengths]
lemma rod_lengths_axes (a : Fin 3) (M : ℕ) :
    RodLengths a M = fun b => ![0,0,M] (Equiv.swap (2 : Fin 3) a b) := by
  funext b; fin_cases a <;> fin_cases b <;> norm_num [RodLengths,Equiv.swap_apply_def]
lemma box_of_rod {n : ℕ} (a : Fin 3) (M : ℕ) (cubes : Fin n → Cube)
    (h : RectSolvable (RodLengths a M) cubes) : BoxFrameSolvable 2 2 (M+2) cubes := by
  refine ⟨Equiv.swap (2 : Fin 3) a,?_⟩
  simpa only [Nat.add_sub_cancel,Nat.sub_self,rod_lengths_axes] using h

lemma rectCorner_card (l : Fin 3 → ℕ) :
    (Finset.univ.filter fun p : RectSlot l => RectCorner p).card = 8 := by
  rw [← Fintype.card_subtype,Fintype.card_congr (Equiv.subtypeSum),Fintype.card_sum]
  change Fintype.card {k : Fin 8 // True} + Fintype.card {p : (Σ e : Fin 12, Fin (l (edgeAxis e))) // False} = 8
  simp

lemma joint_missing_le_left (l : Fin 3 → ℕ) (s u t : Cube) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p ∧ ¬ RectFits u t p).card ≤
      (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p).card := by
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1⟩
lemma joint_missing_le_right (l : Fin 3 → ℕ) (s u t : Cube) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p ∧ ¬ RectFits u t p).card ≤
      (Finset.univ.filter fun p : RectSlot l => ¬ RectFits u t p).card := by
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.2⟩

lemma joint_missing_le_corners (l : Fin 3 → ℕ) (s u t : Cube)
    (he : ∀ e, 0 < l (edgeAxis e) →
      HasEdge s (t (edgeFaces e 0)) (t (edgeFaces e 1)) ∨ HasEdge u (t (edgeFaces e 0)) (t (edgeFaces e 1))) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p ∧ ¬ RectFits u t p).card ≤ 8 := by
  apply le_trans ?_ (le_of_eq (rectCorner_card l))
  apply Finset.card_le_card
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  cases p with
  | inl k => trivial
  | inr p =>
    obtain ⟨hs,hu⟩ := (Finset.mem_filter.mp hp).2
    rcases he p.1 (Nat.zero_lt_of_lt p.2.isLt) with h | h
    · exact False.elim (hs h)
    · exact False.elim (hu h)

lemma joint_missing_lt_of_witness (l : Fin 3 → ℕ) (s u t : Cube)
    (p : RectSlot l) (hs : ¬ RectFits s t p) (hu : RectFits u t p) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p ∧ ¬ RectFits u t p).card <
      (Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hk).2.1⟩
  · intro he
    have hp : p ∈ Finset.univ.filter fun p : RectSlot l => ¬ RectFits s t p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩
    rw [← he] at hp
    exact (Finset.mem_filter.mp hp).2.2 hu

lemma rectFits_self (t : Cube) {l : Fin 3 → ℕ} (p : RectSlot l) : RectFits t t p := by
  cases p with
  | inl k => exact fits_self t k
  | inr e => exact ⟨_,_,edge_adjacent e.1,rfl,rfl⟩
lemma rect_missing_index (l : Fin 3 → ℕ) (c t : Cube) (hc : UsesAllColours c) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits c t p).card =
      (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (catalogue (catalogueIndex c)) t p).card := by
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,rectFits_catalogueIndex c t hc]
lemma rect_joint_missing_index (l : Fin 3 → ℕ) (c u t : Cube) (hc : UsesAllColours c) (hu : UsesAllColours u) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits c t p ∧ ¬ RectFits u t p).card =
      (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (catalogue (catalogueIndex c)) t p ∧
        ¬ RectFits (catalogue (catalogueIndex u)) t p).card := by
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,rectFits_catalogueIndex c t hc,rectFits_catalogueIndex u t hu]
end FiveColour.Physical
