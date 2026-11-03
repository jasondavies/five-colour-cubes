module
public import FiveColour.StripProfiles
public import FiveColour.RodModel
public import FiveColour.CornerDefects
@[expose] public section
namespace FiveColour.Physical.Strip
open scoped BigOperators

abbrev Lengths (axes : Equiv.Perm (Fin 3)) (M : ℕ) := fun a => ![0,1,M] (axes a)
lemma count_bits (s t : Fin 75) (axes : Equiv.Perm (Fin 3)) (M : ℕ) :
    (Finset.univ.filter fun p : RectSlot (Lengths axes M) => ¬ RectFits (catalogue s) (catalogue t) p).card =
      cornerMissBits s t + alongBits s t (axes.symm 1) + alongBits s t (axes.symm 2)*M := by
  rw [rect_missing_card,missingCorners_bits]
  simp_rw [missingAlong_bits]
  have he := Equiv.sum_comp axes.symm (fun a => alongBits s t a * ![0,1,M] (axes a))
  simp only [Equiv.apply_symm_apply] at he
  rw [← he]
  simp [Fin.sum_univ_succ,Nat.add_assoc]

lemma defect_bounds (s t : Fin 75) (a b : Fin 3) (hab : a ≠ b)
    (ha : BichromaticAxis (catalogue t) a) (hb : BichromaticAxis (catalogue t) b)
    (M : ℕ) (hM : 2 ≤ M) :
    cornerMissBits s t+alongBits s t a+alongBits s t b*M ≤ 2*M+7 ∧
      (¬ OppositeRepeat (catalogue s) →
        cornerMissBits s t+alongBits s t a+alongBits s t b*M ≤ 2*M+6) := by
  have hk := (directional_bits s t).2.2.1 b
  have hsum := ((directional_bits s t).2.2.2 a b hab).1
  have hnon (hn : ¬ OppositeRepeat (catalogue s)) :
      cornerMissBits s t+alongBits s t a+alongBits s t b*M ≤ 2*M+6 := by
    have hh := adjacent_bits s hn t a b hab ha hb
    have hmul := Nat.mul_le_mul_left (M-2) hk
    have hm : M-2+2=M := by omega
    nlinarith
  refine ⟨?_,hnon⟩
  by_cases ho : OppositeRepeat (catalogue s)
  · have hh := opposite_source_corners s t ho
    have hmul := Nat.mul_le_mul_left (M-1) hk
    have hm : M-1+1=M := by omega
    nlinarith
  · have := hnon ho; omega

lemma maximal_of_large (s t : Fin 75) (a b : Fin 3) (hab : a ≠ b)
    (ha : BichromaticAxis (catalogue t) a) (hb : BichromaticAxis (catalogue t) b)
    (M : ℕ) (hM : 2 ≤ M)
    (hlarge : 2*M+6 < cornerMissBits s t+alongBits s t a+alongBits s t b*M) : Maximal s t a b := by
  have hso : OppositeRepeat (catalogue s) := by
    by_contra hn; have := (defect_bounds s t a b hab ha hb M hM).2 hn; omega
  have hh := opposite_source_corners s t hso
  have hk := (directional_bits s t).2.2.1 b
  have hsum := ((directional_bits s t).2.2.2 a b hab).1
  have hb2 : alongBits s t b=2 := by
    by_contra hn
    have hk1 : alongBits s t b ≤ 1 := by omega
    have hmul := Nat.mul_le_mul_left (M-1) hk1
    have hm : M-1+1=M := by omega
    nlinarith
  rw [hb2] at hlarge hsum
  exact ⟨hso,by omega,by omega,hb2⟩

lemma separation (s u t : Fin 75) (axes : Equiv.Perm (Fin 3)) (M : ℕ) (hM : 2 ≤ M)
    (hmono : ∀ a, axes a ≠ 0 → BichromaticAxis (catalogue t) a) (hsu : s ≠ u) :
    (Finset.univ.filter fun p : RectSlot (Lengths axes M) =>
      ¬ RectFits (catalogue s) (catalogue t) p ∧ ¬ RectFits (catalogue u) (catalogue t) p).card ≤ 2*M+6 := by
  classical
  let a := axes.symm (1 : Fin 3)
  let b := axes.symm (2 : Fin 3)
  have hab : a ≠ b := axes.symm.injective.ne (by decide)
  have ha := hmono a (by simp [a])
  have hb := hmono b (by simp [b])
  by_cases hs : cornerMissBits s t+alongBits s t a+alongBits s t b*M ≤ 2*M+6
  · apply (joint_missing_le_left _ _ _ _).trans
    rw [count_bits]; exact hs
  by_cases hu : cornerMissBits u t+alongBits u t a+alongBits u t b*M ≤ 2*M+6
  · apply (joint_missing_le_right _ _ _ _).trans
    rw [count_bits]; exact hu
  have hmaxs := maximal_of_large s t a b hab ha hb M hM (by omega)
  have hmaxu := maximal_of_large u t a b hab ha hb M hM (by omega)
  have hbound : (Finset.univ.filter fun p : RectSlot (Lengths axes M) => ¬ RectFits (catalogue s) (catalogue t) p).card ≤ 2*M+7 := by
    rw [count_bits]; exact (defect_bounds s t a b hab ha hb M hM).1
  have witness : ∃ p : RectSlot (Lengths axes M), ¬ RectFits (catalogue s) (catalogue t) p ∧ RectFits (catalogue u) (catalogue t) p := by
    rcases maximal_witness_bits t a b hab ha hb s hmaxs u hmaxu hsu with ⟨k,hs,hu⟩ | ⟨e,he,hs,hu⟩
    · refine ⟨.inl k,?_,?_⟩
      · simpa [RectFits,cornerMissing,← incidence_fits] using hs
      · simpa [RectFits,cornerMissing,← incidence_fits] using hu
    · have hlen : 0 < Lengths axes M (edgeAxis e) := by
        rcases he with he | he
        · simp [Lengths,he,a]
        · simp [Lengths,he,b]; omega
      refine ⟨.inr ⟨e,⟨0,hlen⟩⟩,?_,?_⟩
      · simpa [RectFits,edgeMissingBit,← edgeBits_correct] using hs
      · simpa [RectFits,edgeMissingBit,← edgeBits_correct] using hu
  obtain ⟨p,hsp,hup⟩ := witness
  have := joint_missing_lt_of_witness (Lengths axes M) (catalogue s) (catalogue u) (catalogue t) p hsp hup
  omega

lemma opposite_short_bound (s t : Fin 75) (z : Fin 3) (hz : Axial (catalogue t) z)
    (M : ℕ) (hM : 2 ≤ M) :
    (Finset.univ.filter fun p : RectSlot (Lengths (Equiv.swap (0 : Fin 3) z) M) =>
      ¬ RectFits (catalogue s) (catalogue t) p).card ≤ 2*M+6 := by
  let axes := Equiv.swap (0 : Fin 3) z
  rw [count_bits]
  have hne1 : axes.symm (1 : Fin 3) ≠ z := by
    intro he; have := congrArg axes he; simp [axes] at this
  have hne2 : axes.symm (2 : Fin 3) ≠ z := by
    intro he; have := congrArg axes he; simp [axes] at this
  have hh := opposite_short_bits s t z (axes.symm 1) (axes.symm 2)
    (axes.symm.injective.ne (by decide)) hne1 hne2 hz
  have hk := (directional_bits s t).2.2.1 (axes.symm 2)
  have hmul := Nat.mul_le_mul_left (M-2) hk
  have hm : M-2+2=M := by omega
  nlinarith
end FiveColour.Physical.Strip
