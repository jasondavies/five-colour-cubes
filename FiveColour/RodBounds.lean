module
public import FiveColour.RodProfiles
public import FiveColour.RodModel
public import FiveColour.BoxDirectional
public import FiveColour.CornerDefects
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

lemma rod_count_bits (s t : Fin 75) (a : Fin 3) (M : ℕ) :
    (Finset.univ.filter fun p : RectSlot (RodLengths a M) => ¬ RectFits (catalogue s) (catalogue t) p).card =
      cornerMissBits s t + rodAlongBits s t a*M := by
  rw [rod_missing_card,missingCorners_bits,missingAlong_bits]
lemma rod_along_le (s t : Fin 75) (a : Fin 3) : rodAlongBits s t a ≤ 2 :=
  (directional_bits s t).2.2.1 a
lemma rod_adjacent_bound (s t : Fin 75) (a : Fin 3) (M : ℕ) (hM : 1 ≤ M)
    (ht : RodTarget t a) (hs : ¬ OppositeRepeat (catalogue s)) :
    cornerMissBits s t+rodAlongBits s t a*M ≤ M+7 := by
  obtain ⟨hk,hh⟩ := adjacent_rod_bits s hs t a ht
  have hmul := Nat.mul_le_mul_left (M-1) hk
  have hM' : M-1+1=M := by omega
  nlinarith
lemma rod_general_bound (s t : Fin 75) (a : Fin 3) (M : ℕ) (hM : 1 ≤ M)
    (ht : RodTarget t a) :
    cornerMissBits s t+rodAlongBits s t a*M ≤ 2*M+6 := by
  by_cases hs : OppositeRepeat (catalogue s)
  · have hh := opposite_source_corners s t hs
    have hk := rod_along_le s t a
    nlinarith
  · have := rod_adjacent_bound s t a M hM ht hs
    omega
lemma rod_axial_bound (s t : Fin 75) (a : Fin 3) (M : ℕ) (hM : 2 ≤ M)
    (ha : Axial (catalogue t) a) :
    cornerMissBits s t+rodAlongBits s t a*M ≤ 2*M+4 := by
  have hh := axial_rod_bits s t a ha
  have hk := rod_along_le s t a
  have hmul := Nat.mul_le_mul_left (M-2) hk
  have hM' : M-2+2=M := by omega
  nlinarith

lemma rod_separate_of_small (t : Fin 75) (a : Fin 3) (M d : ℕ) (ht : RodTarget t a)
    (hd : 8 ≤ d)
    (hsmall : ∀ s, rodAlongBits s t a ≤ 1 → cornerMissBits s t+rodAlongBits s t a*M ≤ d)
    (s u : Fin 75) (hsu : s ≠ u) :
    (Finset.univ.filter fun p : RectSlot (RodLengths a M) =>
      ¬ RectFits (catalogue s) (catalogue t) p ∧ ¬ RectFits (catalogue u) (catalogue t) p).card ≤ d := by
  classical
  by_cases hs : rodAlongBits s t a ≤ 1
  · apply (joint_missing_le_left _ _ _ _).trans
    rw [rod_count_bits]; exact hsmall s hs
  by_cases hu : rodAlongBits u t a ≤ 1
  · apply (joint_missing_le_right _ _ _ _).trans
    rw [rod_count_bits]; exact hsmall u hu
  have hsk : rodAlongBits s t a=2 := by have := rod_along_le s t a; omega
  have huk : rodAlongBits u t a=2 := by have := rod_along_le u t a; omega
  have hso : OppositeRepeat (catalogue s) := by
    by_contra hn; exact hs (adjacent_rod_bits s hn t a ht).1
  have huo : OppositeRepeat (catalogue u) := by
    by_contra hn; exact hu (adjacent_rod_bits u hn t a ht).1
  apply (joint_missing_le_corners _ _ _ _ ?_).trans hd
  intro e he
  have hea : edgeAxis e=a := by
    by_contra hh; simp [RodLengths,hh] at he
  have hbad := rod_bad_disjoint_bits t a ht s hso hsk u huo huk hsu e hea
  simpa only [edgeMissingBit,Bool.eq_false_iff,edgeBits_correct,not_and_or,not_not] using hbad

lemma rod_separate (t : Fin 75) (a : Fin 3) (M d : ℕ) (hM : 1 ≤ M)
    (ht : RodTarget t a) (hd : 8 ≤ d) (hMd : M+7 ≤ d) (s u : Fin 75) (hsu : s ≠ u) :
    (Finset.univ.filter fun p : RectSlot (RodLengths a M) =>
      ¬ RectFits (catalogue s) (catalogue t) p ∧ ¬ RectFits (catalogue u) (catalogue t) p).card ≤ d := by
  apply rod_separate_of_small t a M d ht hd ?_ s u hsu
  intro v hv
  by_cases ho : OppositeRepeat (catalogue v)
  · have hh := opposite_source_corners v t ho
    nlinarith
  · exact (rod_adjacent_bound v t a M hM ht ho).trans hMd

lemma rod_axial_separate (t : Fin 75) (a : Fin 3) (M : ℕ) (hM : 3 ≤ M)
    (ht : RodTarget t a) (ho : OppositeRepeat (catalogue t)) (s u : Fin 75) (hsu : s ≠ u) :
    (Finset.univ.filter fun p : RectSlot (RodLengths a M) =>
      ¬ RectFits (catalogue s) (catalogue t) p ∧ ¬ RectFits (catalogue u) (catalogue t) p).card ≤ 2*M+3 := by
  apply rod_separate_of_small t a M (2*M+3) ht (by omega) ?_ s u hsu
  intro v hv
  have hh := opposite_corner_bits v t ho
  nlinarith
lemma rod_axial_large_opposite (s t : Fin 75) (a : Fin 3) (M : ℕ) (hM : 3 ≤ M)
    (ht : RodTarget t a) (ho : OppositeRepeat (catalogue t))
    (hs : 2*M+3 < cornerMissBits s t+rodAlongBits s t a*M) : OppositeRepeat (catalogue s) := by
  by_contra hn
  have hk := (adjacent_rod_bits s hn t a ht).1
  have hh := opposite_corner_bits s t ho
  nlinarith
end FiveColour.Physical
