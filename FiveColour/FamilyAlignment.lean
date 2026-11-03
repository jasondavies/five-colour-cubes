module
public import FiveColour.BoxGeometry
public import FiveColour.BoxAxes
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def poleAxis (p : Fin 10) (t : Fin 75) : Fin 3 :=
  let f := ((List.finRange 6).find? fun f => decide (catalogue t f = pairFirst p)).getD 0
  ⟨f.val/2,by have := f.isLt; omega⟩
lemma family_alignment_bits (p : Fin 10) : ∀ t, ¬ HasPairBit t p →
    (∀ a, a ≠ poleAxis p t → BichromaticAxis (catalogue t) a) ∧
    ∀ s, OppositeRepeat (catalogue s) → ¬ HasPairBit s p →
      cornerMissBits s t ≤ 4 ∧ ∀ a, a ≠ poleAxis p t → alongBits s t a = 0 := by
  fin_cases p <;> decide +kernel
lemma family_alignment (p : Fin 10) (t : Fin 75) (ht : ¬ HasPair (catalogue t) p) :
    (∀ a, a ≠ poleAxis p t → BichromaticAxis (catalogue t) a) ∧
    ∀ s, OppositeRepeat (catalogue s) → ¬ HasPair (catalogue s) p →
      missingCorners (catalogue s) (catalogue t) ≤ 4 ∧
      ∀ a, a ≠ poleAxis p t → missingAlong (catalogue s) (catalogue t) a = 0 := by
  simpa only [HasPairBit,edgeBits_correct,HasPair,← missingCorners_bits,← missingAlong_bits]
    using family_alignment_bits p t (by simpa only [HasPairBit,edgeBits_correct,HasPair] using ht)

lemma family_rect_missing (p : Fin 10) (s t : Fin 75)
    (hs : ¬ HasPair (catalogue s) p) (ht : ¬ HasPair (catalogue t) p)
    (ho : OppositeRepeat (catalogue s)) (m u v : ℕ) :
    (Finset.univ.filter fun pos : RectSlot (fun a => ![m,u,v] (Equiv.swap (0 : Fin 3) (poleAxis p t) a)) =>
      ¬ RectFits (catalogue s) (catalogue t) pos).card ≤ 2*m+4 := by
  classical
  rw [rect_missing_card]
  obtain ⟨hc,he⟩ := (family_alignment p t ht).2 s ho hs
  have hsum : (∑ a, missingAlong (catalogue s) (catalogue t) a * ![m,u,v] (Equiv.swap (0 : Fin 3) (poleAxis p t) a)) =
      missingAlong (catalogue s) (catalogue t) (poleAxis p t) * m := by
    rw [Finset.sum_eq_single (poleAxis p t)]
    · simp
    · intro a _ ha; rw [he a ha]; simp
    · simp
  rw [hsum]
  have hk : missingAlong (catalogue s) (catalogue t) (poleAxis p t) ≤ 2 := by
    rw [missingAlong_bits]; exact (directional_bits s t).2.2.1 _
  nlinarith
end FiveColour.Physical
