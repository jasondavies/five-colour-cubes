module
public import FiveColour.BoxSymmetry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def alongBits (s t : Fin 75) (a : Fin 3) :=
  (Finset.univ.filter fun e : Fin 12 => edgeAxis e = a ∧
    (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false).card
lemma missingAlong_bits (s t : Fin 75) (a : Fin 3) :
    missingAlong (catalogue s) (catalogue t) a = alongBits s t a := by
  unfold missingAlong alongBits
  congr 1; ext e; simp [← edgeBits_correct]

/-- Directional inequalities for the twelve geometric edges. -/
lemma directional_canonical (s : Fin 75) : ∀ t, t = 0 ∨ t = 3 →
    (∑ a, alongBits s t a) ≤ 4 ∧
    cornerMissBits s t + (∑ a, alongBits s t a) ≤ 10 ∧
    (∀ a, alongBits s t a ≤ 2) ∧
    (∀ a b, a ≠ b → alongBits s t a + alongBits s t b ≤ 3 ∧
      cornerMissBits s t + 2*(alongBits s t a + alongBits s t b) ≤ 12) := by
  fin_cases s <;> decide +kernel

lemma thin_directional_canonical (s : Fin 75) : ∀ t, t = 0 ∨ t = 3 → ∀ a,
    BichromaticAxis (catalogue t) a →
      cornerMissBits s t + alongBits s t a ≤ 8 ∧
      ∀ b, a ≠ b → BichromaticAxis (catalogue t) b →
        cornerMissBits s t + alongBits s t a + alongBits s t b ≤ 9 := by
  fin_cases s <;> decide +kernel

lemma anchorFor_cases (t : Fin 75) : anchorFor t = 0 ∨ anchorFor t = 3 := by
  unfold anchorFor; split <;> simp

lemma normalised_corner_bits (s t : Fin 75) :
    cornerMissBits s t = cornerMissBits (normalisedSource s t) (anchorFor t) := by
  simpa only [missingCorners_bits] using normalised_corners s t

lemma normalised_along_bits (s t : Fin 75) (a : Fin 3) :
    alongBits s t a = alongBits (normalisedSource s t) (anchorFor t)
      (axisEquiv (normalisationRotation t) a) := by
  simpa only [missingAlong_bits] using normalised_along s t a

/-- The two canonical checks cover every target by colour relabelling and
proper rotation. Directional indices are transported by an axis permutation. -/
lemma directional_bits (s : Fin 75) : ∀ t,
    (∑ a, alongBits s t a) ≤ 4 ∧
    cornerMissBits s t + (∑ a, alongBits s t a) ≤ 10 ∧
    (∀ a, alongBits s t a ≤ 2) ∧
    (∀ a b, a ≠ b → alongBits s t a + alongBits s t b ≤ 3 ∧
      cornerMissBits s t + 2*(alongBits s t a + alongBits s t b) ≤ 12) := by
  intro t
  have h := directional_canonical (normalisedSource s t) (anchorFor t) (anchorFor_cases t)
  simp_rw [normalised_along_bits s t,normalised_corner_bits s t]
  rw [Equiv.sum_comp]
  exact ⟨h.1,h.2.1,fun a => h.2.2.1 _,fun a b hab =>
    h.2.2.2 _ _ ((axisEquiv (normalisationRotation t)).injective.ne hab)⟩

lemma thin_directional_bits (s : Fin 75) : ∀ t a,
    BichromaticAxis (catalogue t) a →
      cornerMissBits s t + alongBits s t a ≤ 8 ∧
      ∀ b, a ≠ b → BichromaticAxis (catalogue t) b →
        cornerMissBits s t + alongBits s t a + alongBits s t b ≤ 9 := by
  intro t a ha
  have h := thin_directional_canonical (normalisedSource s t) (anchorFor t) (anchorFor_cases t)
    _ ((normalised_bichromatic t a).mp ha)
  simp_rw [normalised_along_bits s t,normalised_corner_bits s t]
  exact ⟨h.1,fun b hab hb => h.2 _
    ((axisEquiv (normalisationRotation t)).injective.ne hab) ((normalised_bichromatic t b).mp hb)⟩

end FiveColour.Physical
