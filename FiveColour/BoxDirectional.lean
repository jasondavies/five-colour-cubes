module
public import FiveColour.BoxAxes
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def alongBits (s t : Fin 75) (a : Fin 3) :=
  (Finset.univ.filter fun e : Fin 12 => edgeAxis e = a ∧
    (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false).card
lemma missingAlong_bits (s t : Fin 75) (a : Fin 3) :
    missingAlong (catalogue s) (catalogue t) a = alongBits s t a := by
  unfold missingAlong alongBits
  congr 1; ext e; simp [← edgeBits_correct]

/-- Directional inequalities for the twelve geometric edges. -/
lemma directional_bits (s : Fin 75) : ∀ t,
    (∑ a, alongBits s t a) ≤ 4 ∧
    cornerMissBits s t + (∑ a, alongBits s t a) ≤ 10 ∧
    (∀ a, alongBits s t a ≤ 2) ∧
    (∀ a b, a ≠ b → alongBits s t a + alongBits s t b ≤ 3 ∧
      cornerMissBits s t + 2*(alongBits s t a + alongBits s t b) ≤ 12) := by
  fin_cases s <;> decide +kernel

lemma thin_directional_bits (s : Fin 75) : ∀ t a,
    BichromaticAxis (catalogue t) a →
      cornerMissBits s t + alongBits s t a ≤ 8 ∧
      ∀ b, a ≠ b → BichromaticAxis (catalogue t) b →
        cornerMissBits s t + alongBits s t a + alongBits s t b ≤ 9 := by
  fin_cases s <;> decide +kernel

end FiveColour.Physical
