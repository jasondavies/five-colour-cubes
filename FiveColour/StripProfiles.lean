module
public import FiveColour.BoxDirectional
public import FiveColour.RodAxes
@[expose] public section
namespace FiveColour.Physical.Strip
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cornerMissing (s t : Fin 75) (k : Fin 8) : Prop := (Replay.fits t s).testBit k.val = false
instance (s t : Fin 75) : DecidablePred (cornerMissing s t) := by intro k; unfold cornerMissing; infer_instance
def edgeMissing (s t : Fin 75) (e : Fin 12) : Prop :=
  (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false
instance (s t : Fin 75) : DecidablePred (edgeMissing s t) := by intro e; unfold edgeMissing; infer_instance

def Maximal (s t : Fin 75) (a b : Fin 3) : Prop :=
  OppositeRepeat (catalogue s) ∧ cornerMissBits s t = 6 ∧ alongBits s t a = 1 ∧ alongBits s t b = 2
instance (s t : Fin 75) (a b : Fin 3) : Decidable (Maximal s t a b) := by unfold Maximal; infer_instance

lemma adjacent_bits (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t a b,
    a ≠ b → BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  fin_cases s <;> decide +kernel

/-- Equality in the strip defect bound determines the source from its
missing positions. This checks only individual cube incidence profiles. -/
lemma maximal_witness_bits (t : Fin 75) : ∀ a b, a ≠ b →
    BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
    ∀ s, Maximal s t a b → ∀ u, Maximal u t a b → s ≠ u →
      (∃ k, cornerMissing s t k ∧ ¬ cornerMissing u t k) ∨
      (∃ e, (edgeAxis e = a ∨ edgeAxis e = b) ∧ edgeMissing s t e ∧ ¬ edgeMissing u t e) := by
  fin_cases t <;> decide +kernel

/-- Put the repeated axis of an opposite-repeat target along the length-two
side; the other two directions then have the improved bound. -/
lemma opposite_short_bits (s : Fin 75) : ∀ t (z a b : Fin 3),
    a ≠ b → a ≠ z → b ≠ z → Axial (catalogue t) z →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  fin_cases s <;> decide +kernel
end FiveColour.Physical.Strip
