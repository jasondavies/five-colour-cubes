module
public import FiveColour.BoxCounts
public import FiveColour.SharpGeometry
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def BichromaticAxis (t : Cube) (a : Fin 3) : Prop :=
  ∀ e, edgeAxis e = a → t (edgeFaces e 0) ≠ t (edgeFaces e 1)
instance (t : Cube) (a : Fin 3) : Decidable (BichromaticAxis t a) := by
  unfold BichromaticAxis; infer_instance

lemma mono_axis : ∀ t : Fin 75, ∃ z : Fin 3,
    ∀ a, a ≠ z → BichromaticAxis (catalogue t) a := by decide +kernel

lemma family_axis_bits (p : Fin 10) : ∀ t : Fin 75, ¬ HasPairBit t p →
    ∃ z : Fin 3, (∀ a, a ≠ z → BichromaticAxis (catalogue t) a) ∧
      ∀ e, edgeAxis e ≠ z → ∀ r,
        r = p ∨ PairDisjoint p r →
          pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) ≠ r := by
  fin_cases p <;> decide +kernel
lemma family_axis (p : Fin 10) (t : Fin 75) (ht : ¬ HasPair (catalogue t) p) :
    ∃ z : Fin 3, (∀ a, a ≠ z → BichromaticAxis (catalogue t) a) ∧
      ∀ e, edgeAxis e ≠ z → ∀ r,
        r = p ∨ PairDisjoint p r →
          pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) ≠ r := by
  apply family_axis_bits p t
  simpa only [HasPairBit,edgeBits_correct,HasPair] using ht

lemma swap_zero (z a : Fin 3) : Equiv.swap (0 : Fin 3) z a = 0 ↔ a = z := by
  fin_cases z <;> fin_cases a <;> decide +kernel
end FiveColour.Physical
