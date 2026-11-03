module
public import FiveColour.BoxAxes
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Axial (t : Cube) (a : Fin 3) : Prop :=
  t ⟨2*a.val,by omega⟩ = t ⟨2*a.val+1,by omega⟩
instance (t : Cube) (a : Fin 3) : Decidable (Axial t a) := by unfold Axial; infer_instance
lemma rod_axis : ∀ t : Fin 75, ∃ a : Fin 3,
    BichromaticAxis (catalogue t) a ∧ (OppositeRepeat (catalogue t) → Axial (catalogue t) a) := by decide +kernel
lemma rod_family_axis_bits (p : Fin 10) : ∀ t : Fin 75, ¬ HasPairBit t p →
    ∃ a : Fin 3, BichromaticAxis (catalogue t) a ∧
      (OppositeRepeat (catalogue t) → Axial (catalogue t) a) ∧
      ∀ e, edgeAxis e = a → ∀ r,
        r = p ∨ PairDisjoint p r →
          pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) ≠ r := by
  fin_cases p <;> decide +kernel
lemma rod_family_axis (p : Fin 10) (t : Fin 75) (ht : ¬ HasPair (catalogue t) p) :
    ∃ a : Fin 3, BichromaticAxis (catalogue t) a ∧
      (OppositeRepeat (catalogue t) → Axial (catalogue t) a) ∧
      ∀ e, edgeAxis e = a → ∀ r,
        r = p ∨ PairDisjoint p r →
          pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) ≠ r := by
  apply rod_family_axis_bits p t
  simpa only [HasPairBit,edgeBits_correct,HasPair] using ht
end FiveColour.Physical
