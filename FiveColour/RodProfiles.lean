module
public import FiveColour.RodAxes
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def RodTarget (t : Fin 75) (a : Fin 3) : Prop :=
  BichromaticAxis (catalogue t) a ∧ (OppositeRepeat (catalogue t) → Axial (catalogue t) a)
instance (t : Fin 75) (a : Fin 3) : Decidable (RodTarget t a) := by unfold RodTarget; infer_instance
def edgeMissingBit (s t : Fin 75) (e : Fin 12) : Prop :=
  (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false
instance (s t : Fin 75) : DecidablePred (edgeMissingBit s t) := by intro e; unfold edgeMissingBit; infer_instance
def rodAlongBits (s t : Fin 75) (a : Fin 3) :=
  (Finset.univ.filter fun e => edgeAxis e = a ∧ edgeMissingBit s t e).card

lemma adjacent_rod_bits (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t a,
    RodTarget t a → rodAlongBits s t a ≤ 1 ∧ cornerMissBits s t + rodAlongBits s t a ≤ 8 := by
  fin_cases s <;> decide +kernel
lemma axial_rod_bits (s : Fin 75) : ∀ t a, Axial (catalogue t) a →
    cornerMissBits s t + 2*rodAlongBits s t a ≤ 8 := by
  fin_cases s <;> decide +kernel

/-- The two opposite-repeat varieties missing two axial edge types have
complementary missing edges. The source hypotheses prune the finite check. -/
lemma rod_bad_disjoint_bits (t : Fin 75) : ∀ a, RodTarget t a → ∀ s,
    OppositeRepeat (catalogue s) → rodAlongBits s t a = 2 → ∀ u,
    OppositeRepeat (catalogue u) → rodAlongBits u t a = 2 → s ≠ u →
      ∀ e, edgeAxis e = a → ¬ (edgeMissingBit s t e ∧ edgeMissingBit u t e) := by
  fin_cases t <;> decide +kernel
end FiveColour.Physical
