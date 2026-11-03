module
public import FiveColour.RodSymmetry
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def RodTarget (t : Fin 75) (a : Fin 3) : Prop :=
  BichromaticAxis (catalogue t) a ∧ (OppositeRepeat (catalogue t) → Axial (catalogue t) a)
instance (t : Fin 75) (a : Fin 3) : Decidable (RodTarget t a) := by unfold RodTarget; infer_instance
abbrev rodAlongBits := alongBits

lemma adjacent_rod_canonical (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t, t = 0 ∨ t = 3 → ∀ a,
    RodTarget t a → rodAlongBits s t a ≤ 1 ∧ cornerMissBits s t + rodAlongBits s t a ≤ 8 := by
  fin_cases s <;> decide +kernel
lemma axial_rod_canonical (s : Fin 75) : ∀ t, t = 0 ∨ t = 3 → ∀ a, Axial (catalogue t) a →
    cornerMissBits s t + 2*rodAlongBits s t a ≤ 8 := by
  fin_cases s <;> decide +kernel

/-- The two opposite-repeat varieties missing two axial edge types have
complementary missing edges. The source hypotheses prune the finite check. -/
lemma rod_bad_disjoint_canonical (t : Fin 75) : t = 0 ∨ t = 3 → ∀ a, RodTarget t a → ∀ s,
    OppositeRepeat (catalogue s) → rodAlongBits s t a = 2 → ∀ u,
    OppositeRepeat (catalogue u) → rodAlongBits u t a = 2 → s ≠ u →
      ∀ e, edgeAxis e = a → ¬ (edgeMissingBit s t e ∧ edgeMissingBit u t e) := by
  fin_cases t <;> decide +kernel

lemma normalised_rod_target (t : Fin 75) (a : Fin 3) :
    RodTarget t a ↔ RodTarget (anchorFor t) (axisEquiv (normalisationRotation t) a) := by
  simp only [RodTarget,normalised_bichromatic t a,normalised_target_kind t,normalised_axial t a]

lemma adjacent_rod_bits (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t a,
    RodTarget t a → rodAlongBits s t a ≤ 1 ∧ cornerMissBits s t + rodAlongBits s t a ≤ 8 := by
  intro hs t a ht
  simpa only [rodAlongBits,normalised_along_bits s t,normalised_corner_bits s t] using
    adjacent_rod_canonical (normalisedSource s t) (fun h => hs ((normalised_source_kind s t).mp h))
      (anchorFor t) (anchorFor_cases t) _ ((normalised_rod_target t a).mp ht)

lemma axial_rod_bits (s : Fin 75) : ∀ t a, Axial (catalogue t) a →
    cornerMissBits s t + 2*rodAlongBits s t a ≤ 8 := by
  intro t a ha
  simpa only [rodAlongBits,normalised_along_bits s t,normalised_corner_bits s t] using
    axial_rod_canonical (normalisedSource s t) (anchorFor t) (anchorFor_cases t)
      _ ((normalised_axial t a).mp ha)

/-- Normalise the target once; the induced source permutation preserves
inequality, and the edge permutation transports the separation witness. -/
lemma rod_bad_disjoint_bits (t : Fin 75) : ∀ a, RodTarget t a → ∀ s,
    OppositeRepeat (catalogue s) → rodAlongBits s t a = 2 → ∀ u,
    OppositeRepeat (catalogue u) → rodAlongBits u t a = 2 → s ≠ u →
      ∀ e, edgeAxis e = a → ¬ (edgeMissingBit s t e ∧ edgeMissingBit u t e) := by
  intro a ht s hs hsa u hu hua hsu e he
  have h := rod_bad_disjoint_canonical (anchorFor t) (anchorFor_cases t)
    _ ((normalised_rod_target t a).mp ht)
    (normalisedSource s t) ((normalised_source_kind s t).mpr hs)
    (by simpa only [rodAlongBits,normalised_along_bits s t] using hsa)
    (normalisedSource u t) ((normalised_source_kind u t).mpr hu)
    (by simpa only [rodAlongBits,normalised_along_bits u t] using hua)
    ((normalisedSource_injective t).ne hsu) (edgeEquiv (normalisationRotation t) e)
    ((rotatedEdge_axis _ e).trans (congrArg (axisEquiv (normalisationRotation t)) he))
  simpa only [normalised_edgeMissingBit s t e,normalised_edgeMissingBit u t e] using h

end FiveColour.Physical
