module
public import FiveColour.PairCapacityData
@[expose] public section
namespace FiveColour.Physical

/-- Every nonzero table entry gives a physical obstruction to a larger multiplicity.
The zero entries use the universal seven-copy bound. -/
theorem pair_capacity_bound {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (kind : Fin 2) (m : Fin 8)
    (hm : m.val ≤ multiplicity cubes (canonicalAnchor kind)) (i : Fin 75) :
    multiplicity cubes i ≤ pairCap kind m i := by
  by_cases hz : (pairSplit kind m i).val = 0
  · simpa only [pairCap, hz, Nat.sub_zero] using multiplicity_le_seven cubes hc h i
  · obtain ⟨ha, hi, hw⟩ := pair_witnesses_valid kind m i hz
    exact two_variety_capacity cubes hc h (canonicalAnchor kind) i (pairTarget kind m i)
      hi (pairSplit kind m i).val (by omega) (pairMaskCriterion_sound _ _ _ _ hw) (ha.trans hm)

end FiveColour.Physical
