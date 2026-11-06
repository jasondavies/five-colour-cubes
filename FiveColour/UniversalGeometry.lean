module
public import FiveColour.UniversalData
@[expose] public section
namespace FiveColour.Physical
open ColourCubes.Geometry

/-- The four bicoloured types rrp, indexed by the colours other than r. -/
def universalBiTypes (a : Fin 75) (r : Fin 5) : Finset (Fin 4) :=
  Finset.univ.filter fun p => ∃ k : Fin 8,
    catalogueCornerKey a k = cornerKey ![r,r,r.succAbove p]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma universal_bi_types (a : Fin 75) : ∀ r : Fin 5,
    (universalBiTypes a r).card ≤ 2 ∧
    ((universalBiTypes a r).Nonempty → universalSourceClass a = r.castSucc) := by
  fin_cases a <;> decide +kernel

lemma universal_pair_geometry (r : Fin 5) : ∀ z : Fin 6,
    Submission.AdjacentRepeat (catalogue (universalPairTarget r z)) ∧
    universalPairPosition r z 0 ≠ universalPairPosition r z 1 ∧
    ∀ a : Fin 75,
      ((Replay.fits (universalPairTarget r z) a).testBit
        (universalPairPosition r z 0).val = true ↔ universalPairFirst z ∈ universalBiTypes a r) ∧
      ((Replay.fits (universalPairTarget r z) a).testBit
        (universalPairPosition r z 1).val = true ↔ universalPairSecond z ∈ universalBiTypes a r) := by
  unfold Submission.AdjacentRepeat
  fin_cases r <;> decide +kernel

/-- Two sources, each carrying at most two of four types, cannot match every
prescribed pair. This is the four-element combinatorial core of the lower bound. -/
lemma universal_two_insufficient : ∀ S T : Finset (Fin 4),
    S.card ≤ 2 → T.card ≤ 2 → ∃ z : Fin 6,
      ¬ (universalPairFirst z ∈ S ∧ universalPairSecond z ∈ T) ∧
      ¬ (universalPairFirst z ∈ T ∧ universalPairSecond z ∈ S) := by
  decide +kernel

lemma universal_sources : ∀ i : Fin 15,
    UsesAllColours (Submission.universalFamily i) ∧
    catalogueIndex (Submission.universalFamily i) = universalSource i ∧
    Submission.AdjacentRepeat (Submission.universalFamily i) := by
  unfold UsesAllColours Submission.AdjacentRepeat
  decide +kernel

lemma universal_sources_distinct : Function.Injective universalSource := by
  decide +kernel

lemma universal_placements (t : Fin 75) :
    Function.Injective (universalPlacement t) ∧
    ∀ k : Fin 8, (Replay.fits t (universalSource (universalPlacement t k))).testBit k.val = true := by
  fin_cases t <;> decide +kernel

end FiveColour.Physical
