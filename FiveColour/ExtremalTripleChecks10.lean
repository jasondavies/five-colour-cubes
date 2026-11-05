module
public import FiveColour.ExtremalTripleData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

lemma triple_reduction_1_0 : ∀ c : Fin 75,
    0 < c → tripleAnchor 1 ≠ 0 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 0 c).Valid (tripleAnchor 1) 0 c := by decide +kernel

lemma triple_reduction_1_1 : ∀ c : Fin 75,
    1 < c → tripleAnchor 1 ≠ 1 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 1 c).Valid (tripleAnchor 1) 1 c := by decide +kernel

lemma triple_reduction_1_2 : ∀ c : Fin 75,
    2 < c → tripleAnchor 1 ≠ 2 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 2 c).Valid (tripleAnchor 1) 2 c := by decide +kernel

lemma triple_reduction_1_3 : ∀ c : Fin 75,
    3 < c → tripleAnchor 1 ≠ 3 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 3 c).Valid (tripleAnchor 1) 3 c := by decide +kernel

lemma triple_reduction_1_4 : ∀ c : Fin 75,
    4 < c → tripleAnchor 1 ≠ 4 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 4 c).Valid (tripleAnchor 1) 4 c := by decide +kernel

lemma triple_reduction_1_5 : ∀ c : Fin 75,
    5 < c → tripleAnchor 1 ≠ 5 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 5 c).Valid (tripleAnchor 1) 5 c := by decide +kernel

lemma triple_reduction_1_6 : ∀ c : Fin 75,
    6 < c → tripleAnchor 1 ≠ 6 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 6 c).Valid (tripleAnchor 1) 6 c := by decide +kernel

lemma triple_reduction_1_7 : ∀ c : Fin 75,
    7 < c → tripleAnchor 1 ≠ 7 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 7 c).Valid (tripleAnchor 1) 7 c := by decide +kernel

lemma triple_reduction_1_8 : ∀ c : Fin 75,
    8 < c → tripleAnchor 1 ≠ 8 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 8 c).Valid (tripleAnchor 1) 8 c := by decide +kernel

lemma triple_reduction_1_9 : ∀ c : Fin 75,
    9 < c → tripleAnchor 1 ≠ 9 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 9 c).Valid (tripleAnchor 1) 9 c := by decide +kernel

lemma triple_reduction_1_10 : ∀ c : Fin 75,
    10 < c → tripleAnchor 1 ≠ 10 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 10 c).Valid (tripleAnchor 1) 10 c := by decide +kernel

lemma triple_reduction_1_11 : ∀ c : Fin 75,
    11 < c → tripleAnchor 1 ≠ 11 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 11 c).Valid (tripleAnchor 1) 11 c := by decide +kernel

lemma triple_reduction_1_12 : ∀ c : Fin 75,
    12 < c → tripleAnchor 1 ≠ 12 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 12 c).Valid (tripleAnchor 1) 12 c := by decide +kernel

lemma triple_reduction_1_13 : ∀ c : Fin 75,
    13 < c → tripleAnchor 1 ≠ 13 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 13 c).Valid (tripleAnchor 1) 13 c := by decide +kernel

lemma triple_reduction_1_14 : ∀ c : Fin 75,
    14 < c → tripleAnchor 1 ≠ 14 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 14 c).Valid (tripleAnchor 1) 14 c := by decide +kernel

lemma triple_reduction_1_15 : ∀ c : Fin 75,
    15 < c → tripleAnchor 1 ≠ 15 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 15 c).Valid (tripleAnchor 1) 15 c := by decide +kernel

lemma triple_reduction_1_16 : ∀ c : Fin 75,
    16 < c → tripleAnchor 1 ≠ 16 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 16 c).Valid (tripleAnchor 1) 16 c := by decide +kernel

lemma triple_reduction_1_17 : ∀ c : Fin 75,
    17 < c → tripleAnchor 1 ≠ 17 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 17 c).Valid (tripleAnchor 1) 17 c := by decide +kernel

lemma triple_reduction_1_18 : ∀ c : Fin 75,
    18 < c → tripleAnchor 1 ≠ 18 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 18 c).Valid (tripleAnchor 1) 18 c := by decide +kernel

lemma triple_reduction_1_19 : ∀ c : Fin 75,
    19 < c → tripleAnchor 1 ≠ 19 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 19 c).Valid (tripleAnchor 1) 19 c := by decide +kernel

lemma triple_reduction_1_20 : ∀ c : Fin 75,
    20 < c → tripleAnchor 1 ≠ 20 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 20 c).Valid (tripleAnchor 1) 20 c := by decide +kernel

lemma triple_reduction_1_21 : ∀ c : Fin 75,
    21 < c → tripleAnchor 1 ≠ 21 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 21 c).Valid (tripleAnchor 1) 21 c := by decide +kernel

lemma triple_reduction_1_22 : ∀ c : Fin 75,
    22 < c → tripleAnchor 1 ≠ 22 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 22 c).Valid (tripleAnchor 1) 22 c := by decide +kernel

lemma triple_reduction_1_23 : ∀ c : Fin 75,
    23 < c → tripleAnchor 1 ≠ 23 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 23 c).Valid (tripleAnchor 1) 23 c := by decide +kernel

lemma triple_reduction_1_24 : ∀ c : Fin 75,
    24 < c → tripleAnchor 1 ≠ 24 → tripleAnchor 1 ≠ c →
      (tripleReduction 1 24 c).Valid (tripleAnchor 1) 24 c := by decide +kernel

end FiveColour.Physical
