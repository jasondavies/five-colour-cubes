module
public import FiveColour.ExtremalLocalGeometry
public import FiveColour.ExtremalDisjointChecks
public import FiveColour.ExtremalSixChecks0
public import FiveColour.ExtremalSixChecks1
public import FiveColour.ExtremalSixChecks2
public import FiveColour.ExtremalSixChecks3
public import FiveColour.ExtremalSixChecks4
public import FiveColour.ExtremalSixChecks5
public import FiveColour.ExtremalSixChecks6
public import FiveColour.ExtremalSixChecks7
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

def sixInventories : Fin 8 → List LocalInventory :=
  ![sixInventories0,sixInventories1,sixInventories2,sixInventories3,
    sixInventories4,sixInventories5,sixInventories6,sixInventories7]

theorem six_inventories_cover (k : Fin 8) :
    (sixInventories k).map LocalInventory.counts = sourceCompositions 7 8 := by
  fin_cases k
  · exact six_inventories_cover_0
  · exact six_inventories_cover_1
  · exact six_inventories_cover_2
  · exact six_inventories_cover_3
  · exact six_inventories_cover_4
  · exact six_inventories_cover_5
  · exact six_inventories_cover_6
  · exact six_inventories_cover_7

theorem six_inventories_valid (k : Fin 8) :
    ∀ w ∈ sixInventories k, w.Valid k 6 := by
  fin_cases k
  · exact six_inventories_valid_0
  · exact six_inventories_valid_1
  · exact six_inventories_valid_2
  · exact six_inventories_valid_3
  · exact six_inventories_valid_4
  · exact six_inventories_valid_5
  · exact six_inventories_valid_6
  · exact six_inventories_valid_7

theorem six_masks_valid (k : Fin 8) : ∀ (t i : Fin 75) (g : Fin 8),
    sixGroup k i = some g → ∀ q : Fin 8, (sixMasks k t g).testBit q.val = true →
      (Replay.fits t i).testBit q.val = true := by
  fin_cases k
  · exact six_masks_valid_0
  · exact six_masks_valid_1
  · exact six_masks_valid_2
  · exact six_masks_valid_3
  · exact six_masks_valid_4
  · exact six_masks_valid_5
  · exact six_masks_valid_6
  · exact six_masks_valid_7

lemma local_allocation {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (k : Fin 8) (a : ℕ) (w : LocalInventory)
    (hw : w.Valid k a) (ha : a ≤ multiplicity cubes 3)
    (hcap : ∀ g : Fin 7, w.counts g ≤ (localPools cubes k g.succ).card) :
    HasSolution cubes := by
  apply cornerAllocation_solves cubes (localPools cubes k) (sixMasks k)
    (Fin.cons a w.counts) w.placement (sourcePools_disjoint _) ?_ ?_ hw
  · intro g
    refine Fin.cases ?_ (fun j => hcap j) g
    simpa only [Fin.cons_zero, localPools_anchor] using ha
  · intro t g i hi q hq
    apply (fits_catalogueIndex _ (hc i) _ _).mpr
    exact (incidence_fits _ _ _).mp
      (six_masks_valid k t _ g (Finset.mem_filter.mp hi).2 q hq)

/-- Four anchor copies and four arbitrary disjoint sources; their varieties may repeat. -/
lemma four_disjoint_normalised {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (ha : 4 ≤ multiplicity cubes 3)
    (hd : 4 ≤ ∑ g : Fin 7, (localPools cubes 0 g.succ).card) : HasSolution cubes := by
  obtain ⟨v, hv, hle⟩ := exists_subcounts
    (fun g : Fin 7 => (localPools cubes 0 g.succ).card) 4 hd
  have hmem := mem_sourceCompositions v hv
  rw [← disjoint_inventories_cover] at hmem
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmem
  exact local_allocation cubes hc 0 4 w (disjoint_inventories_valid w hw) ha hle

lemma adjacent_six_impossible (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes)
    (hm : 6 ≤ multiplicity cubes 3) : False := by
  obtain ⟨K, hK, hb⟩ := anchor_cover cubes hc hno 3
  rcases K.eq_empty_or_nonempty with rfl | hne
  · have ht := localPools_empty_total cubes
    rw [Fin.sum_univ_succ, localPools_anchor] at ht
    have hd : 4 ≤ ∑ g : Fin 7, (localPools cubes 0 g.succ).card := by
      simp only [Finset.card_empty] at hb hK
      simp only [Nat.cast_add] at ht
      omega
    exact hno (four_disjoint_normalised cubes hc (by omega) hd)
  · obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp (show K.card = 1 from by
      have := Finset.card_pos.mpr hne
      omega)
    have hbnonneg : 0 ≤ Certificate.mass (multiplicityVector cubes) (anchorBad 3 {k}) :=
      Finset.sum_nonneg fun i _ => multiplicity_nonneg cubes i
    have ht := localPools_single_total cubes k
    rw [Fin.sum_univ_succ, localPools_anchor] at ht
    simp only [Finset.card_singleton] at hb hK
    have hsum : ∑ g : Fin 7, (localPools cubes k g.succ).card = 8 := by
      simp only [Nat.cast_add] at ht
      omega
    have hmem := mem_sourceCompositions (fun g : Fin 7 => (localPools cubes k g.succ).card) hsum
    rw [← six_inventories_cover k] at hmem
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hmem
    exact hno (local_allocation cubes hc k 6 w (six_inventories_valid k w hw) hm
      (fun g => (congrFun he g).le))

lemma opposite_six_impossible (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes)
    (hm : 6 ≤ multiplicity cubes 0) : False := by
  obtain ⟨K, hK, hb⟩ := anchor_cover cubes hc hno 0
  have hbad : anchorBad 0 K = Finset.univ.erase 0 := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact opposite_bad_empty
    · obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp (show K.card = 1 from by
        have := Finset.card_pos.mpr hne
        omega)
      exact opposite_bad_single k
  rw [hbad] at hb
  have ht := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 75)))
    (multiplicityVector cubes) (Finset.mem_univ (0 : Fin 75))
  change Certificate.mass (multiplicityVector cubes) (Finset.univ.erase 0) +
    (multiplicity cubes 0 : Int) = Certificate.mass (multiplicityVector cubes) Finset.univ at ht
  rw [multiplicity_total] at ht
  omega

/-- Independent of Threshold15: every fourteen-cube obstruction has multiplicity at most five. -/
theorem fourteen_multiplicity_le_five (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes) (a : Fin 75) :
    multiplicity cubes a ≤ 5 := by
  by_contra h
  obtain ⟨hc', hno', hm⟩ := normalised_counterexample cubes hc hno a
  have hk : anchorFor a = 0 ∨ anchorFor a = 3 := by
    unfold anchorFor
    split <;> simp
  rcases hk with hk | hk
  · rw [hk] at hm
    exact opposite_six_impossible _ hc' hno' (by omega)
  · rw [hk] at hm
    exact adjacent_six_impossible _ hc' hno' (by omega)

/-- Six identical varieties suffice in any fourteen physical sources. -/
theorem fourteen_six_suffices (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (a : Fin 75)
    (ha : 6 ≤ multiplicity cubes a) : HasSolution cubes := by
  by_contra hno
  have := fourteen_multiplicity_le_five cubes hc hno a
  omega

end FiveColour.Physical
