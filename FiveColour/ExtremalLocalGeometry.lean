module
public import FiveColour.ExtremalLocalData
public import FiveColour.AnchorNormalisation
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

lemma six_group_anchor : ∀ (k : Fin 8) (i : Fin 75),
    sixGroup k i = some 0 ↔ i = 3 := by decide +kernel

lemma six_group_empty : ∀ i : Fin 75,
    sixGroup 0 i = none ↔ i ∈ anchorBad 3 ∅ := by decide +kernel

lemma six_group_single (k : Fin 8) : ∀ i : Fin 75,
    sixGroup k i = none ↔ i ∈ anchorBad 3 {k} := by
  fin_cases k <;> decide +kernel

lemma opposite_bad_empty : anchorBad 0 ∅ = Finset.univ.erase 0 := by decide +kernel
lemma opposite_bad_single (k : Fin 8) : anchorBad 0 {k} = Finset.univ.erase 0 := by
  fin_cases k <;> decide +kernel

def localPools {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :=
  sourcePools (fun i => sixGroup k (catalogueIndex (cubes i)))

lemma localPools_anchor {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    (localPools cubes k 0).card = multiplicity cubes 3 := by
  simp only [localPools, sourcePools, six_group_anchor, multiplicity]

lemma localPools_empty_total {n : ℕ} (cubes : Fin n → Cube) :
    (∑ g, ((localPools cubes 0) g).card : ℕ) +
      Certificate.mass (multiplicityVector cubes) (anchorBad 3 ∅) = (n : Int) := by
  rw [mass_multiplicity]
  have h := sourcePools_total (fun i => sixGroup 0 (catalogueIndex (cubes i)))
  simp only [six_group_empty] at h
  exact_mod_cast h

lemma localPools_single_total {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    (∑ g, ((localPools cubes k) g).card : ℕ) +
      Certificate.mass (multiplicityVector cubes) (anchorBad 3 {k}) = (n : Int) := by
  rw [mass_multiplicity]
  have h := sourcePools_total (fun i => sixGroup k (catalogueIndex (cubes i)))
  simp only [six_group_single k] at h
  exact_mod_cast h

lemma six_group_unpopulated : ∀ (k : Fin 8) (g : Fin 7),
    4 + singletonCount k ≤ g.val → ∀ i : Fin 75, sixGroup k i ≠ some g.succ := by
  decide +kernel

lemma six_group_disjoint_index : ∀ (k : Fin 8) (g : Fin 4) (i : Fin 75),
    sixGroup k i = some ⟨g.val+1, by omega⟩ ↔ disjointGroup i = some g := by
  decide +kernel

lemma six_group_disjoint (k : Fin 8) (g : Fin 4) (i : Fin 75) :
    sixGroup k i = some ⟨g.val+1, by omega⟩ ↔ sixGroup 0 i = some ⟨g.val+1, by omega⟩ := by
  simp only [six_group_disjoint_index]

lemma six_group_singleton : ∀ (k : Fin 8) (r : Fin 3) (i : Fin 75),
    sixGroup k i = some ⟨r.val+5, by omega⟩ → singletonVariety k r = some i := by
  decide +kernel

/-- Calibrate all bits of each shared mask with one containment identity. -/
lemma disjoint_masks_subset : ∀ (t i : Fin 75) (g : Fin 4),
    disjointGroup i = some g →
      (disjointMasks t g).land (Replay.fits t i) = disjointMasks t g := by
  decide +kernel

lemma disjoint_masks_valid (t i : Fin 75) (g : Fin 4)
    (hg : disjointGroup i = some g) (q : Fin 8)
    (hq : (disjointMasks t g).testBit q.val = true) : (Replay.fits t i).testBit q.val = true := by
  have h := congrArg (fun mask : ℕ => mask.testBit q.val) (disjoint_masks_subset t i g hg)
  simpa only [Nat.land_eq, Nat.testBit_land, hq, Bool.true_and] using h

/-- The other columns reuse incidence directly; no repeated geometry table is needed. -/
theorem six_masks_valid (k : Fin 8) (t i : Fin 75) (g : Fin 8)
    (hg : sixGroup k i = some g) (q : Fin 8)
    (hq : (sixMasks k t g).testBit q.val = true) : (Replay.fits t i).testBit q.val = true := by
  fin_cases g
  · have hi := (six_group_anchor k i).mp hg
    subst i
    exact hq
  · exact disjoint_masks_valid t i 0 ((six_group_disjoint_index k 0 i).mp hg) q hq
  · exact disjoint_masks_valid t i 1 ((six_group_disjoint_index k 1 i).mp hg) q hq
  · exact disjoint_masks_valid t i 2 ((six_group_disjoint_index k 2 i).mp hg) q hq
  · exact disjoint_masks_valid t i 3 ((six_group_disjoint_index k 3 i).mp hg) q hq
  · have hs := six_group_singleton k 0 i hg
    change ((singletonVariety k 0).elim 255 (Replay.fits t)).testBit q.val = true at hq
    simpa only [hs, Option.elim_some] using hq
  · have hs := six_group_singleton k 1 i hg
    change ((singletonVariety k 1).elim 255 (Replay.fits t)).testBit q.val = true at hq
    simpa only [hs, Option.elim_some] using hq
  · have hs := six_group_singleton k 2 i hg
    change ((singletonVariety k 2).elim 255 (Replay.fits t)).testBit q.val = true at hq
    simpa only [hs, Option.elim_some] using hq

lemma localPools_populated {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    populatedCounts k (fun g => (localPools cubes k g.succ).card) := by
  intro g hg
  have he : localPools cubes k g.succ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact six_group_unpopulated k g hg _ (Finset.mem_filter.mp hi).2
  change (localPools cubes k g.succ).card = 0
  rw [he, Finset.card_empty]

lemma localPools_disjoint_total {n : ℕ} (cubes : Fin n → Cube) (k : Fin 8) :
    (∑ g : Fin 7, (localPools cubes 0 g.succ).card) =
      disjointCount (fun g => (localPools cubes k g.succ).card) := by
  have he (g : Fin 4) : localPools cubes k ⟨g.val+1, by omega⟩ =
      localPools cubes 0 ⟨g.val+1, by omega⟩ := by
    ext i
    simp only [localPools, sourcePools, Finset.mem_filter, Finset.mem_univ, true_and]
    exact six_group_disjoint k g _
  have hz := localPools_populated cubes 0
  have h4 := hz 4 (by decide)
  have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide)
  change (localPools cubes 0 5).card = 0 at h4
  change (localPools cubes 0 6).card = 0 at h5
  change (localPools cubes 0 7).card = 0 at h6
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  change localPools cubes k 1 = localPools cubes 0 1 at h0
  change localPools cubes k 2 = localPools cubes 0 2 at h1
  change localPools cubes k 3 = localPools cubes 0 3 at h2
  change localPools cubes k 4 = localPools cubes 0 4 at h3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, disjointCount]
  change (localPools cubes 0 1).card + ((localPools cubes 0 2).card +
      ((localPools cubes 0 3).card + ((localPools cubes 0 4).card +
      ((localPools cubes 0 5).card + ((localPools cubes 0 6).card +
      ((localPools cubes 0 7).card + 0)))))) =
      (localPools cubes k 1).card + (localPools cubes k 2).card +
      (localPools cubes k 3).card + (localPools cubes k 4).card
  rw [h0,h1,h2,h3]
  omega

end FiveColour.Physical
