module
public import FiveColour.AnchorNormalisation
public import FiveColour.CoverReduction
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The twenty oriented corner types with exactly one repeated colour. -/
def doubleKeys : Finset Nat :=
  ((Finset.univ : Finset (Fin 5 × Fin 5)).filter fun p => p.1 ≠ p.2).image
    fun p => cornerKey ![p.1, p.1, p.2]

def doubleCorners (i : Fin 75) : Finset Nat :=
  (Finset.univ.image (catalogueCornerKey i)) ∩ doubleKeys

lemma doubleKeys_card : doubleKeys.card = 20 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma doubleCorners_card : ∀ i : Fin 75, ¬ OppositeRepeat (catalogue i) →
    (doubleCorners i).card = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Normalisation sends either repeated-colour corner of an adjacent anchor
into the two positions omitted by cover 252. -/
lemma normalised_double_slot : ∀ (i : Fin 75) (k : Fin 8),
    ¬ OppositeRepeat (catalogue i) → catalogueCornerKey i k ∈ doubleKeys →
      ColourCubes.Geometry.rotatedSlot (normalisationRotation i) k ∈
        (cornerSet omittedCover.val)ᶜ := by decide +kernel

lemma omittedCover_card : (cornerSet omittedCover.val).card = 6 := by decide +kernel

/-- Eleven distinct adjacent varieties cannot have disjoint pairs of repeated-colour corners. -/
theorem exists_shared_double (S : Finset (Fin 75)) (hS : 10 < S.card)
    (hadj : ∀ i ∈ S, ¬ OppositeRepeat (catalogue i)) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ ∃ key ∈ doubleCorners i, key ∈ doubleCorners j := by
  by_contra h
  have hd : (S : Set (Fin 75)).PairwiseDisjoint doubleCorners := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro key hki hkj
    exact h ⟨i, hi, j, hj, hij, key, hki, hkj⟩
  have hs : S.biUnion doubleCorners ⊆ doubleKeys := by
    apply Finset.biUnion_subset.mpr
    intro i _
    exact Finset.inter_subset_right
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hd, doubleKeys_card] at hc
  have he : ∑ i ∈ S, (doubleCorners i).card = 2*S.card := by
    calc
      _ = ∑ _i ∈ S, 2 := Finset.sum_congr rfl fun i hi => doubleCorners_card i (hadj i hi)
      _ = _ := by simp [Nat.mul_comm]
  rw [he] at hc
  omega

/-- A shared repeated-colour corner gives a non-anchor neighbour in the
exceptional cover after normalising the chosen adjacent anchor. -/
theorem normalised_shared_neighbour (i j : Fin 75) (hij : i ≠ j)
    (hi : ¬ OppositeRepeat (catalogue i))
    (hkey : ∃ key ∈ doubleCorners i, key ∈ doubleCorners j) :
    varietyEquiv (anchorSymmetry i) j ∈ anchorBad 3 (cornerSet omittedCover.val) := by
  obtain ⟨key, hki, hkj⟩ := hkey
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hki).1
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hkj).1
  have hfit : Fits (catalogue j) (catalogue i) k :=
    (incidence_fits i j k).mp ((incidence_keys i j k).mpr ⟨l, hl.trans hk.symm⟩)
  have ha : anchorFor i = 3 := by simp [anchorFor, hi]
  have hr : recolour (normalisingColour i) (catalogue i) =
      rotate (catalogue 3) (normalisationRotation i) := by
    unfold rotate ColourCubes.rotate
    funext f
    simpa only [ha] using normalisation_faces i f
  have hf := (fits_recolour (normalisingColour i) (catalogue j) (catalogue i) k).mpr hfit
  rw [hr, fits_rotate_target] at hf
  have hc : UsesAllColours ((anchorSymmetry i).apply (catalogue j)) :=
    ((anchorSymmetry i).usesAllColours_apply _).mpr (catalogue_uses_all_colours j)
  have hf' := (fits_catalogueIndex _ hc _ _).mp hf
  have hn : varietyEquiv (anchorSymmetry i) j ≠ 3 := by
    intro hji
    have hn := normalise_variety i
    rw [ha] at hn
    exact hij ((varietyEquiv (anchorSymmetry i)).injective (hn.trans hji.symm))
  apply Finset.mem_erase.mpr
  refine ⟨hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ColourCubes.Geometry.rotatedSlot (normalisationRotation i) k, ?_, hf'⟩⟩
  exact normalised_double_slot i k hi (hk.symm ▸ (Finset.mem_inter.mp hki).2)

/-- The exceptional cover has positive non-anchor mass whenever the chosen
anchor shares a repeated-colour corner with another present variety. -/
theorem normalised_omitted_mass_pos {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (i j : Fin 75) (hij : i ≠ j)
    (hi : ¬ OppositeRepeat (catalogue i)) (hj : 0 < multiplicity cubes j)
    (hkey : ∃ key ∈ doubleCorners i, key ∈ doubleCorners j) :
    0 < Certificate.mass (multiplicityVector (fun q => (anchorSymmetry i).apply (cubes q)))
      (anchorBad 3 (cornerSet omittedCover.val)) := by
  have hmem := normalised_shared_neighbour i j hij hi hkey
  have hsum := Finset.single_le_sum
    (fun k _ => multiplicity_nonneg (fun q => (anchorSymmetry i).apply (cubes q)) k) hmem
  change (multiplicity (fun q => (anchorSymmetry i).apply (cubes q))
    (varietyEquiv (anchorSymmetry i) j) : Int) ≤
      Certificate.mass (multiplicityVector (fun q => (anchorSymmetry i).apply (cubes q)))
        (anchorBad 3 (cornerSet omittedCover.val)) at hsum
  rw [multiplicity_apply _ cubes hc] at hsum
  omega

end FiveColour.Physical
