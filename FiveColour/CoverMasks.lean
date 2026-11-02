module
public import FiveColour.PackedHallCore
public import FiveColour.RootCapacityDefs
public import FiveColour.Anchor
@[expose] public section
namespace FiveColour.Physical

/-- Decode a set of catalogue varieties from its low 75 bits. -/
def decodeVarieties (mask : Nat) : Finset (Fin 75) :=
  Finset.univ.filter fun i => mask.testBit i.val

lemma decode_neighbourhood (t : Fin 75) (d : Nat) :
    decodeVarieties (Packed.neighbourhoodMask t d) = varietyNeighbours t (cornerSet d) := by
  ext i
  simp only [decodeVarieties, varietyNeighbours, Finset.mem_filter, Finset.mem_univ,
    true_and, Packed.neighbourhoodMask_bit, cornerSet, incidence_fits]

lemma decode_remove (mask : Nat) (i : Fin 75) :
    decodeVarieties (mask &&& ((2^75-1) ^^^ (2^i.val))) = (decodeVarieties mask).erase i := by
  ext j
  simp only [decodeVarieties, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp [j.isLt, hv, Ne.symm h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cornerSet_complement : ∀ d : Fin 256, cornerSet (255-d.val) = (cornerSet d.val)ᶜ := by
  decide +kernel

/-- The anchor Hall neighbourhood with the anchor itself removed. -/
def coverBadMask (kind : Fin 2) (d : Fin 256) : Nat :=
  Packed.neighbourhoodMask (canonicalAnchor kind) (255-d.val) &&&
    ((2^75-1) ^^^ (2^(canonicalAnchor kind).val))

lemma coverBadMask_model (kind : Fin 2) (d : Fin 256) :
    decodeVarieties (coverBadMask kind d) = anchorBad (canonicalAnchor kind) (cornerSet d.val) := by
  rw [coverBadMask, decode_remove, decode_neighbourhood, cornerSet_complement]
  rfl

/-- Transport a mask by a map of varieties. Bitwise union also works for
noninjective maps, so no carry or permutation assumption is hidden here. -/
def transportMask (f : Fin 75 → Fin 75) (mask : Nat) : Nat :=
  (((List.finRange 75).filter fun i => mask.testBit i.val).map fun i => 2^(f i).val).foldr Nat.lor 0

lemma transportMask_model (f : Fin 75 → Fin 75) (mask : Nat) :
    decodeVarieties (transportMask f mask) = (decodeVarieties mask).image f := by
  ext j
  simp [decodeVarieties, transportMask, Packed.testBit_fold_lor, Nat.testBit_two_pow,
    Fin.ext_iff]

/-- The one omitted distinct/all-adjacent cover is the complement of the
anchor's two repeated-colour corners. The shared-corner argument must exclude it. -/
def omittedCover : Fin 256 := 252

/-- Exactly the numerical domain of the exported cover reduction. This leaves
exclusion of the special distinct/all-adjacent cover as an explicit premise. -/
def CoverEligible (kind : Fin 2) (m : Fin 8) (d : Fin 256) : Prop :=
  0 < m.val ∧ (cornerSet d.val).card + m.val ≤ 7 ∧
    ¬ (kind = 0 ∧ m = 1 ∧ d = omittedCover)

instance (kind : Fin 2) (m : Fin 8) (d : Fin 256) : Decidable (CoverEligible kind m d) := by
  unfold CoverEligible
  infer_instance

end FiveColour.Physical
