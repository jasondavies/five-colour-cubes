module
public import FiveColour.HallCuts
public import FiveColour.PackedHallData
public import FiveColour.PackedData
public import FiveColour.PackedSemantics
@[expose] public section
namespace FiveColour.Packed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Verify the transposed incidence table, independently of how it was generated. -/
lemma cornerSources_correct (t : Fin 75) : ∀ (i : Fin 75) (k : Fin 8),
    (cornerSources t k).testBit i.val = (Replay.fits t i).testBit k.val := by
  fin_cases t <;> decide +kernel

/-- Union the eight source masks selected by a target-corner mask. -/
def neighbourhoodMask (t : Fin 75) (d : Nat) : Nat :=
  (((List.finRange 8).filter fun k => d.testBit k.val).map (cornerSources t)).foldr Nat.lor 0

lemma testBit_fold_lor (xs : List Nat) (i : Nat) :
    (xs.foldr Nat.lor 0).testBit i = true ↔ ∃ a ∈ xs, a.testBit i = true := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

lemma neighbourhoodMask_bit (t i : Fin 75) (d : Nat) :
    (neighbourhoodMask t d).testBit i.val = true ↔
      ∃ k : Fin 8, d.testBit k.val = true ∧ (Replay.fits t i).testBit k.val = true := by
  simp only [neighbourhoodMask, testBit_fold_lor, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, ⟨k, hk, rfl⟩, ha⟩
    exact ⟨k, hk, by simpa only [cornerSources_correct] using ha⟩
  · rintro ⟨k, hd, hi⟩
    exact ⟨cornerSources t k, ⟨k, hd, rfl⟩, by simpa only [cornerSources_correct] using hi⟩

/-- Ignore arithmetic weights here: their correctness is proved by PackedCalibration. -/
def actualSignatures (t : Fin 75) : List (Nat × Int) :=
  (cuts[t.val]!).toList.map fun c => (c.mask, c.rhs)

def expectedSignatures (t : Fin 75) : List (Nat × Int) :=
  (List.range 255).map fun d => (neighbourhoodMask t (d+1), (Physical.maskCut t (d+1)).rhs)

/-- Decode the semantic fields of a packed Hall cut. -/
def signatureModel (s : Nat × Int) : Certificate.Cut 75 where
  neighbours := Finset.univ.filter fun i => s.1.testBit i.val = true
  rhs := s.2

lemma expectedSignature_model (t : Fin 75) (d : Nat) (hd : d < 256) :
    signatureModel (neighbourhoodMask t d, (Physical.maskCut t d).rhs) = Physical.maskCut t d := by
  have hn : (Finset.univ.filter fun i => (neighbourhoodMask t d).testBit i.val = true) =
      Finset.univ.filter (fun i => (Replay.fits t i).land d ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neighbourhoodMask_bit,
      Physical.mask_overlap_iff _ _ hd]
  simp only [signatureModel, Physical.maskCut, hn]

end FiveColour.Packed
