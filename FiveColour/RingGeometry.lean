module
public import FiveColour.RingData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical.Ring
def monoEdge : Fin 10 → Fin 9 → Fin 12 := ![![0,0,0,8,10,11,9,11,10],![0,0,0,8,10,11,9,11,10],![0,0,0,8,10,11,9,11,10],![0,0,0,8,10,11,9,11,10],![0,0,0,0,7,6,0,6,7],![0,0,0,0,7,6,0,6,7],![0,0,0,0,7,6,0,6,7],![0,0,0,0,4,5,0,4,5],![0,0,0,0,4,5,0,4,5],![0,0,0,0,4,5,0,4,5]]

lemma family_bits : ∀ p s, ¬ HasPairBit (variety p s) p := by decide +kernel
lemma family_missing (p : Fin 10) (s : Fin 9) : ¬ HasPair (catalogue (variety p s)) p := by
  simpa only [HasPairBit,edgeBits_correct,HasPair] using family_bits p s
lemma family_complete_bits : ∀ p i, ¬ HasPairBit i p → ∃ s, variety p s = i := by decide +kernel
lemma family_complete (p : Fin 10) (i : Fin 75) (h : ¬ HasPair (catalogue i) p) :
    ∃ s, variety p s = i := by
  apply family_complete_bits p i
  simpa only [HasPairBit,edgeBits_correct,HasPair] using h
lemma opposite_iff : ∀ p s, OppositeRepeat (catalogue (variety p s)) ↔ s.val < 3 := by decide +kernel
lemma corner_bijective : ∀ p t, Function.Bijective (cornerMap p t) := by decide +kernel
noncomputable def cornerEquiv (p : Fin 10) (t : Fin 9) : Fin 8 ≃ Fin 8 :=
  Equiv.ofBijective (cornerMap p t) (corner_bijective p t)

lemma corner_bits : ∀ p t s (k : Fin 8),
    (Replay.fits (variety p t) (variety p s)).testBit (cornerMap p t k).val =
      (mask t s).testBit k.val := by decide +kernel
lemma corner_fits (p : Fin 10) (t s : Fin 9) (k : Fin 8) :
    Fits (catalogue (variety p s)) (catalogue (variety p t)) (cornerMap p t k) ↔
      fits t s k.castSucc := by
  rw [← incidence_fits,corner_bits]
  rfl

lemma mono_only : ∀ p t e,
    catalogue (variety p t) (edgeFaces e 0) = catalogue (variety p t) (edgeFaces e 1) ↔
      3 ≤ t.val ∧ e = monoEdge p t := by decide +kernel
lemma mono_bits : ∀ p t s, 3 ≤ t.val →
    (edgeBits (variety p s)).testBit
      (5*(catalogue (variety p t) (edgeFaces (monoEdge p t) 0)).val +
        (catalogue (variety p t) (edgeFaces (monoEdge p t) 1)).val) =
      (mask t s).testBit 8 := by decide +kernel

def slot (p : Fin 10) (t : Fin 9) (k : Fin 9) : FrameSlot 1 :=
  if h : k.val < 8 then .inl (cornerMap p t ⟨k.val,h⟩) else .inr (monoEdge p t,0)
lemma slot_core : ∀ p t k, active true t k → CorePosition (catalogue (variety p t)) (slot p t k) := by
  decide +kernel

def coreSlot (p : Fin 10) (t : Fin 9) (k : {k // active true t k}) :
    {pos : FrameSlot 1 // CorePosition (catalogue (variety p t)) pos} :=
  ⟨slot p t k.val,slot_core p t k.val k.property⟩
lemma coreSlot_bijective : ∀ p t, Function.Bijective (coreSlot p t) := by decide +kernel
noncomputable def coreEquiv (p : Fin 10) (t : Fin 9) :=
  Equiv.ofBijective (coreSlot p t) (coreSlot_bijective p t)

lemma slot_fits (p : Fin 10) (t s : Fin 9) (k : Fin 9) (hk : active true t k) :
    FrameFits (catalogue (variety p s)) (catalogue (variety p t)) (slot p t k) ↔ fits t s k := by
  unfold slot
  split_ifs with h
  · exact corner_fits p t s ⟨k.val,h⟩
  · have he : k = 8 := Fin.ext (by omega)
    subst k
    change HasEdge _ _ _ ↔ _
    rw [← edgeBits_correct,mono_bits p t s (by rcases hk with hk | hk <;> simp_all)]
    rfl

/-- Compatibility of an arbitrary extra variety with the nine core positions. -/
def extraFits (p : Fin 10) (t : Fin 9) (w : Fin 75) (k : Fin 9) : Prop :=
  if h : k.val < 8 then
    (Replay.fits (variety p t) w).testBit (cornerMap p t ⟨k.val,h⟩).val = true
  else (edgeBits w).testBit
    (5*(catalogue (variety p t) (edgeFaces (monoEdge p t) 0)).val +
      (catalogue (variety p t) (edgeFaces (monoEdge p t) 1)).val) = true
instance (p : Fin 10) (t : Fin 9) (w : Fin 75) : DecidablePred (extraFits p t w) := by
  intro k; unfold extraFits; split_ifs <;> infer_instance
lemma extraFits_correct (p : Fin 10) (t : Fin 9) (w : Fin 75) (k : Fin 9) :
    extraFits p t w k ↔ FrameFits (catalogue w) (catalogue (variety p t)) (slot p t k) := by
  unfold extraFits slot
  split_ifs with h
  · exact incidence_fits _ _ _
  · exact edgeBits_correct _ _ _

def oppositeOf (t : Fin 9) : Fin 9 := ⟨t.val % 3,by omega⟩
/-- If the extra cube fits none of a majority target's core, it fits a
corner in the other half of the corresponding opposite-repeat target. -/
lemma extra_alternative (p : Fin 10) : ∀ t w, 3 ≤ t.val →
    (¬ ∃ k, active true t k ∧ extraFits p t w k) →
      ∃ k, active true (oppositeOf t) k ∧ ¬ fits (oppositeOf t) t k ∧
        extraFits p (oppositeOf t) w k := by
  fin_cases p <;> decide +kernel

end FiveColour.Physical.Ring
