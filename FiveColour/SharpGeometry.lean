module
public import FiveColour.RingGeometry
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- An opposite-repeat target shares at least two corners with every source. -/
lemma opposite_corner_bits (s : Fin 75) : ∀ t,
    OppositeRepeat (catalogue t) → cornerMissBits s t ≤ 6 := by
  fin_cases s <;> decide +kernel
lemma opposite_corner_missing (c : Cube) (hc : UsesAllColours c) (t : Fin 75)
    (ht : OppositeRepeat (catalogue t)) : missingCorners c (catalogue t) ≤ 6 := by
  have he : missingCorners c (catalogue t) = missingCorners (catalogue (catalogueIndex c)) (catalogue t) := by
    unfold missingCorners
    congr 1; ext k; simp [fits_catalogueIndex c hc]
  rw [he,missingCorners_bits]
  exact opposite_corner_bits _ _ ht

lemma common_pair_bits (p : Fin 10) : ∀ s t,
    ¬ HasPairBit s p → ¬ HasPairBit t p → OppositeRepeat (catalogue t) →
      cornerMissBits s t ≤ 4 ∧ cornerMissBits t s + edgeMissBits t s ≤ 7 := by
  fin_cases p <;> decide +kernel
lemma common_pair_geometry (p : Fin 10) (s t : Fin 75)
    (hs : ¬ HasPair (catalogue s) p) (ht : ¬ HasPair (catalogue t) p)
    (ho : OppositeRepeat (catalogue t)) :
    missingCorners (catalogue s) (catalogue t) ≤ 4 ∧
      missingCorners (catalogue t) (catalogue s) + missingEdges (catalogue t) (catalogue s) ≤ 7 := by
  simpa only [HasPairBit,edgeBits_correct,HasPair,← missingCorners_bits,← missingEdges_bits]
    using common_pair_bits p s t
      (by simpa only [HasPairBit,edgeBits_correct,HasPair] using hs)
      (by simpa only [HasPairBit,edgeBits_correct,HasPair] using ht) ho

def PairDisjoint (p r : Fin 10) : Prop :=
  pairFirst p ≠ pairFirst r ∧ pairFirst p ≠ pairSecond r ∧
  pairSecond p ≠ pairFirst r ∧ pairSecond p ≠ pairSecond r
instance (p r : Fin 10) : Decidable (PairDisjoint p r) := by unfold PairDisjoint; infer_instance
lemma missing_disjoint_bits : ∀ (p r : Fin 10) (i : Fin 75), p ≠ r →
    ¬ HasPairBit i p → ¬ HasPairBit i r → PairDisjoint p r := by decide +kernel
lemma missing_disjoint (p r : Fin 10) (i : Fin 75) (hpr : p ≠ r)
    (hp : ¬ HasPair (catalogue i) p) (hr : ¬ HasPair (catalogue i) r) : PairDisjoint p r := by
  apply missing_disjoint_bits p r i hpr
  · simpa only [HasPairBit,edgeBits_correct,HasPair] using hp
  · simpa only [HasPairBit,edgeBits_correct,HasPair] using hr
lemma no_three_disjoint : ∀ p r s, PairDisjoint p r → PairDisjoint p s → ¬ PairDisjoint r s := by
  decide +kernel
lemma opposite_no_mono (t : Fin 75) : OppositeRepeat (catalogue t) → ∀ e,
    catalogue t (edgeFaces e 0) ≠ catalogue t (edgeFaces e 1) := by
  fin_cases t <;> decide +kernel

lemma opposite_core {m q : ℕ} (cubes : Fin m → Cube) (t : Fin 75)
    (ht : OppositeRepeat (catalogue t)) (corners : Fin 8 ↪ Fin m)
    (hf : ∀ k, Fits (cubes (corners k)) (catalogue t) k) :
    ∃ f : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin m,
      ∀ p, FrameFits (cubes (f p)) (catalogue t) p.val := by
  let g : {p : FrameSlot q // CorePosition (catalogue t) p} → Fin 8 := fun p =>
    match p with
    | ⟨.inl k,_⟩ => k
    | ⟨.inr (e,_),h⟩ => False.elim (opposite_no_mono t ht e h)
  have hg (p) : Sum.inl (g p) = p.val := by
    rcases p with ⟨p,hp⟩
    cases p with
    | inl k => rfl
    | inr ep => exact False.elim (opposite_no_mono t ht ep.1 hp)
  let e : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin 8 :=
    ⟨g,fun a b he => Subtype.ext ((hg a).symm.trans ((congrArg Sum.inl he).trans (hg b)))⟩
  refine ⟨e.trans corners,?_⟩
  intro p
  rw [← hg p]
  exact hf (g p)

end FiveColour.Physical
