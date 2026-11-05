module
public import Mathlib.Tactic.Linarith
public import FiveColour.FramePools
public import FiveColour.AnchorKinds
public import FiveColour.Multiplicity
public import FiveColour.Reserve
@[expose] public section
set_option Elab.async false
namespace FiveColour.Physical

lemma hasEdge_rotate (c : Cube) (r : Fin 24) (a b : Fin 5) :
    HasEdge (rotate c r) a b ↔ HasEdge c a b := by
  constructor
  · rintro ⟨f,g,hfg,hf,hg⟩
    exact ⟨_,_,rotation_adjacent r f g hfg,hf,hg⟩
  · rintro ⟨f,g,hfg,hf,hg⟩
    obtain ⟨f',rfl⟩ := (ColourCubes.rotations_bijective r).surjective f
    obtain ⟨g',rfl⟩ := (ColourCubes.rotations_bijective r).surjective g
    refine ⟨f',g',?_,hf,hg⟩
    contrapose! hfg
    have h : ∀ (r : Fin 24) (f g : Fin 6), f.val/2=g.val/2 →
        (ColourCubes.rotations r f).val/2=(ColourCubes.rotations r g).val/2 := by decide +kernel
    exact h r f' g' hfg

lemma hasEdge_catalogueIndex (c : Cube) (hc : UsesAllColours c) (a b : Fin 5) :
    HasEdge c a b ↔ HasEdge (catalogue (catalogueIndex c)) a b := by
  obtain ⟨r,hr⟩ := catalogueIndex_spec c hc
  conv_lhs => rw [hr]
  exact hasEdge_rotate _ _ _ _

def FrameFits (c t : Cube) {q : ℕ} : FrameSlot q → Prop
  | .inl k => Fits c t k
  | .inr p => HasEdge c (t (edgeFaces p.1 0)) (t (edgeFaces p.1 1))
instance (c t : Cube) (q : ℕ) : DecidablePred (@FrameFits c t q) := by
  intro p; cases p <;> unfold FrameFits <;> infer_instance

lemma frameFits_physical (c t : Cube) {q : ℕ} (p : FrameSlot q) (h : FrameFits c t p) :
    FacesFit c t (frameExposed q p) := by
  cases p with
  | inl k =>
    obtain ⟨r,hr⟩ := h
    refine ⟨ColourCubes.rotations r,(ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩,?_⟩
    intro f hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
    exact hr a
  | inr p => exact edge_fits _ _ _ h

lemma frameFits_catalogueIndex (c t : Cube) (hc : UsesAllColours c) {q : ℕ} (p : FrameSlot q) :
    FrameFits c t p ↔ FrameFits (catalogue (catalogueIndex c)) t p := by
  cases p with
  | inl k => exact fits_catalogueIndex c hc t k
  | inr p => exact hasEdge_catalogueIndex c hc _ _

def missingCorners (c t : Cube) := (Finset.univ.filter fun k => ¬ Fits c t k).card
def missingEdges (c t : Cube) := (Finset.univ.filter fun e : Fin 12 =>
  ¬ HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1))).card

/-- Untrusted edge bits, checked against physical face adjacency below. -/
def edgeBits : Fin 75 → ℕ := ![7595838,12234430,14273982,7598015,7598015,12300223,12300223,16371647,16371647,7598078,7598078,12300286,12300286,16371710,16371710,7597980,16514972,16773020,16514972,16773020,16371612,12300188,33288092,33288092,14413247,14413247,16445119,16445119,7596986,7602110,7602110,16509946,16449214,16772026,16509946,16449214,16772026,16444090,14417342,14417342,14412218,33287098,33287098,16508735,16508735,12267446,16478198,16482230,16770878,16478198,16482230,16770878,16475958,12562366,12562366,14380470,14675390,33255350,14675390,33255350,15323054,15462382,15466414,15462382,15466414,15460142,33285950,33285950,15396526,15724462,33222334,15724462,33222334,33148862,33148862]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgeBits_correct (s : Fin 75) : ∀ a b : Fin 5,
    (edgeBits s).testBit (5*a.val+b.val) = true ↔ HasEdge (catalogue s) a b := by
  fin_cases s <;> decide +kernel

def cornerMissBits (s t : Fin 75) := (Finset.univ.filter fun k : Fin 8 =>
  (Replay.fits t s).testBit k.val = false).card
def edgeMissBits (s t : Fin 75) := (Finset.univ.filter fun e : Fin 12 =>
  (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false).card

lemma missingCorners_bits (s t : Fin 75) : missingCorners (catalogue s) (catalogue t) = cornerMissBits s t := by
  unfold missingCorners cornerMissBits
  congr 1; ext k; simp [← incidence_fits]
lemma missingEdges_bits (s t : Fin 75) : missingEdges (catalogue s) (catalogue t) = edgeMissBits s t := by
  unfold missingEdges edgeMissBits
  congr 1; ext e; simp [← edgeBits_correct]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma frame_bit_bounds (s : Fin 75) : ∀ t : Fin 75,
    edgeMissBits s t ≤ 4 ∧ cornerMissBits s t + edgeMissBits s t ≤ 10 ∧
    (OppositeRepeat (catalogue t) → edgeMissBits s t ≤ 3 ∧ cornerMissBits s t + edgeMissBits s t ≤ 9) := by
  fin_cases s <;> decide +kernel

theorem frame_geometry_bounds (s : Fin 75) : ∀ t : Fin 75,
    missingEdges (catalogue s) (catalogue t) ≤ 4 ∧
    missingCorners (catalogue s) (catalogue t) + missingEdges (catalogue s) (catalogue t) ≤ 10 ∧
    (OppositeRepeat (catalogue t) → missingEdges (catalogue s) (catalogue t) ≤ 3 ∧
      missingCorners (catalogue s) (catalogue t) + missingEdges (catalogue s) (catalogue t) ≤ 9) := by
  simpa only [missingCorners_bits,missingEdges_bits] using frame_bit_bounds s

lemma frame_missing_card (c t : Cube) (q : ℕ) :
    (Finset.univ.filter fun p : FrameSlot q => ¬ FrameFits c t p).card =
      missingCorners c t + missingEdges c t * q := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeSum),Fintype.card_sum]
  congr 1
  · exact Fintype.card_subtype _
  · have he : {p : Fin 12 × Fin q // ¬ FrameFits c t (.inr p)} ≃
        ({e : Fin 12 // ¬ HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1))} × Fin q) :=
      { toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
        invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr he,Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype]
    rfl

lemma frame_missing_bound (c : Cube) (hc : UsesAllColours c) (t : Fin 75) (q : ℕ) (hq : 1 ≤ q) :
    (Finset.univ.filter fun p : FrameSlot q => ¬ FrameFits c (catalogue t) p).card ≤ 4*q+6 ∧
    (OppositeRepeat (catalogue t) →
      (Finset.univ.filter fun p : FrameSlot q => ¬ FrameFits c (catalogue t) p).card ≤ 3*q+6) := by
  have he : (Finset.univ.filter fun p : FrameSlot q => ¬ FrameFits c (catalogue t) p) =
      (Finset.univ.filter fun p : FrameSlot q => ¬ FrameFits (catalogue (catalogueIndex c)) (catalogue t) p) := by
    ext p; simp [frameFits_catalogueIndex c _ hc]
  rw [he,frame_missing_card]
  obtain ⟨he,hce,ho⟩ := frame_geometry_bounds (catalogueIndex c) t
  constructor
  · nlinarith [Nat.mul_le_mul_right (q-1) he, Nat.sub_add_cancel hq]
  · intro ht
    obtain ⟨he,hce⟩ := ho ht
    nlinarith [Nat.mul_le_mul_right (q-1) he, Nat.sub_add_cancel hq]

def HasPair (c : Cube) (p : Fin 10) := HasEdge c (pairFirst p) (pairSecond p)
instance (c : Cube) (p : Fin 10) : Decidable (HasPair c p) := inferInstanceAs (Decidable (HasEdge _ _ _))

def HasPairBit (i : Fin 75) (p : Fin 10) :=
  (edgeBits i).testBit (5*(pairFirst p).val+(pairSecond p).val) = true
instance (i : Fin 75) (p : Fin 10) : Decidable (HasPairBit i p) := inferInstanceAs (Decidable (_ = true))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_missing_pair_bits (i : Fin 75) : ∀ p r : Fin 10, p ≠ r →
    ¬ HasPairBit i p → ¬ HasPairBit i r →
    OppositeRepeat (catalogue i) ∧ ∀ j : Fin 75,
      ¬ HasPairBit j p → ¬ HasPairBit j r → j=i := by
  fin_cases i <;> decide +kernel

theorem two_missing_pairs (i : Fin 75) : ∀ p r : Fin 10, p ≠ r →
    ¬ HasPair (catalogue i) p → ¬ HasPair (catalogue i) r →
    OppositeRepeat (catalogue i) ∧ ∀ j : Fin 75,
      ¬ HasPair (catalogue j) p → ¬ HasPair (catalogue j) r → j=i := by
  simpa only [HasPairBit,edgeBits_correct,HasPair] using two_missing_pair_bits i

set_option maxRecDepth 100000 in
lemma mono_edge_unique (t : Fin 75) : ∀ a : Fin 5,
    (Finset.univ.filter fun e : Fin 12 => catalogue t (edgeFaces e 0) = a ∧
      catalogue t (edgeFaces e 1) = a).card ≤ 1 := by
  fin_cases t <;> decide +kernel

lemma frameFits_self (t : Cube) {q : ℕ} (p : FrameSlot q) : FrameFits t t p := by
  cases p with
  | inl k => exact fits_self t k
  | inr p => exact ⟨_,_,edge_adjacent p.1,rfl,rfl⟩
end FiveColour.Physical
