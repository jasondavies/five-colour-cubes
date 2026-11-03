module
public import FiveColour.FrameCompletion
public import FiveColour.RareGeometry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The direction parallel to an edge is the coordinate missing from its two normals. -/
def edgeAxis : Fin 12 → Fin 3 := ![2,2,1,1,2,2,1,1,0,0,0,0]
/-- Eight corners and a separate interval of positions on every geometric edge. -/
abbrev RectSlot (lengths : Fin 3 → ℕ) := Fin 8 ⊕ (Σ e : Fin 12, Fin (lengths (edgeAxis e)))
def rectExposed (lengths : Fin 3 → ℕ) : RectSlot lengths → Finset (Fin 6)
  | .inl k => Finset.univ.image (ColourCubes.exposedFaces k)
  | .inr e => {edgeFaces e.1 0,edgeFaces e.1 1}
def RectFits (c t : Cube) {lengths : Fin 3 → ℕ} : RectSlot lengths → Prop
  | .inl k => Fits c t k
  | .inr e => HasEdge c (t (edgeFaces e.1 0)) (t (edgeFaces e.1 1))
instance (c t : Cube) (lengths : Fin 3 → ℕ) : DecidablePred (@RectFits c t lengths) := by
  intro p; cases p <;> unfold RectFits <;> infer_instance

def RectSolvable {n : ℕ} (lengths : Fin 3 → ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ target, UsesAllColours target ∧ ∃ f : RectSlot lengths ↪ Fin n,
    ∀ p, FacesFit (cubes (f p)) target (rectExposed lengths p)

/-- The three side lengths are unordered: an assignment to the coordinate axes
is part of the assembly. No reflection of an individual source is allowed. -/
def BoxFrameSolvable {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ axes : Equiv.Perm (Fin 3), RectSolvable (fun i => ![a-2,b-2,c-2] (axes i)) cubes

lemma rectSlot_card (l : Fin 3 → ℕ) : Fintype.card (RectSlot l) = 8 + 4 * ∑ i, l i := by
  unfold RectSlot
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [edgeAxis,Fin.sum_univ_succ]
  ring
lemma rectFits_physical (c t : Cube) {l : Fin 3 → ℕ} (p : RectSlot l) (h : RectFits c t p) :
    FacesFit c t (rectExposed l p) := by
  cases p with
  | inl k => exact frameFits_physical c t (.inl k : FrameSlot 0) h
  | inr e => exact edge_fits c t e.1 h
lemma rectFits_catalogueIndex (c t : Cube) (hc : UsesAllColours c)
    {l : Fin 3 → ℕ} (p : RectSlot l) :
    RectFits c t p ↔ RectFits (catalogue (catalogueIndex c)) t p := by
  cases p with
  | inl k => exact fits_catalogueIndex c hc t k
  | inr e => exact hasEdge_catalogueIndex c hc _ _
lemma rect_of_match {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube) (t : Fin 75)
    (h : ∃ f : RectSlot l ↪ Fin n, ∀ p, RectFits (cubes (f p)) (catalogue t) p) :
    RectSolvable l cubes := by
  obtain ⟨f,hf⟩ := h
  exact ⟨catalogue t,catalogue_uses_all_colours t,f,fun p => rectFits_physical _ _ p (hf p)⟩
lemma rect_hasSolution {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube)
    (h : RectSolvable l cubes) : HasSolution cubes := by
  obtain ⟨t,ht,f,hf⟩ := h
  refine ⟨t,ht,Function.Embedding.inl.trans f,?_⟩
  intro k
  obtain ⟨r,hr,hfit⟩ := hf (.inl k)
  obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
  exact ⟨r,fun j => hfit _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
lemma box_frame_hasSolution {n a b c : ℕ} (cubes : Fin n → Cube)
    (h : BoxFrameSolvable a b c cubes) : HasSolution cubes := by
  obtain ⟨_,h⟩ := h
  exact rect_hasSolution _ cubes h

/-- Face interiors are indexed by their normal and their two free coordinates. -/
def faceAxis₁ : Fin 6 → Fin 3 := ![1,1,0,0,0,0]
def faceAxis₂ : Fin 6 → Fin 3 := ![2,2,2,2,1,1]
abbrev RectFiller (l : Fin 3 → ℕ) :=
  (Σ f : Fin 6, Fin (l (faceAxis₁ f)) × Fin (l (faceAxis₂ f))) ⊕
    (Fin (l 0) × Fin (l 1) × Fin (l 2))
abbrev RectFullSlot (l : Fin 3 → ℕ) := RectSlot l ⊕ RectFiller l

def rectFullExposed (l : Fin 3 → ℕ) : RectFullSlot l → Finset (Fin 6)
  | .inl p => rectExposed l p
  | .inr (.inl p) => {p.1}
  | .inr (.inr _) => ∅
def RectFullSolvable {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ target, UsesAllColours target ∧ ∃ f : RectFullSlot l ↪ Fin n,
    ∀ p, FacesFit (cubes (f p)) target (rectFullExposed l p)
def BoxSolvable {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ axes : Equiv.Perm (Fin 3), RectFullSolvable (fun i => ![a-2,b-2,c-2] (axes i)) cubes

lemma rectFullSlot_card (l : Fin 3 → ℕ) :
    Fintype.card (RectFullSlot l) = ∏ i, (l i + 2) := by
  unfold RectFullSlot
  rw [Fintype.card_sum,rectSlot_card]
  unfold RectFiller
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin]
  simp [faceAxis₁,faceAxis₂,Fin.sum_univ_succ,Fin.prod_univ_succ]
  ring
lemma rect_frame_of_full {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube)
    (h : RectFullSolvable l cubes) : RectSolvable l cubes := by
  obtain ⟨t,ht,f,hf⟩ := h
  exact ⟨t,ht,Function.Embedding.inl.trans f,fun p => hf (.inl p)⟩
lemma rect_full_of_frame {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : (∏ i, (l i + 2)) ≤ n)
    (h : RectSolvable l cubes) : RectFullSolvable l cubes := by
  classical
  obtain ⟨t,ht,f,hf⟩ := h
  obtain ⟨g,hg⟩ := embedding_extend_sum (B := RectFiller l) f (by
    have he : Fintype.card (RectSlot l) + Fintype.card (RectFiller l) = ∏ i, (l i + 2) :=
      (Fintype.card_sum (α := RectSlot l) (β := RectFiller l)).symm.trans (rectFullSlot_card l)
    simpa only [Fintype.card_fin,he] using hn)
  refine ⟨t,ht,g,?_⟩
  intro p
  cases p with
  | inl p => simpa only [hg,rectFullExposed] using hf p
  | inr p => cases p with
    | inl p => exact fits_one_face _ _ (hc _) p.1
    | inr p =>
      refine ⟨ColourCubes.rotations 0,(ColourCubes.proper_rotation_iff _).mpr ⟨0,rfl⟩,?_⟩
      intro f hf
      exact False.elim (Finset.notMem_empty f hf)

lemma box_volume (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (axes : Equiv.Perm (Fin 3)) :
    (∏ i, (![a-2,b-2,c-2] (axes i) + 2)) = a*b*c := by
  rw [Equiv.prod_comp axes (fun j => ![a-2,b-2,c-2] j + 2)]
  simp [Fin.prod_univ_succ,Nat.sub_add_cancel ha,Nat.sub_add_cancel hb,Nat.sub_add_cancel hc,Nat.mul_assoc]
lemma box_full_of_frame {n : ℕ} (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (cubes : Fin n → Cube) (hcol : ∀ i, UsesAllColours (cubes i)) (hn : a*b*c ≤ n)
    (h : BoxFrameSolvable a b c cubes) : BoxSolvable a b c cubes := by
  obtain ⟨axes,h⟩ := h
  exact ⟨axes,rect_full_of_frame _ cubes hcol (by simpa only [box_volume a b c ha hb hc axes] using hn) h⟩
lemma box_requires_pieces {n a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (cubes : Fin n → Cube) (h : BoxSolvable a b c cubes) : a*b*c ≤ n := by
  obtain ⟨axes,_,_,f,_⟩ := h
  simpa only [rectFullSlot_card,box_volume a b c ha hb hc axes,Fintype.card_fin] using
    Fintype.card_le_of_embedding f
/-- Every assignment of the three axes is realised by a proper rotation. -/
lemma axes_realised (axes : Equiv.Perm (Fin 3)) : ∃ r : Fin 24, ∀ f : Fin 6,
    (ColourCubes.rotations r f).val / 2 = (axes ⟨f.val / 2,by omega⟩).val := by
  revert axes
  decide +kernel

lemma box_frame_card (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (axes : Equiv.Perm (Fin 3)) :
    Fintype.card (RectSlot (fun i => ![a-2,b-2,c-2] (axes i))) = 4*(a+b+c)-16 := by
  rw [rectSlot_card,Equiv.sum_comp axes (fun i => ![a-2,b-2,c-2] i)]
  simp [Fin.sum_univ_succ]
  omega
lemma box_frame_requires_pieces {n a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (cubes : Fin n → Cube) (h : BoxFrameSolvable a b c cubes) : 4*(a+b+c)-16 ≤ n := by
  obtain ⟨axes,_,_,f,_⟩ := h
  simpa only [box_frame_card a b c ha hb hc axes,Fintype.card_fin] using Fintype.card_le_of_embedding f
end FiveColour.Physical
