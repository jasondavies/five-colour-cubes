module
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import FiveColour.Matching
@[expose] public section
namespace FiveColour.Physical

theorem frameFinTwo : NeZero 2 := by infer_instance
theorem frameFinSix : NeZero 6 := by infer_instance

/-- The twelve geometric edges, with their outward face normals. -/
def edgeFaces : Fin 12 → Fin 2 → Fin 6 :=
  letI : NeZero 2 := frameFinTwo
  letI : NeZero 6 := frameFinSix
  ![![0,2], ![0,3], ![0,4], ![0,5], ![1,2], ![1,3],
    ![1,4], ![1,5], ![2,4], ![2,5], ![3,4], ![3,5]]

def HasEdge (c : Cube) (a b : Fin 5) : Prop :=
  ∃ f g : Fin 6, f.val / 2 ≠ g.val / 2 ∧ c f = a ∧ c g = b

instance (c : Cube) (a b : Fin 5) : Decidable (HasEdge c a b) := by
  unfold HasEdge
  infer_instance

lemma hasEdge_symm {c : Cube} {a b : Fin 5} (h : HasEdge c a b) : HasEdge c b a := by
  obtain ⟨f,g,hfg,hf,hg⟩ := h
  exact ⟨g,f,hfg.symm,hg,hf⟩

/-- Two adjacent a-faces cannot both be opposite a face of colour b. -/
lemma monochromatic_supplies (c : Cube) (hc : UsesAllColours c) (a b : Fin 5)
    (ha : HasEdge c a a) : HasEdge c a b := by
  obtain ⟨f,g,hfg,hf,hg⟩ := ha
  obtain ⟨h,hh⟩ := hc b
  by_cases hfh : f.val / 2 ≠ h.val / 2
  · exact ⟨f,h,hfh,hf,hh⟩
  · exact ⟨g,h,by omega,hg,hh⟩

def cornerOfEdge : Fin 12 → Fin 8 := ![0,2,0,1,4,6,4,5,0,1,2,3]

lemma edge_adjacent : ∀ e : Fin 12,
    (edgeFaces e 0).val / 2 ≠ (edgeFaces e 1).val / 2 := by decide +kernel

lemma edge_corner_faces : ∀ e : Fin 12, ∃ a b : Fin 3,
    ColourCubes.exposedFaces (cornerOfEdge e) a = edgeFaces e 0 ∧
    ColourCubes.exposedFaces (cornerOfEdge e) b = edgeFaces e 1 := by decide +kernel

lemma rotation_adjacent : ∀ (r : Fin 24) (f g : Fin 6), f.val / 2 ≠ g.val / 2 →
    (ColourCubes.rotations r f).val / 2 ≠ (ColourCubes.rotations r g).val / 2 := by
  decide +kernel

lemma edge_rotation_complete : ∀ (e : Fin 12) (f g : Fin 6),
    f.val / 2 ≠ g.val / 2 → ∃ r : Fin 24,
      ColourCubes.rotations r (edgeFaces e 0) = f ∧
      ColourCubes.rotations r (edgeFaces e 1) = g := by decide +kernel

/-- Every target edge occurs on either of its chosen corner copies. -/
lemma edge_of_corner (c t : Cube) (e : Fin 12) (h : Fits c t (cornerOfEdge e)) :
    HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1)) := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨a,b,ha,hb⟩ := edge_corner_faces e
  exact ⟨_,_,rotation_adjacent r _ _ (edge_adjacent e),
    by simpa only [ha] using hr a, by simpa only [hb] using hr b⟩

/-- Matching the specified exterior faces by a proper rotation. -/
def FacesFit (c t : Cube) (faces : Finset (Fin 6)) : Prop :=
  ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧ ∀ f ∈ faces, c (r f) = t f

lemma edge_fits (c t : Cube) (e : Fin 12)
    (h : HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1))) :
    FacesFit c t {edgeFaces e 0,edgeFaces e 1} := by
  obtain ⟨f,g,hfg,hf,hg⟩ := h
  obtain ⟨r,hr0,hr1⟩ := edge_rotation_complete e f g hfg
  refine ⟨ColourCubes.rotations r,(ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩,?_⟩
  intro h hh
  rcases Finset.mem_insert.mp hh with rfl | hh
  · simpa only [hr0] using hf
  · rcases Finset.mem_singleton.mp hh with rfl
    simpa only [hr1] using hg

abbrev FrameSlot (q : ℕ) := Fin 8 ⊕ (Fin 12 × Fin q)

def frameExposed (q : ℕ) : FrameSlot q → Finset (Fin 6)
  | .inl k => Finset.univ.image (ColourCubes.exposedFaces k)
  | .inr p => {edgeFaces p.1 0,edgeFaces p.1 1}

def FrameSolvable {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) : Prop :=
  ∃ target, UsesAllColours target ∧ ∃ p : FrameSlot q ↪ Fin m,
    ∀ k, FacesFit (cubes (p k)) target (frameExposed q k)

lemma frameSlot_card (q : ℕ) : Fintype.card (FrameSlot q) = 12*q+8 := by
  simp [FrameSlot, Nat.add_comm]

/-- Join disjoint corner and edge placements to make the physical frame. -/
lemma frame_of_placements {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (t : Cube)
    (ht : UsesAllColours t) (corners : Fin 8 ↪ Fin m) (edges : (Fin 12 × Fin q) ↪ Fin m)
    (hc : ∀ k, Fits (cubes (corners k)) t k)
    (he : ∀ p, HasEdge (cubes (edges p)) (t (edgeFaces p.1 0)) (t (edgeFaces p.1 1)))
    (hd : ∀ k p, corners k ≠ edges p) : FrameSolvable q cubes := by
  refine ⟨t,ht,⟨Sum.elim corners edges,corners.injective.sumElim edges.injective hd⟩,?_⟩
  intro p
  cases p with
  | inl k =>
    obtain ⟨r,hr⟩ := hc k
    refine ⟨ColourCubes.rotations r,(ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩,?_⟩
    intro f hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
    exact hr a
  | inr p => exact edge_fits _ _ _ (he p)

end FiveColour.Physical
