module
public import FiveColour.FrameGeometry
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
/-! Generic frame completion adapted from the companion four-to-three development.
No companion catalogue or threshold theorem is used. -/
namespace FiveColour.Physical

/-- The remaining positions: six face interiors and the interior of the cube. -/
abbrev FillerSlot (k : ℕ) := (Fin 6 × Fin k × Fin k) ⊕ (Fin k × Fin k × Fin k)
/-- Positions classified by how many of their coordinates lie on the boundary. -/
abbrev FullSlot (k : ℕ) := FrameSlot k ⊕ FillerSlot k

def fullExposed (k : ℕ) : FullSlot k → Finset (Fin 6)
  | .inl q => frameExposed k q
  | .inr (.inl q) => {q.1}
  | .inr (.inr _) => ∅

def FullSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Cube) : Prop :=
  ∃ target : Cube, UsesAllColours target ∧
    ∃ p : FullSlot k ↪ Fin m, ∀ q, FacesFit (cubes (p q)) target (fullExposed k q)

lemma fullSlot_card (k : ℕ) : Fintype.card (FullSlot k) = (k+2)^3 := by
  simp only [FullSlot, FillerSlot, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring

lemma full_requires_pieces {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (h : FullSolvable k cubes) : (k+2)^3 ≤ m := by
  obtain ⟨_,_,p,_⟩ := h
  simpa only [fullSlot_card,Fintype.card_fin] using Fintype.card_le_of_embedding p

lemma frame_of_full {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (h : FullSolvable k cubes) : FrameSolvable k cubes := by
  obtain ⟨t,ht,p,hp⟩ := h
  exact ⟨t,ht,Function.Embedding.inl.trans p,fun q => hp (.inl q)⟩

/-- Extend a placement by assigning the new positions to unused copies. -/
lemma embedding_extend_sum {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A ↪ C) (h : Fintype.card A + Fintype.card B ≤ Fintype.card C) :
    ∃ q : A ⊕ B ↪ C, ∀ a, q (.inl a) = p a := by
  classical
  let R := {c : C // c ∉ Set.range p}
  have hR : Fintype.card B ≤ Fintype.card R := by
    rw [Fintype.card_subtype_compl, Fintype.card_range]
    omega
  obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le hR
  refine ⟨⟨Sum.elim p (fun b => (r b).val), ?_⟩, fun _ => rfl⟩
  exact p.injective.sumElim (Subtype.val_injective.comp r.injective)
    (fun a b heq => (r b).property ⟨a, heq⟩)

lemma rotations_face_transitive : ∀ f g : Fin 6,
    ∃ r : Fin 24, ColourCubes.rotations r f = g := by decide +kernel

lemma fits_one_face (c t : Cube) (hc : UsesAllColours c) (f : Fin 6) :
    FacesFit c t {f} := by
  obtain ⟨g,hg⟩ := hc (t f)
  obtain ⟨r,hr⟩ := rotations_face_transitive f g
  refine ⟨ColourCubes.rotations r,(ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩,?_⟩
  intro h hh
  rcases Finset.mem_singleton.mp hh with rfl
  simpa only [hr] using hg

/-- Keep the frame placement, then fill face interiors using the common palette.
Completely internal positions impose no colour constraints. -/
lemma full_of_frame {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (hm : (k+2)^3 ≤ m)
    (h : FrameSolvable k cubes) : FullSolvable k cubes := by
  classical
  obtain ⟨t,ht,p,hp⟩ := h
  obtain ⟨q,hq⟩ := embedding_extend_sum (B := FillerSlot k) p (by
    have hcard : Fintype.card (FrameSlot k) + Fintype.card (FillerSlot k) = (k+2)^3 :=
      (Fintype.card_sum (α := FrameSlot k) (β := FillerSlot k)).symm.trans (fullSlot_card k)
    simpa only [Fintype.card_fin] using hcard.le.trans hm)

  refine ⟨t,ht,q,?_⟩
  intro pos
  cases pos with
  | inl pos => simpa only [hq, fullExposed] using hp pos
  | inr pos => cases pos with
    | inl pos => exact fits_one_face _ t (hc _) pos.1
    | inr pos =>
      refine ⟨ColourCubes.rotations 0,(ColourCubes.proper_rotation_iff _).mpr ⟨0,rfl⟩,?_⟩
      intro f hf
      exact False.elim (Finset.notMem_empty f hf)

/-- Completing a frame adds only the requirement that enough physical pieces remain. -/
theorem full_iff_frame_and_size {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) : FullSolvable k cubes ↔
      FrameSolvable k cubes ∧ (k+2)^3 ≤ m :=
  ⟨fun h => ⟨frame_of_full k cubes h,full_requires_pieces k cubes h⟩,
    fun h => full_of_frame k cubes hc h.2 h.1⟩

end FiveColour.Physical
