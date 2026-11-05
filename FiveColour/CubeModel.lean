module
public import Mathlib.Tactic.Ring
public import FiveColour.FrameGeometry
@[expose] public section
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

end FiveColour.Physical
