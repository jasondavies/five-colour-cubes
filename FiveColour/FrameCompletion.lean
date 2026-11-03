module
public import FiveColour.FrameGeometry
@[expose] public section
namespace FiveColour.Physical

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

end FiveColour.Physical
