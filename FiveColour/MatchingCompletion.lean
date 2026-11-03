module
public import FiveColour.FrameCompletion
@[expose] public section
namespace FiveColour.FrameHall

/-- Complete an injective placement using a disjoint pool that fits every position. -/
theorem complete_with_pool {A P I : Type*} [Fintype A] [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I]
    (fits : I → P → Prop) (positions : A ↪ P) (copies : A ↪ I)
    (hf : ∀ a, fits (copies a) (positions a)) (pool : Finset I)
    (hsize : Fintype.card P ≤ Fintype.card A + pool.card)
    (hpool : ∀ i ∈ pool, ∀ p, p ∉ Set.range positions → fits i p) (hdisjoint : ∀ a, copies a ∉ pool) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  classical
  let R := {p : P // p ∉ Set.range positions}
  have hR : Fintype.card R ≤ Fintype.card pool := by
    rw [Fintype.card_subtype_compl,Fintype.card_range]
    simpa using (show Fintype.card P - Fintype.card A ≤ pool.card by omega)
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le hR
  let g : A ⊕ R ↪ I := ⟨Sum.elim copies (fun p => (pick p).val),
    copies.injective.sumElim (Subtype.val_injective.comp pick.injective)
      (fun a p he => hdisjoint a (he.symm ▸ (pick p).property))⟩
  let out : A ⊕ R → P := Sum.elim positions Subtype.val
  have hinj : Function.Injective out := positions.injective.sumElim Subtype.val_injective
    (fun a p he => p.property ⟨a,he⟩)
  have hsurj : Function.Surjective out := by
    intro p
    by_cases hp : p ∈ Set.range positions
    · obtain ⟨a,rfl⟩ := hp; exact ⟨.inl a,rfl⟩
    · exact ⟨.inr ⟨p,hp⟩,rfl⟩
  let e := Equiv.ofBijective out ⟨hinj,hsurj⟩
  refine ⟨e.symm.toEmbedding.trans g,?_⟩
  intro p
  change fits (g (e.symm p)) p
  have he : out (e.symm p) = p := e.apply_symm_apply p
  generalize hz : e.symm p = z at *
  cases z with
  | inl a => rw [← he]; exact hf a
  | inr r => rw [← he]; exact hpool (pick r).val (pick r).property r.val r.property
end FiveColour.FrameHall
