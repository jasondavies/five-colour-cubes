module
public import FiveColour.FiniteHall
@[expose] public section
namespace FiveColour.FrameHall
variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

omit [Fintype P] [DecidableEq P] [DecidableEq I] in
lemma partial_hall (fits : I → P → Prop) [DecidableRel fits]
    (special : P → Prop) [DecidablePred special]
    (placement : {p // special p} ↪ I) (hplacement : ∀ p, fits (placement p) p.val)
    (D : Finset P) (hs : ∀ p ∈ D, special p) : D.card ≤ (neighbours fits D).card := by
  let lift : D → {p // special p} := fun p => ⟨p.val,hs p.val p.property⟩
  have hinj : Function.Injective lift := fun a b he => Subtype.ext (congrArg (fun z : {p // special p} => z.val) he)
  let f : D ↪ I := ⟨fun p => placement (lift p),placement.injective.comp hinj⟩
  have hfit (p : D) : f p ∈ neighbours fits D :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val,p.property,hplacement (lift p)⟩
  let e : D ↪ (neighbours fits D) := ⟨fun p => ⟨f p,hfit p⟩,
    fun a b he => f.injective (congrArg Subtype.val he)⟩
  simpa using Fintype.card_le_of_embedding e

/-- One under-supplied class of positions can be repaired by a disjoint pool
whose members each miss fewer positions than that class has suppliers. -/
theorem match_of_one_deficit (fits : I → P → Prop) [DecidableRel fits]
    (d b : ℕ) (special : P → Prop) [DecidablePred special]
    (hsize : Fintype.card P ≤ Fintype.card I)
    (hmiss : ∀ i, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d)
    (placement : {p // special p} ↪ I) (hplacement : ∀ p, fits (placement p) p.val)
    (S V : Finset I) (hdisj : Disjoint S V) (hS : b ≤ S.card) (hSV : d ≤ S.card + V.card)
    (hV : ∀ i ∈ V, (Finset.univ.filter fun p => ¬ fits i p).card ≤ b)
    (hpositions : ∀ p, ¬ special p →
      d ≤ (Finset.univ.filter fun i => fits i p).card ∨ ∀ i ∈ S, fits i p) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_small_sets fits d hsize hmiss
  intro D hD
  by_cases hs : ∀ p ∈ D, special p
  · exact partial_hall fits special placement hplacement D hs
  · push Not at hs
    obtain ⟨p,hp,hps⟩ := hs
    rcases hpositions p hps with hm | hSfit
    · exact hD.trans (hm.trans (Finset.card_le_card fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,(Finset.mem_filter.mp hi).2⟩))
    have hSN : S ⊆ neighbours fits D := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,hSfit i hi⟩
    by_cases hd : D.card ≤ S.card
    · exact hd.trans (Finset.card_le_card hSN)
    have hVN : V ⊆ neighbours fits D := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_contra hn
      have hsub : D ⊆ Finset.univ.filter fun p => ¬ fits i p := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun hf => hn ⟨p,hp,hf⟩⟩
      have := (Finset.card_le_card hsub).trans (hV i hi)
      omega
    have hu := Finset.card_le_card (Finset.union_subset hSN hVN)
    rw [Finset.card_union_of_disjoint hdisj] at hu
    omega
omit [DecidableEq P] in
/-- A sufficiently large pool whose members each miss at most d positions,
together with d universal copies, gives a matching. -/
theorem match_of_pools (fits : I → P → Prop) [DecidableRel fits] (d : ℕ)
    (A V : Finset I) (hA : Fintype.card P ≤ A.card) (hV : d ≤ V.card)
    (hmiss : ∀ i ∈ A, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d)
    (hfull : ∀ i ∈ V, ∀ p, fits i p) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_hall
  intro D
  by_cases hn : D.Nonempty
  · obtain ⟨p,hp⟩ := hn
    by_cases hd : D.card ≤ d
    · exact hd.trans (hV.trans (Finset.card_le_card fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,hfull i hi p⟩))
    · apply (Finset.card_le_univ D).trans (hA.trans (Finset.card_le_card ?_))
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_contra hn
      have hsub : D ⊆ Finset.univ.filter fun p => ¬ fits i p := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun hf => hn ⟨p,hp,hf⟩⟩
      exact hd ((Finset.card_le_card hsub).trans (hmiss i hi))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
end FiveColour.FrameHall
