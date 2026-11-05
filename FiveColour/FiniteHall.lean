module
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Tactic.Push
@[expose] public section
namespace FiveColour.FrameHall
variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

def neighbours (fits : I → P → Prop) [DecidableRel fits] (D : Finset P) : Finset I :=
  Finset.univ.filter fun i => ∃ p ∈ D, fits i p

omit [DecidableEq P] in
theorem match_of_hall (fits : I → P → Prop) [DecidableRel fits]
    (h : ∀ D, D.card ≤ (neighbours fits D).card) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  let allowed := fun p => Finset.univ.filter fun i => fits i p
  have he (D : Finset P) : D.biUnion allowed = neighbours fits D := by
    ext i; simp [allowed,neighbours]
  obtain ⟨f,hf,hfits⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp
    (fun D => by simpa only [he] using h D)
  exact ⟨⟨f,hf⟩,fun p => (Finset.mem_filter.mp (hfits p)).2⟩

omit [DecidableEq P] in
/-- A source that misses at most d positions neighbours every set larger than d. -/
theorem match_of_small_sets (fits : I → P → Prop) [DecidableRel fits] (d : ℕ)
    (hsize : Fintype.card P ≤ Fintype.card I)
    (hmiss : ∀ i, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d)
    (hsmall : ∀ D : Finset P, D.card ≤ d → D.card ≤ (neighbours fits D).card) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_hall
  intro D
  by_cases hd : D.card ≤ d
  · exact hsmall D hd
  · have hall : neighbours fits D = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_contra hn
      have hsub : D ⊆ Finset.univ.filter fun p => ¬ fits i p := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun hf => hn ⟨p,hp,hf⟩⟩
      exact hd ((Finset.card_le_card hsub).trans (hmiss i))
    rw [hall,Finset.card_univ]
    exact (Finset.card_le_univ D).trans hsize

omit [DecidableEq P] in
/-- Enough copies fitting every position settle the small Hall sets. -/
theorem match_of_universal_copies (fits : I → P → Prop) [DecidableRel fits] (d : ℕ)
    (hsize : Fintype.card P ≤ Fintype.card I)
    (hmiss : ∀ i, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d)
    (copies : Finset I) (hcard : d ≤ copies.card) (hall : ∀ i ∈ copies, ∀ p, fits i p) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_small_sets fits d hsize hmiss
  intro D hd
  by_cases hn : D.Nonempty
  · obtain ⟨p,hp⟩ := hn
    exact hd.trans (hcard.trans (Finset.card_le_card fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,hall i hi p⟩))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- A partial matching handles exceptional positions; every other position
has at least d neighbours. -/
theorem match_of_partial (fits : I → P → Prop) [DecidableRel fits] (d : ℕ)
    (special : P → Prop) [DecidablePred special]
    (hsize : Fintype.card P ≤ Fintype.card I)
    (hmiss : ∀ i, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d)
    (placement : {p // special p} ↪ I) (hplacement : ∀ p, fits (placement p) p.val)
    (hmany : ∀ p, ¬ special p → d ≤ (Finset.univ.filter fun i => fits i p).card) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_small_sets fits d hsize hmiss
  intro D hd
  by_cases hs : ∀ p ∈ D, special p
  · let lift : D → {p // special p} := fun p => ⟨p.val,hs p.val p.property⟩
    have hinj : Function.Injective lift := fun a b he => Subtype.ext (congrArg (fun z : {p // special p} => z.val) he)
    let f : D ↪ I := ⟨fun p => placement (lift p),placement.injective.comp hinj⟩
    have hfit (p : D) : f p ∈ neighbours fits D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val,p.property,hplacement (lift p)⟩
    let e : D ↪ (neighbours fits D) := ⟨fun p => ⟨f p,hfit p⟩,
      fun a b he => f.injective (congrArg Subtype.val he)⟩
    simpa using Fintype.card_le_of_embedding e
  · push Not at hs
    obtain ⟨p,hp,hns⟩ := hs
    exact hd.trans ((hmany p hns).trans (Finset.card_le_card fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,(Finset.mem_filter.mp hi).2⟩))
end FiveColour.FrameHall
