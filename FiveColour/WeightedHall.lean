module
public import FiveColour.FiniteHall
@[expose] public section
namespace FiveColour.FrameHall
open scoped BigOperators
variable {P I S : Type*} [Fintype P] [Fintype I] [Fintype S]
  [DecidableEq P] [DecidableEq I] [DecidableEq S]

omit [Fintype S] [DecidableEq I] in
/-- Counting copies by type gives the cardinality of any union of types. -/
lemma count_types (typeOf : I → S) (T : Finset S) :
    ∑ s ∈ T, (Finset.univ.filter fun i => typeOf i = s).card =
      (Finset.univ.filter fun i => typeOf i ∈ T).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

omit [Fintype S] [DecidableEq P] in
/-- A finite list of sufficient Hall inequalities can be checked once for a
compatibility pattern, and then used with arbitrary source multiplicities. -/
theorem match_of_cuts (typeOf : I → S) (fits : S → P → Prop) [DecidableRel fits]
    (cuts : List (Finset S × ℕ))
    (cover : ∀ D : Finset P, ∃ c ∈ cuts, D.card ≤ c.2 ∧
      ∀ s ∈ c.1, ∃ p ∈ D, fits s p)
    (bounds : ∀ c ∈ cuts, c.2 ≤ ∑ s ∈ c.1,
      (Finset.univ.filter fun i => typeOf i = s).card) :
    ∃ f : P ↪ I, ∀ p, fits (typeOf (f p)) p := by
  apply match_of_hall (fun i p => fits (typeOf i) p)
  intro D
  obtain ⟨c,hc,hd,hs⟩ := cover D
  have hb := bounds c hc
  rw [count_types] at hb
  apply hd.trans (hb.trans (Finset.card_le_card ?_))
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs _ (Finset.mem_filter.mp hi).2⟩

/-- A pool fitting every ordinary position, and a subpool fitting every
exceptional position, suffice if each meets the corresponding demand. -/
theorem match_of_two_pools (fits : I → P → Prop) [DecidableRel fits]
    (special : Finset P) (pool strong : Finset I)
    (hstrong : special.card ≤ strong.card)
    (hpool : Fintype.card P ≤ pool.card)
    (hs : ∀ i ∈ strong, ∀ p ∈ special, fits i p)
    (hp : ∀ i ∈ pool, ∀ p ∉ special, fits i p) :
    ∃ f : P ↪ I, ∀ p, fits (f p) p := by
  apply match_of_hall
  intro D
  by_cases hsub : D ⊆ special
  · by_cases hn : D.Nonempty
    · obtain ⟨p,hpD⟩ := hn
      exact (Finset.card_le_card hsub).trans (hstrong.trans (Finset.card_le_card
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hpD,hs i hi p (hsub hpD)⟩))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  · obtain ⟨p,hpD,hps⟩ := Finset.not_subset.mp hsub
    exact (Finset.card_le_univ D).trans (hpool.trans (Finset.card_le_card
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hpD,hp i hi p hps⟩))
end FiveColour.FrameHall
