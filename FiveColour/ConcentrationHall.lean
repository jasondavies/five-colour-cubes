module
public import FiveColour.DeficitHall
@[expose] public section
namespace FiveColour.FrameHall

/-- If distinct labels cannot jointly miss more than d positions, a failed
matching whose small Hall sets are sound forces a large single-label pool. -/
theorem failure_concentrates {I P V : Type*} [Fintype I] [Fintype P]
    [DecidableEq I] [DecidableEq P] [DecidableEq V]
    (fits : I → P → Prop) [DecidableRel fits] (label : I → V) (d r : ℕ)
    (hsize : Fintype.card P ≤ Fintype.card I)
    (hsmall : ∀ D : Finset P, D.card ≤ d → D.card ≤ (neighbours fits D).card)
    (hmiss : ∀ i, (Finset.univ.filter fun p => ¬ fits i p).card ≤ d+r)
    (hseparate : ∀ i j, label i ≠ label j →
      (Finset.univ.filter fun p => ¬ fits i p ∧ ¬ fits j p).card ≤ d)
    (hfail : ¬ ∃ f : P ↪ I, ∀ p, fits (f p) p) :
    ∃ i, d < (Finset.univ.filter fun p => ¬ fits i p).card ∧
      Fintype.card I + 1 ≤ (Finset.univ.filter fun j => label j = label i).card + d+r := by
  classical
  have hbad : ∃ D : Finset P, (neighbours fits D).card < D.card := by
    by_contra hh; push Not at hh
    exact hfail (match_of_hall fits hh)
  obtain ⟨D,hD⟩ := hbad
  have hd : d < D.card := by by_contra hh; have := hsmall D (by omega); omega
  let absent := Finset.univ \ neighbours fits D
  have hcard : absent.card = Fintype.card I - (neighbours fits D).card := by
    simp [absent,Finset.card_sdiff]
  have hpos : 0 < absent.card := by have := Finset.card_le_univ D; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
  have hnot (j) (hj : j ∈ absent) : ∀ p ∈ D, ¬ fits j p := by
    intro p hp hfit
    apply (Finset.mem_sdiff.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,hfit⟩
  have hsub (j) (hj : j ∈ absent) : D ⊆ Finset.univ.filter fun p => ¬ fits j p :=
    fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnot j hj p hp⟩
  have hmax := (Finset.card_le_card (hsub i hi)).trans (hmiss i)
  have hlabels : absent ⊆ Finset.univ.filter fun j => label j = label i := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hn
    have hs : D ⊆ Finset.univ.filter fun p => ¬ fits j p ∧ ¬ fits i p :=
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnot j hj p hp,hnot i hi p hp⟩
    have := (Finset.card_le_card hs).trans (hseparate j i hn)
    omega
  refine ⟨i,hd.trans_le (Finset.card_le_card (hsub i hi)),?_⟩
  have := Finset.card_le_card hlabels
  omega

/-- Corners (or another exceptional subset) and well-supplied ordinary
positions verify all Hall inequalities up to d. -/
lemma small_hall_of_partial {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq I] [DecidableEq P]
    (fits : I → P → Prop) [DecidableRel fits]
    (special : P → Prop) [DecidablePred special]
    (f : {p // special p} ↪ I) (hf : ∀ p, fits (f p) p.val)
    (d : ℕ) (hmany : ∀ p, ¬ special p → d ≤ (Finset.univ.filter fun i => fits i p).card) :
    ∀ D : Finset P, D.card ≤ d → D.card ≤ (neighbours fits D).card := by
  intro D hd
  by_cases hs : ∀ p ∈ D, special p
  · exact partial_hall fits special f hf D hs
  · push Not at hs
    obtain ⟨p,hp,hps⟩ := hs
    apply hd.trans ((hmany p hps).trans (Finset.card_le_card ?_))
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,(Finset.mem_filter.mp hi).2⟩
end FiveColour.FrameHall
