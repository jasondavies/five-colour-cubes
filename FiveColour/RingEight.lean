module
public import FiveColour.RingEleven
@[expose] public section
namespace FiveColour.Physical.Ring
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
def SmallMajor (x : Fin 9 → ℕ) (t : Fin 9) : Prop :=
  (3 ≤ t.val ∧ t.val < 6 ∧ 5 ≤ P x ∧ 2 ≤ x t) ∨
  (6 ≤ t.val ∧ 5 ≤ M x ∧ 2 ≤ x t)
lemma choose_eight (x : Fin 9 → ℕ) (h : O x + P x + M x = 8) :
    (∃ t : Fin 9, t.val < 3 ∧ Bounds true t x) ∨ ∃ t, SmallMajor x t := by
  by_cases hp : 4 ≤ O x + P x
  · by_cases hm : 4 ≤ O x + M x
    · left
      by_cases h01 : x 0 ≤ x 1
      · by_cases h12 : x 1 ≤ x 2
        · refine ⟨2,by decide,?_⟩
          norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,
            O,P,M] at *
          omega
        · refine ⟨1,by decide,?_⟩
          norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,
            O,P,M] at *
          omega
      · by_cases h02 : x 0 ≤ x 2
        · refine ⟨2,by decide,?_⟩
          norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,
            O,P,M] at *
          omega
        · refine ⟨0,by decide,?_⟩
          norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,
            O,P,M] at *
          omega
    · right
      have hP : 5 ≤ P x := by omega
      by_cases h3 : 2 ≤ x 3
      · exact ⟨3,Or.inl ⟨by decide,by decide,hP,h3⟩⟩
      by_cases h4 : 2 ≤ x 4
      · exact ⟨4,Or.inl ⟨by decide,by decide,hP,h4⟩⟩
      exact ⟨5,Or.inl ⟨by decide,by decide,hP,by unfold P at hP; omega⟩⟩
  · right
    have hM : 5 ≤ M x := by omega
    by_cases h6 : 2 ≤ x 6
    · exact ⟨6,Or.inr ⟨by decide,hM,h6⟩⟩
    by_cases h7 : 2 ≤ x 7
    · exact ⟨7,Or.inr ⟨by decide,hM,h7⟩⟩
    exact ⟨8,Or.inr ⟨by decide,hM,by unfold M at hM; omega⟩⟩

end FiveColour.Physical.Ring
