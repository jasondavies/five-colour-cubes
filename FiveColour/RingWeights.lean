module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import FiveColour.RingData
public import FiveColour.WeightedHall
@[expose] public section
namespace FiveColour.Physical.Ring
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Bounds (core : Bool) (t : Fin 9) (x : Fin 9 → ℕ) : Prop :=
  ∀ c ∈ cuts t, demand core t c ≤ ∑ s ∈ cutSources c.1, x s

/-- Every set of positions is dominated by one of ten Hall inequalities.
Only the nine-type compatibility pattern is enumerated here. -/
lemma cut_cover (core : Bool) (t : Fin 9) :
    ∀ D : Finset (Fin 9), (∀ k ∈ D, active core t k) →
      ∃ c ∈ cuts t, D.card ≤ demand core t c ∧
        ∀ s ∈ cutSources c.1, ∃ k ∈ D, fits t s k := by
  cases core <;> fin_cases t <;> decide +kernel

lemma match_of_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (typeOf : I → Fin 9) (core : Bool) (t : Fin 9)
    (h : Bounds core t (fun s => (Finset.univ.filter fun i => typeOf i = s).card)) :
    ∃ f : {k // active core t k} ↪ I, ∀ k, fits t (typeOf (f k)) k.val := by
  classical
  apply FrameHall.match_of_cuts typeOf (fun s (k : {k // active core t k}) => fits t s k.val)
    ((cuts t).map fun c => (cutSources c.1,demand core t c))
  · intro D
    let E := D.image Subtype.val
    have he : E.card = D.card := Finset.card_image_of_injective _ Subtype.val_injective
    obtain ⟨c,hc,hd,hs⟩ := cut_cover core t E (by
      intro k hk; obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hk; exact p.property)
    refine ⟨(cutSources c.1,demand core t c),List.mem_map.mpr ⟨c,hc,rfl⟩,by omega,?_⟩
    intro s hs'
    obtain ⟨k,hk,hfit⟩ := hs s hs'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨p,hp,hfit⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact h d hd

def O (x : Fin 9 → ℕ) := x 0 + x 1 + x 2
def P (x : Fin 9 → ℕ) := x 3 + x 4 + x 5
def M (x : Fin 9 → ℕ) := x 6 + x 7 + x 8

def Major (x : Fin 9 → ℕ) (t : Fin 9) : Prop :=
  (3 ≤ t.val ∧ t.val < 6 ∧ 8 ≤ P x ∧ 3 ≤ x t) ∨
  (6 ≤ t.val ∧ 8 ≤ M x ∧ 3 ≤ x t)

/-- Select an opposite target with maximal multiplicity, or a majority
orientation containing three copies of an adjacent-repeat target. -/
lemma choose_target (x : Fin 9 → ℕ) (h : O x + P x + M x = 11) :
    (∃ t : Fin 9, t.val < 3 ∧ Bounds true t x) ∨ ∃ t, Major x t := by
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
      have hP : 8 ≤ P x := by omega
      by_cases h3 : 3 ≤ x 3
      · exact ⟨3,Or.inl ⟨by decide,by decide,hP,h3⟩⟩
      by_cases h4 : 3 ≤ x 4
      · exact ⟨4,Or.inl ⟨by decide,by decide,hP,h4⟩⟩
      exact ⟨5,Or.inl ⟨by decide,by decide,hP,by unfold P at hP; omega⟩⟩
  · right
    have hM : 8 ≤ M x := by omega
    by_cases h6 : 3 ≤ x 6
    · exact ⟨6,Or.inr ⟨by decide,hM,h6⟩⟩
    by_cases h7 : 3 ≤ x 7
    · exact ⟨7,Or.inr ⟨by decide,hM,h7⟩⟩
    exact ⟨8,Or.inr ⟨by decide,hM,by unfold M at hM; omega⟩⟩

lemma major_corners (x : Fin 9 → ℕ) (t : Fin 9) (h : Major x t) :
    Bounds false t x := by
  fin_cases t <;>
    norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Major,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,P,M] at * <;>
    omega

lemma major_core (x : Fin 9 → ℕ) (t : Fin 9) (h : Major x t)
    (ho : 0 < O x ∨ (3 ≤ t.val ∧ t.val < 6 ∧ 9 ≤ P x) ∨ (6 ≤ t.val ∧ 9 ≤ M x)) :
    Bounds true t x := by
  fin_cases t <;>
    norm_num [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,Major,Bounds,cuts,demand,cutSources,Fin.sum_univ_succ,Finset.sum_filter,O,P,M] at * <;>
    omega

end FiveColour.Physical.Ring
