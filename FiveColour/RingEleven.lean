module
public import FiveColour.RingWeights
public import FiveColour.RingGeometry
public import FiveColour.ExtraHall
@[expose] public section
namespace FiveColour.Physical.Ring
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Positions (core : Bool) (t : Fin 9) := {k // active core t k}
def sameSide (t s : Fin 9) : Prop :=
  (3 ≤ t.val ∧ t.val < 6 ∧ 3 ≤ s.val ∧ s.val < 6) ∨ (6 ≤ t.val ∧ 6 ≤ s.val)
instance (t : Fin 9) : DecidablePred (sameSide t) := by intro s; unfold sameSide; infer_instance
def nextSide (t : Fin 9) : Fin 9 := ![0,1,2,4,5,3,7,8,6] t
def special (t : Fin 9) : Finset (Positions true t) :=
  Finset.univ.filter fun k => ¬ fits t (nextSide t) k.val

lemma special_card : ∀ t, 3 ≤ t.val → (special t).card = 3 := by decide +kernel
lemma positions_card : ∀ t, 3 ≤ t.val → Fintype.card (Positions true t) = 9 := by decide +kernel
lemma self_fits : ∀ t k, active true t k → fits t t k := by decide +kernel
lemma side_fits : ∀ t s, 3 ≤ t.val → sameSide t s →
    ∀ k : Positions true t, k ∉ special t → fits t s k.val := by decide +kernel
def counts {I : Type*} [Fintype I] (typeOf : I → Fin 9) (s : Fin 9) : ℕ :=
  (Finset.univ.filter fun i => typeOf i = s).card
lemma counts_total {I : Type*} [Fintype I] [DecidableEq I] (typeOf : I → Fin 9) :
    O (counts typeOf) + P (counts typeOf) + M (counts typeOf) = Fintype.card I := by
  have h := FrameHall.count_types typeOf Finset.univ
  simpa [counts,O,P,M,Fin.sum_univ_succ,Nat.add_assoc] using h

def pool {I : Type*} [Fintype I] (typeOf : I → Fin 9) (t : Fin 9) : Finset I :=
  Finset.univ.filter fun i => sameSide t (typeOf i)
lemma pool_card {I : Type*} [Fintype I] [DecidableEq I] (typeOf : I → Fin 9) (t : Fin 9) :
    (pool typeOf t).card = ∑ s ∈ Finset.univ.filter (sameSide t), counts typeOf s := by
  simp only [counts]
  rw [FrameHall.count_types]
  simp [pool]
lemma major_pool {I : Type*} [Fintype I] [DecidableEq I] (typeOf : I → Fin 9) (t : Fin 9)
    (h : Major (counts typeOf) t) : 3 ≤ t.val ∧ 8 ≤ (pool typeOf t).card ∧ 3 ≤ counts typeOf t := by
  rw [pool_card]
  fin_cases t <;> simp [Major,sameSide,Fin.sum_univ_succ,Finset.sum_filter,P,M] at * <;> omega

lemma corners_of_core_bounds (x : Fin 9 → ℕ) (t : Fin 9) (h : Bounds true t x) : Bounds false t x := by
  intro c hc
  apply le_trans ?_ (h c hc)
  unfold demand
  simp only [Bool.not_false,Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false,
    Bool.true_and]
  split_ifs <;> omega

/-- The eleven-copy corner lemma uses only the nine-type Hall inequalities
and the total multiplicity, not an enumeration of collections. -/
theorem eleven_corners {I : Type*} [Fintype I] [DecidableEq I]
    (typeOf : I → Fin 9) (hI : Fintype.card I = 11) :
    ∃ t, ∃ f : Positions false t ↪ I, ∀ k, fits t (typeOf (f k)) k.val := by
  have hx : O (counts typeOf) + P (counts typeOf) + M (counts typeOf) = 11 := by
    rw [counts_total,hI]
  rcases choose_target (counts typeOf) hx with ⟨t,_,ht⟩ | ⟨t,ht⟩
  · exact ⟨t,match_of_bounds typeOf false t (corners_of_core_bounds _ _ ht)⟩
  · exact ⟨t,match_of_bounds typeOf false t (major_corners _ _ ht)⟩

theorem eleven_core {I : Type*} [Fintype I] [DecidableEq I]
    (typeOf : I → Fin 9) (hI : Fintype.card I = 11) (ho : ∃ i, (typeOf i).val < 3) :
    ∃ t, ∃ f : Positions true t ↪ I, ∀ k, fits t (typeOf (f k)) k.val := by
  have hx : O (counts typeOf) + P (counts typeOf) + M (counts typeOf) = 11 := by
    rw [counts_total,hI]
  have hO : 0 < O (counts typeOf) := by
    obtain ⟨i,hi⟩ := ho
    have hc : 0 < counts typeOf (typeOf i) := Finset.card_pos.mpr
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    generalize he : typeOf i = s at *
    fin_cases s <;> simp_all [O]
  rcases choose_target (counts typeOf) hx with ⟨t,_,ht⟩ | ⟨t,ht⟩
  · exact ⟨t,match_of_bounds typeOf true t ht⟩
  · exact ⟨t,match_of_bounds typeOf true t (major_core _ _ ht (Or.inl hO))⟩

lemma major_extra {I : Type*} [Fintype I] [DecidableEq I] (typeOf : I → Fin 9) (t : Fin 9)
    (h : Major (counts typeOf) t) (extra : Positions true t → Prop)
    (he : ∃ k, extra k) :
    ∃ f : Positions true t ↪ Option I, ∀ k, match f k with
      | none => extra k
      | some i => fits t (typeOf i) k.val := by
  classical
  obtain ⟨ht,hpool,hstrong⟩ := major_pool typeOf t h
  obtain ⟨k,hk⟩ := he
  apply FrameHall.two_pools_extra (fun i k => fits t (typeOf i) k.val)
    extra (special t) (pool typeOf t) (Finset.univ.filter fun i => typeOf i = t) k hk
  · exact (Finset.card_erase_le).trans (by simpa [special_card t ht,counts] using hstrong)
  · simpa only [positions_card t ht] using hpool
  · intro i hi p _
    rw [(Finset.mem_filter.mp hi).2]
    exact self_fits t p.val p.property
  · intro i hi p hp
    exact side_fits t _ ht (Finset.mem_filter.mp hi).2 p hp

def otherHalf (t : Fin 9) : Finset (Positions true (oppositeOf t)) :=
  Finset.univ.filter fun k => ¬ fits (oppositeOf t) t k.val
lemma half_card : ∀ t, 3 ≤ t.val → (otherHalf t).card = 4 := by decide +kernel
lemma opposite_positions_card (t : Fin 9) : Fintype.card (Positions true (oppositeOf t)) = 8 := by
  fin_cases t <;> decide +kernel
lemma half_fits : ∀ t, 3 ≤ t.val → ∀ s k,
    (sameSide t s → k ∉ otherHalf t → fits (oppositeOf t) s k.val) ∧
    (sameSide (if t.val < 6 then (6 : Fin 9) else 3) s → k ∈ otherHalf t → fits (oppositeOf t) s k.val) := by
  decide +kernel

lemma opposite_extra {I : Type*} [Fintype I] [DecidableEq I] (typeOf : I → Fin 9) (t : Fin 9)
    (h : Major (counts typeOf) t)
    (hother : 3 ≤ (pool typeOf (if t.val < 6 then (6 : Fin 9) else 3)).card)
    (extra : Positions true (oppositeOf t) → Prop)
    (he : ∃ k ∈ otherHalf t, extra k) :
    ∃ f : Positions true (oppositeOf t) ↪ Option I, ∀ k, match f k with
      | none => extra k
      | some i => fits (oppositeOf t) (typeOf i) k.val := by
  classical
  obtain ⟨ht,hpool,_⟩ := major_pool typeOf t h
  obtain ⟨k,hhalf,hk⟩ := he
  apply FrameHall.two_pools_extra (fun i k => fits (oppositeOf t) (typeOf i) k.val)
    extra (otherHalf t) (pool typeOf t)
    (pool typeOf (if t.val < 6 then (6 : Fin 9) else 3)) k hk
  · simpa [Finset.card_erase_of_mem hhalf,half_card t ht] using hother
  · rw [opposite_positions_card]; omega
  · intro i hi p hp
    exact (half_fits t ht _ p).2 (Finset.mem_filter.mp hi).2 hp
  · intro i hi p hp
    exact (half_fits t ht _ p).1 (Finset.mem_filter.mp hi).2 hp

/-- Any one extra physical variety resolves the last eleven-copy case. -/
theorem eleven_extra {I : Type*} [Fintype I] [DecidableEq I]
    (typeOf : I → Fin 9) (hI : Fintype.card I = 11) (p : Fin 10) (w : Fin 75) :
    ∃ t, ∃ f : Positions true t ↪ Option I, ∀ k, match f k with
      | none => extraFits p t w k.val
      | some i => fits t (typeOf i) k.val := by
  classical
  have hx : O (counts typeOf) + P (counts typeOf) + M (counts typeOf) = 11 := by
    rw [counts_total,hI]
  have hdone (t) (hb : Bounds true t (counts typeOf)) :
      ∃ t, ∃ f : Positions true t ↪ Option I, ∀ k, match f k with
        | none => extraFits p t w k.val
        | some i => fits t (typeOf i) k.val := by
    obtain ⟨f,hf⟩ := match_of_bounds typeOf true t hb
    exact ⟨t,f.trans ⟨Option.some,Option.some_injective _⟩,hf⟩
  rcases choose_target (counts typeOf) hx with ⟨t,_,ht⟩ | ⟨t,ht⟩
  · exact hdone t ht
  by_cases hh : 0 < O (counts typeOf) ∨
      (3 ≤ t.val ∧ t.val < 6 ∧ 9 ≤ P (counts typeOf)) ∨ (6 ≤ t.val ∧ 9 ≤ M (counts typeOf))
  · exact hdone t (major_core _ _ ht hh)
  have h3 : 3 ≤ t.val := (major_pool typeOf t ht).1
  by_cases he : ∃ k, active true t k ∧ extraFits p t w k
  · exact ⟨t,major_extra typeOf t ht _ (by obtain ⟨k,hk,hf⟩ := he; exact ⟨⟨k,hk⟩,hf⟩)⟩
  obtain ⟨k,hk,hnot,hfit⟩ := extra_alternative p t w h3 he
  have hother : 3 ≤ (pool typeOf (if t.val < 6 then (6 : Fin 9) else 3)).card := by
    rw [pool_card]
    fin_cases t <;> simp [Major,sameSide,Fin.sum_univ_succ,Finset.sum_filter,O,P,M] at * <;> omega
  exact ⟨oppositeOf t,opposite_extra typeOf t ht hother _
    ⟨⟨k,hk⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnot⟩,hfit⟩⟩
end FiveColour.Physical.Ring
