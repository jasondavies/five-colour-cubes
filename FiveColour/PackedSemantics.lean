module
public import FiveColour.PackedArithmetic
public import FiveColour.FastCertificates
@[expose] public section
set_option maxHeartbeats 400000
namespace FiveColour.Packed
open scoped BigOperators

def values (v : Nat) : Fin 75 → Nat := fun i => digit v i.val

def ValidVector (v : Nat) : Prop := v = pack (values v) ∧ ∀ i, values v i ≤ 7

instance (v : Nat) : Decidable (ValidVector v) :=
  inferInstanceAs (Decidable (v = pack (values v) ∧ ∀ i, values v i ≤ 7))

lemma values_pack (x : Fin 75 → Nat) (hx : ∀ i, x i ≤ 7) : values (pack x) = x := by
  funext i
  exact pack_digit x hx i

lemma valid_pack (x : Fin 75 → Nat) (hx : ∀ i, x i ≤ 7) : ValidVector (pack x) := by
  simp only [ValidVector, values_pack x hx]
  exact ⟨trivial, hx⟩

lemma valid_encode (x : Fin 75 → Nat) (hx : ∀ i, x i ≤ 7) : ValidVector (encode x) := by
  rw [encode_eq_pack]
  exact valid_pack x hx

def Box.Valid (b : Box) : Prop := ValidVector b.lower ∧ ValidVector b.upper

instance (b : Box) : Decidable b.Valid :=
  inferInstanceAs (Decidable (ValidVector b.lower ∧ ValidVector b.upper))

def vectorModel (v : Nat) : Certificate.Vector 75 := fun i => (values v i : Int)

def Box.model (b : Box) : Certificate.Box 75 :=
  ⟨vectorModel b.lower, vectorModel b.upper⟩

def Cut.member (c : Cut) (i : Fin 75) : Bool := c.mask.testBit i.val

def Cut.Valid (c : Cut) : Prop := Calibrated c.weight c.member

def Cut.model (c : Cut) : Certificate.Cut 75 where
  neighbours := Finset.univ.filter (fun i => c.member i = true)
  rhs := c.rhs

lemma cut_valid_of_weight (c : Cut) (h : c.weight = maskWeight c.member) : c.Valid := by
  change Calibrated c.weight c.member
  rw [h]
  exact maskWeight_calibrated _

lemma list_valid_of_weights (cs : List Cut)
    (h : cs.all (fun c => decide (c.weight = maskWeight c.member)) = true) :
    ∀ c ∈ cs, c.Valid := by
  intro c hc
  exact cut_valid_of_weight c (of_decide_eq_true (List.all_eq_true.mp h c hc))

/-- Packed multiplication has exactly the subset-sum meaning required by Hall. -/
theorem mass_eq (v : Nat) (hv : ValidVector v) (c : Cut) (hc : c.Valid) :
    (mass v c : Int) = Certificate.mass (vectorModel v) c.model.neighbours := by
  have h := packed_subset_sum (values v) hv.2 c.weight c.member hc
  rw [← hv.1] at h
  unfold mass
  rw [h]
  change (∑ i : Fin 75, if c.member i then values v i else 0 : Nat) =
    ∑ i ∈ Finset.univ.filter (fun i => c.member i = true), (values v i : Int)
  rw [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all only [Nat.cast_zero]

lemma allWeight_calibrated : Calibrated allWeight (fun _ => true) := by
  have he : allWeight = maskWeight (fun _ => true) := by decide +kernel
  rw [he]
  exact maskWeight_calibrated _

theorem total_eq (v : Nat) (hv : ValidVector v) :
    (total v : Int) = Certificate.mass (vectorModel v) Finset.univ := by
  have h := packed_subset_sum (values v) hv.2 allWeight (fun _ => true) allWeight_calibrated
  rw [← hv.1] at h
  unfold total
  rw [h]
  simp only [↓reduceIte]
  exact Nat.cast_sum _ _

lemma mass_le_total (v : Nat) (hv : ValidVector v) (c : Cut) (hc : c.Valid) :
    mass v c ≤ total v := by
  have hm := packed_subset_sum (values v) hv.2 c.weight c.member hc
  have ht := packed_subset_sum (values v) hv.2 allWeight (fun _ => true) allWeight_calibrated
  rw [← hv.1] at hm ht
  unfold mass total
  rw [hm, ht]
  apply Finset.sum_le_sum
  intro i _
  split <;> simp_all

theorem outside_eq (v : Nat) (hv : ValidVector v) (c : Cut) (hc : c.Valid) :
    ((total v - mass v c : Nat) : Int) =
      Certificate.mass (vectorModel v) c.model.neighboursᶜ := by
  rw [Int.natCast_sub (mass_le_total v hv c hc), total_eq v hv, mass_eq v hv c hc]
  have h := Certificate.mass_complement (vectorModel v) c.model.neighbours
  omega

def possible (b : Box) (goal : Nat) (c : Cut) : Prop :=
  mass b.lower c ≤ c.rhs ∧ goal ≤ c.rhs + (total b.upper - mass b.upper c)

/-- The packed feasibility test is the reference Hall feasibility test. -/
theorem possible_iff (b : Box) (hb : b.Valid) (goal : Nat) (c : Cut) (hc : c.Valid) :
    possible b goal c ↔ c.model.Possible b.model (goal : Int) := by
  have hl := mass_eq b.lower hb.1 c hc
  have ho := outside_eq b.upper hb.2 c hc
  change (mass b.lower c ≤ c.rhs ∧ goal ≤ c.rhs + (total b.upper - mass b.upper c)) ↔
    (Certificate.mass (vectorModel b.lower) c.model.neighbours ≤ (c.rhs : Int) ∧
      (goal : Int) ≤ c.rhs + Certificate.mass (vectorModel b.upper) c.model.neighboursᶜ)
  constructor
  · intro h
    constructor
    · rw [← hl]
      exact_mod_cast h.1
    · rw [← ho]
      exact_mod_cast h.2
  · intro h
    constructor
    · rw [← hl] at h
      exact_mod_cast h.1
    · rw [← ho] at h
      exact_mod_cast h.2
/-- Replacing a digit is exactly updating one bounded coordinate. -/
theorem replaceDigit_eq_pack (v : Nat) (hv : ValidVector v) (i : Fin 75) (a : Nat) :
    replaceDigit v i.val a = pack (Function.update (values v) i a) := by
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j : Fin 75 => values v j * place j.val) (Finset.mem_univ i)
  change (∑ j ∈ Finset.univ.erase i, values v j * place j.val) +
    values v i * place i.val = pack (values v) at hsum
  rw [← hv.1] at hsum
  have hrest : (∑ j ∈ Finset.univ.erase i, Function.update (values v) i a j * place j.val) =
      ∑ j ∈ Finset.univ.erase i, values v j * place j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hnew := Finset.sum_erase_add Finset.univ
    (fun j : Fin 75 => Function.update (values v) i a j * place j.val) (Finset.mem_univ i)
  rw [hrest, Function.update_self] at hnew
  change _ = pack (Function.update (values v) i a) at hnew
  rw [← hnew]
  change v - values v i * place i.val + a * place i.val = _
  omega

lemma replaceDigit_valid (v : Nat) (hv : ValidVector v) (i : Fin 75) (a : Nat)
    (ha : a ≤ 7) : ValidVector (replaceDigit v i.val a) := by
  rw [replaceDigit_eq_pack v hv i a]
  apply valid_pack
  intro j
  by_cases h : j = i
  · subst j; simpa only [Function.update_self] using ha
  · simpa only [Function.update_of_ne h] using hv.2 j

lemma replaceDigit_values (v : Nat) (hv : ValidVector v) (i : Fin 75) (a : Nat)
    (ha : a ≤ 7) : values (replaceDigit v i.val a) = Function.update (values v) i a := by
  rw [replaceDigit_eq_pack v hv i a]
  apply values_pack
  intro j
  by_cases h : j = i
  · subst j; simpa only [Function.update_self] using ha
  · simpa only [Function.update_of_ne h] using hv.2 j

lemma replaceDigit_model (v : Nat) (hv : ValidVector v) (i : Fin 75) (a : Nat)
    (ha : a ≤ 7) : vectorModel (replaceDigit v i.val a) =
      Function.update (vectorModel v) i (a : Int) := by
  funext j
  change (values (replaceDigit v i.val a) j : Int) = _
  rw [replaceDigit_values v hv i a ha]
  by_cases h : j = i
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, vectorModel]
end FiveColour.Packed
