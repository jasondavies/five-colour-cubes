module
public import FiveColour.PackedCore
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
namespace FiveColour.Packed
open scoped BigOperators

lemma digit_decomposition (a k b : Nat) :
    a = k*b*(a/k/b) + k*(a/k%b) + a%k := by
  calc
    a = a%k + k*(a/k) := (Nat.mod_add_div _ _).symm
    _ = a%k + k*((a/k)%b + b*((a/k)/b)) := by
      exact congrArg (fun z => a%k + k*z) (Nat.mod_add_div (a/k) b).symm
    _ = _ := by ring

/-- Extract one coefficient of a packed product, provided lower digits and
that coefficient cannot carry. All operations are kernel-native arithmetic. -/
theorem product_digit {n : Nat} (x weights : Fin n → Nat) (m k b : Nat)
    (hk : 0 < k)
    (hr : (∑ i, x i * ((weights i*m)%k)) < k)
    (hc : (∑ i, x i * (((weights i*m)/k)%b)) < b) :
    (((∑ i, x i * weights i)*m)/k)%b =
      ∑ i, x i * (((weights i*m)/k)%b) := by
  have hsum : (∑ i, x i * weights i)*m =
      k*(b*(∑ i, x i * ((weights i*m)/k/b)) +
        (∑ i, x i * (((weights i*m)/k)%b))) +
        ∑ i, x i * ((weights i*m)%k) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      x i * weights i * m = x i * (weights i*m) := by ring
      _ = x i * (k*b*((weights i*m)/k/b) + k*((weights i*m)/k%b) + (weights i*m)%k) := by
        rw [← digit_decomposition]
      _ = _ := by ring
  rw [hsum, Nat.mul_add_div hk, Nat.div_eq_of_lt hr]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hc]

def remainderBound : Nat := (middle-1)/(base-1)

/-- A constant packing multiplier represents a particular subset. -/
def Calibrated (m : Nat) (member : Fin 75 → Bool) : Prop :=
  (∀ i, (place i.val*m/middle)%base = if member i then 1 else 0) ∧
  ∀ i : Fin 75, (place i.val*m)%middle ≤ remainderBound

instance (m : Nat) (member : Fin 75 → Bool) : Decidable (Calibrated m member) := by
  unfold Calibrated
  infer_instance

lemma no_carry_remainder : 75*7*remainderBound < middle := by decide +kernel
lemma no_carry_coefficient : 75*7 < base := by decide +kernel
lemma middle_pos : 0 < middle := by decide +kernel

def pack (x : Fin 75 → Nat) : Nat := ∑ i, x i * place i.val

/-- The subset sum is a single digit of a multiplication, with no trusted
native evaluation and no extra axioms. -/
theorem packed_subset_sum (x : Fin 75 → Nat) (hx : ∀ i, x i ≤ 7)
    (m : Nat) (member : Fin 75 → Bool) (hm : Calibrated m member) :
    (pack x*m/middle)%base = ∑ i, if member i then x i else 0 := by
  have hr : (∑ i, x i * ((place i.val*m)%middle)) < middle := by
    have hle : (∑ i, x i * ((place i.val*m)%middle)) ≤ 75*7*remainderBound := by
      calc
        _ ≤ ∑ _i : Fin 75, 7*remainderBound := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.mul_le_mul (hx i) (hm.2 i)
        _ = _ := by simp; ring
    exact hle.trans_lt no_carry_remainder
  have hc : (∑ i, x i * (((place i.val*m)/middle)%base)) < base := by
    have hle : (∑ i, x i * (((place i.val*m)/middle)%base)) ≤ 75*7 := by
      calc
        _ ≤ ∑ _i : Fin 75, 7 := by
          apply Finset.sum_le_sum
          intro i _
          rw [hm.1 i]
          split <;> simp_all
        _ = _ := by simp
    exact hle.trans_lt no_carry_coefficient
  rw [pack, product_digit x (fun i => place i.val) m middle base middle_pos hr hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm.1 i]
  split <;> simp_all
def reversePlace (i : Fin 75) : Nat := place (74-i.val)

lemma coefficient_table : ∀ i j : Fin 75,
    (reversePlace j * place i.val / middle) % base = if i = j then 1 else 0 := by
  decide +kernel

lemma remainder_table : ∀ i : Fin 75,
    (∑ j : Fin 75, reversePlace j * place i.val % middle) ≤ remainderBound := by
  decide +kernel

lemma remainderBound_lt : remainderBound < middle := by decide +kernel

def maskWeight (member : Fin 75 → Bool) : Nat :=
  ∑ j, (if member j then 1 else 0) * reversePlace j

/-- Every Boolean subset has a calibrated packing multiplier. Only the small
power table above is checked by finite computation; this theorem is uniform
in the subset and hence applies to every Hall neighbourhood. -/
theorem maskWeight_calibrated (member : Fin 75 → Bool) :
    Calibrated (maskWeight member) member := by
  let x : Fin 75 → Nat := fun j => if member j then 1 else 0
  have hx : ∀ j, x j ≤ 1 := by intro j; dsimp [x]; split <;> omega
  have hl (i : Fin 75) :
      (∑ j, x j * (reversePlace j * place i.val % middle)) ≤ remainderBound := by
    calc
      _ ≤ ∑ j, reversePlace j * place i.val % middle := by
        apply Finset.sum_le_sum
        intro j _
        simpa using Nat.mul_le_mul_right (reversePlace j * place i.val % middle) (hx j)
      _ ≤ _ := remainder_table i
  have hcoef (i : Fin 75) :
      (∑ j, x j * ((reversePlace j * place i.val / middle) % base)) = x i := by
    simp only [coefficient_table]
    simp [mul_ite]
  constructor
  · intro i
    have hr := (hl i).trans_lt remainderBound_lt
    have hc : (∑ j, x j * ((reversePlace j * place i.val / middle) % base)) < base := by
      rw [hcoef]
      exact (hx i).trans_lt (by decide)
    have h := product_digit x reversePlace (place i.val) middle base middle_pos hr hc
    rw [hcoef] at h
    simpa only [maskWeight, x, Nat.mul_comm] using h
  · intro i
    have he : place i.val * maskWeight member = ∑ j, x j * (reversePlace j * place i.val) := by
      simp only [maskWeight, Finset.mul_sum, x]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, Finset.sum_nat_mod]
    have hm : (∑ j, x j * (reversePlace j * place i.val) % middle) =
        ∑ j, x j * (reversePlace j * place i.val % middle) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [x]
      split <;> simp_all
    rw [hm]
    exact (Nat.mod_le _ _).trans (hl i)

lemma place_positive : ∀ i : Fin 75, 0 < place i.val := by decide +kernel
lemma reverse_place_positive : ∀ i : Fin 75, 0 < reversePlace i := by decide +kernel
lemma place_reverse : ∀ i : Fin 75, place i.val * reversePlace i = middle := by decide +kernel

lemma scaled_digit (m : Nat) (i : Fin 75) :
    (place i.val*m/middle)%base = digit m (74-i.val) := by
  rw [← place_reverse i, Nat.mul_div_mul_left m (reversePlace i) (place_positive i)]
  rfl

lemma one_hot_calibrated : ∀ i : Fin 75,
    Calibrated (reversePlace i) (fun j => decide (j=i)) := by decide +kernel

/-- Reading a packed coordinate returns precisely the original count. -/
theorem pack_digit (x : Fin 75 → Nat) (hx : ∀ i, x i ≤ 7) (i : Fin 75) :
    digit (pack x) i.val = x i := by
  have h := packed_subset_sum x hx (reversePlace i) (fun j => decide (j=i))
    (one_hot_calibrated i)
  rw [← place_reverse i, Nat.mul_div_mul_right (pack x) (place i.val)
    (reverse_place_positive i)] at h
  simpa [digit] using h

lemma encode_eq_pack (f : Fin 75 → Nat) : encode f = pack f := by
  have fold (xs : List (Fin 75)) (a : Nat) :
      xs.foldl (fun acc i => acc + f i * place i.val) a =
        a + (xs.map (fun i => f i * place i.val)).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons i xs ih => simp [List.foldl_cons, ih, Nat.add_assoc]
  rw [encode, fold, zero_add, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

lemma no_carry_255 : 255*remainderBound < middle := by decide +kernel

/-- Summed Boolean masks encode their membership counts without carries.
These digits replace bitwise unions and intersections in the fast checker. -/
theorem membership_count {n : Nat} (hn : n ≤ 255) (weights : Fin n → Nat)
    (members : Fin n → Fin 75 → Bool) (hc : ∀ j, Calibrated (weights j) (members j))
    (i : Fin 75) :
    digit (∑ j, weights j) (74-i.val) = ∑ j, if members j i then 1 else 0 := by
  have hr : (∑ j, 1 * (weights j * place i.val % middle)) < middle := by
    calc
      _ ≤ ∑ _j : Fin n, remainderBound := by
        apply Finset.sum_le_sum
        intro j _
        simpa [Nat.mul_comm] using (hc j).2 i
      _ = n * remainderBound := by simp
      _ ≤ 255 * remainderBound := Nat.mul_le_mul_right _ hn
      _ < middle := no_carry_255
  have he : (∑ j, 1 * ((weights j * place i.val / middle) % base)) =
      ∑ j, if members j i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simpa [Nat.mul_comm] using (hc j).1 i
  have hbound : (∑ j, if members j i then 1 else 0) ≤ n := by
    calc
      _ ≤ ∑ _j : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro j _
        split <;> omega
      _ = n := by simp
  have hb : (∑ j, 1 * ((weights j * place i.val / middle) % base)) < base := by
    rw [he]
    have : 255 < base := by decide
    omega
  have h := product_digit (fun _ => 1) weights (place i.val) middle base middle_pos hr hb
  rw [he] at h
  simp only [one_mul] at h
  rw [Nat.mul_comm, scaled_digit] at h
  exact h

end FiveColour.Packed
