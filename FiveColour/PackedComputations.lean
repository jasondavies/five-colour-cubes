module
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Arithmetic implementations used only to discharge the existing validity
and calibration propositions. The lemmas below prove their semantic meaning. -/
namespace FiveColour.Packed
lemma place_eq_pow (i : Fin 75) : place i.val = 1024 ^ i.val := by
  revert i
  decide +kernel
end FiveColour.Packed

namespace FiveColour.Packed.FastValidity
open scoped BigOperators

def digitMask : Nat := 7 * allWeight

theorem digitMask_lt : digitMask < 1024 ^ 75 := by
  decide +kernel

theorem digitMask_digit : ∀ i : Fin 75,
    digitMask / (1024 ^ i.val) % 1024 = 7 := by
  decide +kernel

theorem digits_reconstruct (v n : Nat) :
    (∑ i ∈ Finset.range n, (v / (1024 ^ i) % 1024) * 1024 ^ i) =
      v % (1024 ^ n) := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]
    rw [Nat.mul_comm]

theorem pack_values (v : Nat) : pack (values v) = v % (1024 ^ 75) := by
  simp only [pack, values, digit, base, place_eq_pow]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : Nat => (v / (1024 ^ i) % 1024) * 1024 ^ i) 75).trans
      (digits_reconstruct v 75)

/-- One native bit-containment test certifies all 75 bounded digits and reconstruction. -/
theorem valid_of_mask (v : Nat) (hv : v &&& digitMask = v) : ValidVector v := by
  have hle : v ≤ digitMask := by
    calc
      v = v &&& digitMask := hv.symm
      _ ≤ digitMask := Nat.and_le_right
  constructor
  · rw [pack_values, Nat.mod_eq_of_lt (hle.trans_lt digitMask_lt)]
  · intro i
    change v / place i.val % base ≤ 7
    rw [place_eq_pow, base]
    have h := congrArg (fun w : Nat => w / (2 ^ (10 * i.val)) % (2 ^ 10)) hv
    rw [Nat.and_div_two_pow, Nat.and_mod_two_pow] at h
    simp only [Nat.pow_mul] at h
    change (v / (1024 ^ i.val) % 1024) &&&
      (digitMask / (1024 ^ i.val) % 1024) =
      v / (1024 ^ i.val) % 1024 at h
    rw [digitMask_digit i] at h
    calc
      v / (1024 ^ i.val) % 1024 = (v / (1024 ^ i.val) % 1024) &&& 7 := h.symm
      _ ≤ 7 := Nat.and_le_right

theorem box_valid_of_masks (b : Box)
    (hl : b.lower &&& digitMask = b.lower)
    (hu : b.upper &&& digitMask = b.upper) : b.Valid :=
  ⟨valid_of_mask b.lower hl, valid_of_mask b.upper hu⟩

end FiveColour.Packed.FastValidity

namespace FiveColour.Packed.FastWeight
open scoped BigOperators

/-- Consume low mask bits while shifting the accumulated base-1024 digits. -/
def loop : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n+1, mask, acc => loop n (mask / 2) (1024 * acc + mask % 2)

def fastMaskWeight (mask : Nat) : Nat := loop 75 mask 0

def weightSum (n mask : Nat) : Nat :=
  ∑ i : Fin n, (mask.testBit i.val).toNat * 1024 ^ (n-1-i.val)

theorem weightSum_succ (n mask : Nat) :
    weightSum (n+1) mask = (mask % 2) * 1024^n + weightSum n (mask / 2) := by
  have head : (mask.testBit 0).toNat = mask % 2 := by
    simpa only [pow_zero, Nat.div_one] using Nat.toNat_testBit mask 0
  unfold weightSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel_right, Nat.sub_zero, head]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_div_two]
  congr 1
  congr 1
  omega

theorem loop_eq (n mask acc : Nat) :
    loop n mask acc = acc * 1024^n + weightSum n mask := by
  induction n generalizing mask acc with
  | zero => simp [loop, weightSum]
  | succ n ih =>
    rw [loop, ih, weightSum_succ, Nat.pow_succ]
    ring

/-- The executable converter equals the existing semantic packing multiplier. -/
theorem fastMaskWeight_eq (mask : Nat) :
    fastMaskWeight mask = maskWeight (fun i => mask.testBit i.val) := by
  rw [fastMaskWeight, loop_eq]
  simp only [Nat.zero_mul, Nat.zero_add, weightSum, maskWeight, reversePlace]
  apply Finset.sum_congr rfl
  intro i _
  have hp := place_eq_pow (⟨74-i.val, by omega⟩ : Fin 75)
  change place (74-i.val) = 1024^(74-i.val) at hp
  rw [hp]
  have hb (b : Bool) : b.toNat = (if b then 1 else 0) := by
    cases b <;> rfl
  rw [hb]

theorem cut_valid_of_fast_weight (c : Cut) (h : c.weight = fastMaskWeight c.mask) : c.Valid := by
  apply cut_valid_of_weight
  change c.weight = maskWeight (fun i => c.mask.testBit i.val)
  rw [← fastMaskWeight_eq]
  exact h

theorem list_weights_of_fast (cs : List Cut)
    (h : cs.all (fun c => decide (c.weight = fastMaskWeight c.mask)) = true) :
    cs.all (fun c => decide (c.weight = maskWeight c.member)) = true := by
  change cs.all (fun c => decide (c.weight = maskWeight (fun i => c.mask.testBit i.val))) = true
  simpa only [fastMaskWeight_eq] using h

end FiveColour.Packed.FastWeight
