module
public import FiveColour.ProjectionData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical.Projection

def maskFits (m : Fin 64) (j : Fin 6) : Prop := m.val.testBit j.val = true
instance (m : Fin 64) : DecidablePred (maskFits m) := by intro j; unfold maskFits; infer_instance
def maskCount (m : Fin 64) := (Finset.univ.filter (maskFits m)).card
def first (p : Fin 6 → Bool) : Fin 6 := ((List.finRange 6).find? p).getD 0
def firstHalf (p : Fin 3 → Bool) : Fin 3 := ((List.finRange 3).find? p).getD 0

def pickThree (a b c : Fin 64) : Fin 3 × (Fin 3 → Fin 6) :=
  let r := firstHalf fun r => decide (3 ≤ (Finset.univ.filter fun j : Fin 6 => j.val/2 ≠ r.val ∧ maskFits a j).card)
  let x := first fun j => decide (j.val/2 ≠ r.val ∧ maskFits b j)
  let y := first fun j => decide (j.val/2 ≠ r.val ∧ maskFits c j ∧ j ≠ x)
  let z := first fun j => decide (j.val/2 ≠ r.val ∧ maskFits a j ∧ j ≠ x ∧ j ≠ y)
  (r,![z,x,y])
def pickTwo (a b : Fin 64) : Fin 3 × (Fin 2 → Fin 6) :=
  let x := first fun j => decide (maskFits a j)
  let y := first fun j => decide (maskFits b j ∧ j ≠ x)
  (firstHalf (fun r => decide (x.val/2 ≠ r.val ∧ y.val/2 ≠ r.val)),![x,y])
def pickOne (a : Fin 64) : Fin 3 × (Fin 1 → Fin 6) :=
  let x := first fun j => decide (maskFits a j)
  (firstHalf (fun r => decide (x.val/2 ≠ r.val)),fun _ => x)

lemma pickThree_valid (a : Fin 64) : 4 ≤ maskCount a → ∀ b, 4 ≤ maskCount b → ∀ c, 4 ≤ maskCount c →
    Function.Injective (pickThree a b c).2 ∧ ∀ i,
      ((pickThree a b c).2 i).val / 2 ≠ (pickThree a b c).1.val ∧
      maskFits (![a,b,c] i) ((pickThree a b c).2 i) := by
  fin_cases a <;> decide +kernel
lemma pickTwo_valid : ∀ a, 2 ≤ maskCount a → ∀ b, 2 ≤ maskCount b →
    Function.Injective (pickTwo a b).2 ∧ ∀ i,
      ((pickTwo a b).2 i).val / 2 ≠ (pickTwo a b).1.val ∧
      maskFits (![a,b] i) ((pickTwo a b).2 i) := by decide +kernel
lemma pickOne_valid : ∀ a, 1 ≤ maskCount a →
    Function.Injective (pickOne a).2 ∧ ∀ i,
      ((pickOne a).2 i).val / 2 ≠ (pickOne a).1.val ∧
      maskFits a ((pickOne a).2 i) := by decide +kernel

/-- At most three corner projections can be placed in a suitable four-position
half. These small six-bit checks are independent of cube collections. -/
lemma place_masks (j : Fin 3) (masks : Fin (3-j.val) → Fin 64)
    (hm : ∀ i, ![4,2,1] j ≤ maskCount (masks i)) :
    ∃ r : Fin 3, ∃ f : Fin (3-j.val) ↪ Half r, ∀ i, maskFits (masks i) (f i).val := by
  fin_cases j
  · change Fin 3 → Fin 64 at masks
    change (∀ i : Fin 3, 4 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 3 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    obtain ⟨hi,hf⟩ := pickThree_valid (masks 0) (hm 0) (masks 1) (hm 1) (masks 2) (hm 2)
    let f := (pickThree (masks 0) (masks 1) (masks 2)).2
    refine ⟨(pickThree (masks 0) (masks 1) (masks 2)).1,
      ⟨fun i => ⟨f i,(hf i).1⟩,fun a b he => hi (congrArg Subtype.val he)⟩,?_⟩
    intro i
    have h := (hf i).2
    fin_cases i <;> exact h
  · change Fin 2 → Fin 64 at masks
    change (∀ i : Fin 2, 2 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 2 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    obtain ⟨hi,hf⟩ := pickTwo_valid (masks 0) (hm 0) (masks 1) (hm 1)
    let f := (pickTwo (masks 0) (masks 1)).2
    refine ⟨(pickTwo (masks 0) (masks 1)).1,
      ⟨fun i => ⟨f i,(hf i).1⟩,fun a b he => hi (congrArg Subtype.val he)⟩,?_⟩
    intro i
    have h := (hf i).2
    fin_cases i <;> exact h
  · change Fin 1 → Fin 64 at masks
    change (∀ i : Fin 1, 1 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 1 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    obtain ⟨hi,hf⟩ := pickOne_valid (masks 0) (hm 0)
    refine ⟨(pickOne (masks 0)).1,
      ⟨fun i => ⟨(pickOne (masks 0)).2 i,(hf i).1⟩,fun a b he => hi (congrArg Subtype.val he)⟩,?_⟩
    intro i
    have h := (hf i).2
    fin_cases i; exact h
end FiveColour.Physical.Projection
