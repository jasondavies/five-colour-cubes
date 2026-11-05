module
public import FiveColour.ExtremalVarieties
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

def distributionType (v : Fin 3 → ℕ) (i : ℕ) : Fin 3 :=
  if i < v 0 then 0 else if i < v 0 + v 1 then 1 else 2

def generalizedVariety (x y : Fin 3 → ℕ) (i : Fin 14) : Fin 75 :=
  if i.val < 4 then 0 else if i.val < 9 then
    extremalBGroup (distributionType x (i.val-4)) else
    extremalCGroup (distributionType y (i.val-9))

def generalizedFamily (x y : Fin 3 → ℕ) (i : Fin 14) : Cube :=
  catalogue (generalizedVariety x y i)

def disjointRepeats (x y : Fin 3 → ℕ) : Prop := x 0 * y 1 = 0 ∧ x 2 * y 2 = 0
instance (x y : Fin 3 → ℕ) : Decidable (disjointRepeats x y) := by
  unfold disjointRepeats; infer_instance

def familyBAllowed : Fin 4 → Finset (Fin 3) := ![{0,1,2},{0,1},{1,2},{1}]
def familyCAllowed : Fin 4 → Finset (Fin 3) := ![{0},{0,2},{0,1},{0,1,2}]

def familyAllowed (p : Fin 4) (i : Fin 14) (v : Fin 75) : Prop :=
  if i.val < 4 then v = 0 else if i.val < 9 then
    ∃ r ∈ familyBAllowed p, v = extremalBGroup r else
    ∃ r ∈ familyCAllowed p, v = extremalCGroup r

instance (p : Fin 4) (i : Fin 14) (v : Fin 75) : Decidable (familyAllowed p i v) := by
  unfold familyAllowed; infer_instance

def uniformNeighbours (p : Fin 4) (t : Fin 75) (d : ℕ) : Finset (Fin 14) :=
  Finset.univ.filter fun i => if i.val < 4 then (Replay.fits t 0).land d ≠ 0
    else if i.val < 9 then ∃ r ∈ familyBAllowed p, (Replay.fits t (extremalBGroup r)).land d ≠ 0
    else ∃ r ∈ familyCAllowed p, (Replay.fits t (extremalCGroup r)).land d ≠ 0

lemma distributionType_positive (x : Fin 3 → ℕ) (hx : ∑ r, x r = 5)
    (i : ℕ) (hi : i < 5) : 0 < x (distributionType x i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hx
  change x 0 + (x 1 + (x 2 + 0)) = 5 at hx
  unfold distributionType
  split_ifs <;> omega

def completionB : Fin 2 → Fin 3 := ![0,2]
def completionC : Fin 2 → Fin 3 := ![1,2]

def completionTag (b c : Fin 5) (i : Fin 14) : Option (Fin 8) :=
  if i.val < 4 then some 0 else if i.val < 9 then
    if i.val-4 = b.val then some 1 else some 2
  else if i.val-9 = c.val then some 3 else none

def completionCapacity : Fin 8 → ℕ := ![4,1,4,1,0,0,0,0]

def completionAllowed (r : Fin 2) (g : Fin 8) (s : Fin 75) : Prop :=
  (g = 0 ∧ s = 0) ∨ (g = 1 ∧ s = extremalBGroup (completionB r)) ∨
  (g = 2 ∧ ∃ j, s = extremalBGroup j) ∨ (g = 3 ∧ s = extremalCGroup (completionC r))
instance (r : Fin 2) (g : Fin 8) (s : Fin 75) : Decidable (completionAllowed r g s) := by
  unfold completionAllowed; infer_instance

lemma completion_pools_card : ∀ (b c : Fin 5) (g : Fin 8),
    (sourcePools (completionTag b c) g).card = completionCapacity g := by
  decide +kernel

lemma distributionType_witness (x : Fin 3 → ℕ) (hx : ∑ i, x i = 5)
    (r : Fin 3) (hr : 0 < x r) : ∃ i : Fin 5, distributionType x i.val = r := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hx
  change x 0 + (x 1 + (x 2 + 0)) = 5 at hx
  fin_cases r
  · change 0 < x 0 at hr
    exact ⟨⟨0,by omega⟩, by simp [distributionType, hr]⟩
  · change 0 < x 1 at hr
    exact ⟨⟨x 0,by omega⟩, by simp [distributionType]; omega⟩
  · change 0 < x 2 at hr
    exact ⟨⟨x 0+x 1,by omega⟩, by simp [distributionType]⟩

end FiveColour.Physical
