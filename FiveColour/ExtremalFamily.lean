module
public import FiveColour.ExtremalExamples
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The three B and three C varieties are indexed in repeat-colour order 2,3,4 and 1,2,4. -/
def extremalBGroup : Fin 3 → Fin 75 := ![extremalB 0,extremalB 2,extremalB 4]
def extremalCGroup : Fin 3 → Fin 75 := ![extremalC 0,extremalC 3,extremalC 1]

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

lemma distributions_length : (sourceCompositions 3 5).length = 21 := by decide +kernel

def extremalDistribution (i : Fin 21) : Fin 3 → ℕ :=
  (sourceCompositions 3 5)[i.val]'(by rw [distributions_length]; exact i.isLt)

lemma distributions_complete (v : Fin 3 → ℕ) (h : ∑ i, v i = 5) :
    ∃ i : Fin 21, extremalDistribution i = v := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (mem_sourceCompositions v h)
  exact ⟨⟨i,by simpa only [distributions_length] using hi⟩,he⟩

def generalizedMaskNeighbours (x y : Fin 3 → ℕ) (t : Fin 75) (d : ℕ) : Finset (Fin 14) :=
  Finset.univ.filter fun i => (Replay.fits t (generalizedVariety x y i)).land d ≠ 0

lemma generalizedMaskNeighbours_eq (x y : Fin 3 → ℕ) (t : Fin 75) (d : ℕ) (hd : d < 256) :
    generalizedMaskNeighbours x y t d = neighbours (generalizedFamily x y) (catalogue t) (cornerSet d) := by
  ext i
  simp only [generalizedMaskNeighbours, neighbours, Finset.mem_filter, Finset.mem_univ, true_and,
    mask_overlap_iff _ _ hd, cornerSet, generalizedFamily, incidence_fits]

end FiveColour.Physical
