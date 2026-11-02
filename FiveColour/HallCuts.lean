module
public import FiveColour.Multiplicity
public import Mathlib.Data.Nat.Bitwise
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The eight low bits select a set of target corners. -/
def cornerSet (d : Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun k => d.testBit k.val

def cornerMask (K : Finset (Fin 8)) : Nat := ∑ k ∈ K, 2^k.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cornerMask_lt : ∀ K, cornerMask K < 256 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cornerSet_cornerMask : ∀ K, cornerSet (cornerMask K) = K := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cornerSet_card : ∀ d : Fin 256,
    ((List.range 8).filter (fun k => d.val.testBit k)).length = (cornerSet d.val).card := by
  decide +kernel

lemma cornerMask_pos {K : Finset (Fin 8)} (hK : K.Nonempty) : 0 < cornerMask K := by
  have he := cornerSet_cornerMask K
  by_contra h
  have hz : cornerMask K = 0 := by omega
  rw [hz] at he
  have : K = ∅ := by simpa [cornerSet] using he.symm
  exact hK.ne_empty this

/-- Bitwise overlap with an eight-bit mask means a common selected corner. -/
lemma mask_overlap_iff (a d : Nat) (hd : d < 256) :
    a.land d ≠ 0 ↔ ∃ k : Fin 8, d.testBit k.val = true ∧ a.testBit k.val = true := by
  constructor
  · intro h
    by_contra hn
    apply h
    apply Nat.zero_of_testBit_eq_false
    intro i
    by_cases hi : i < 8
    · have hk := not_exists.mp hn ⟨i, hi⟩
      cases ha : a.testBit i <;> cases hd' : d.testBit i <;>
        simp_all
    · have hpow : 256 ≤ 2^i := by
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 8 ≤ i)
      have hbit := Nat.testBit_eq_false_of_lt (hd.trans_le hpow)
      simp [hbit]
  · rintro ⟨k, hdk, hak⟩ he
    have hb := congrArg (fun v => Nat.testBit v k.val) he
    simp [hdk, hak] at hb

/-- The integer Hall deficiency associated with a physical corner set. -/
def physicalCut (t : Fin 75) (K : Finset (Fin 8)) : Certificate.Cut 75 where
  neighbours := varietyNeighbours t K
  rhs := (K.card : Int) - 1

/-- Exactly the mask-based cut used by the reference certificate checker. -/
def maskCut (t : Fin 75) (d : Nat) : Certificate.Cut 75 where
  neighbours := Finset.univ.filter fun i => (Replay.fits t i).land d ≠ 0
  rhs := (((List.range 8).filter fun k => d.testBit k).length : Int) - 1

/-- Stored incidence, bitwise overlap and physical neighbourhoods agree. -/
theorem maskCut_eq_physicalCut (t : Fin 75) (d : Fin 256) :
    maskCut t d.val = physicalCut t (cornerSet d.val) := by
  have hn : (Finset.univ.filter fun i => (Replay.fits t i).land d.val ≠ 0) =
      varietyNeighbours t (cornerSet d.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, varietyNeighbours,
      mask_overlap_iff _ _ d.isLt, cornerSet]
    simp only [incidence_fits]
  simp only [maskCut, physicalCut, hn, cornerSet_card]

/-- Every nonempty physical corner set occurs among the 255 exported masks. -/
theorem physicalCut_mem_hallCuts (t : Fin 75) (K : Finset (Fin 8)) (hK : K.Nonempty) :
    physicalCut t K ∈ Replay.hallCuts t := by
  have hpos := cornerMask_pos hK
  have hlt := cornerMask_lt K
  have he : cornerMask K - 1 + 1 = cornerMask K := by omega
  apply List.mem_map.mpr
  refine ⟨cornerMask K - 1, List.mem_range.mpr (by omega), ?_⟩
  change maskCut t (cornerMask K - 1 + 1) = physicalCut t K
  rw [he, maskCut_eq_physicalCut t ⟨cornerMask K, hlt⟩, cornerSet_cornerMask]

/-- Each exported cut has exactly the meaning of a physical Hall deficiency. -/
theorem hallCut_physical {t : Fin 75} {c : Certificate.Cut 75}
    (hc : c ∈ Replay.hallCuts t) :
    ∃ K : Finset (Fin 8), c = physicalCut t K := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hb : d + 1 < 256 := by have := List.mem_range.mp hd; omega
  exact ⟨cornerSet (d+1), maskCut_eq_physicalCut t ⟨d+1, hb⟩⟩

/-- Physical failure is equivalent to satisfying one listed deficiency per target. -/
theorem counterexample_iff_hallCuts {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) :
    ¬ HasSolution cubes ↔ ∀ t : Fin 75, ∃ c ∈ Replay.hallCuts t,
      c.Holds (multiplicityVector cubes) := by
  constructor
  · intro h t
    obtain ⟨K, hK, hcut⟩ := (counterexample_iff_deficient_mass cubes hc).mp h t
    exact ⟨physicalCut t K, physicalCut_mem_hallCuts t K hK, hcut⟩
  · intro h
    apply (not_hasSolution_iff_hall cubes).mpr
    intro t
    obtain ⟨c, hmem, hcut⟩ := h t
    obtain ⟨K, rfl⟩ := hallCut_physical hmem
    change Certificate.mass (multiplicityVector cubes) (varietyNeighbours t K) ≤
      (K.card : Int) - 1 at hcut
    rw [mass_varietyNeighbours cubes hc] at hcut
    exact ⟨K, by omega⟩

/-- The unanchored counterexample problem: total mass and one Hall cut per target. -/
def hallProblem (n : Nat) : Certificate.Problem 75 75 where
  goal := n
  alternatives := Replay.hallCuts

/-- Exact bridge from arbitrary physical collections to the reference checker's integer model. -/
theorem counterexample_iff_admissible {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) :
    ¬ HasSolution cubes ↔ (hallProblem n).Admissible (multiplicityVector cubes) := by
  rw [counterexample_iff_hallCuts cubes hc]
  simp only [Certificate.Problem.Admissible, hallProblem, multiplicity_total, true_and]

/-- A physical counterexample supplies a bounded admissible integer vector. -/
theorem counterexample_vector {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes) :
    (hallProblem n).Admissible (multiplicityVector cubes) ∧
      ∀ i, 0 ≤ multiplicityVector cubes i ∧ multiplicityVector cubes i ≤ 7 := by
  refine ⟨(counterexample_iff_admissible cubes hc).mp h, fun i => ⟨multiplicity_nonneg _ _, ?_⟩⟩
  change (multiplicity cubes i : Int) ≤ 7
  exact_mod_cast multiplicity_le_seven cubes hc h i

end FiveColour.Physical
