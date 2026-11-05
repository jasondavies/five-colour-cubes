module
public import Mathlib.Algebra.BigOperators.Fin
public import FiveColour.Reserve
public import FiveColour.PairCapacityDefs
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- All weak compositions, used only to certify small local source inventories. -/
def sourceCompositions : (g : ℕ) → ℕ → List (Fin g → ℕ)
  | 0, n => if n = 0 then [Fin.elim0] else []
  | g+1, n => (List.range (n+1)).flatMap fun a =>
      (sourceCompositions g (n-a)).map (Fin.cons a)

theorem mem_sourceCompositions {g n : ℕ} (v : Fin g → ℕ)
    (h : ∑ i, v i = n) : v ∈ sourceCompositions g n := by
  induction g generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h.symm
    subst n
    have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [sourceCompositions, hv]
  | succ g ih =>
    have hs := h
    rw [Fin.sum_univ_succ] at hs
    apply List.mem_flatMap.mpr
    refine ⟨v 0, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨fun i => v i.succ, ih _ (by omega), Fin.cons_self_tail v⟩

/-- Select exactly n units from capacities whose total is at least n. -/
theorem exists_subcounts {g : ℕ} (v : Fin g → ℕ) (n : ℕ)
    (h : n ≤ ∑ i, v i) : ∃ w : Fin g → ℕ, (∑ i, w i) = n ∧ ∀ i, w i ≤ v i := by
  induction g generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    exact ⟨v, by simp [hn], fun _ => le_rfl⟩
  | succ g ih =>
    rw [Fin.sum_univ_succ] at h
    obtain ⟨w, hw, hle⟩ := ih (fun i => v i.succ) (n - min n (v 0)) (by omega)
    refine ⟨Fin.cons (min n (v 0)) w, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hw]
      omega
    · intro i
      refine Fin.cases (Nat.min_le_right _ _) (fun j => ?_) i
      exact hle j

/-- A checked assignment uses no more than the available number of each group. -/
structure CornerAllocation where
  target : Fin 75
  group : Fin 8 → Fin 8
  deriving Inhabited

def CornerAllocation.Valid (masks : Fin 75 → Fin 8 → ℕ)
    (capacity : Fin 8 → ℕ) (w : CornerAllocation) : Prop :=
  (∀ k, (masks w.target (w.group k)).testBit k.val = true) ∧
  ∀ g, (Finset.univ.filter fun k => w.group k = g).card ≤ capacity g

instance (masks : Fin 75 → Fin 8 → ℕ) (capacity : Fin 8 → ℕ)
    (w : CornerAllocation) : Decidable (w.Valid masks capacity) := by
  unfold CornerAllocation.Valid
  infer_instance

/-- Explicit corner assignments lift to distinct physical copies in disjoint pools. -/
theorem cornerAllocation_solves {n : ℕ} (cubes : Fin n → Cube)
    (pools : Fin 8 → Finset (Fin n)) (masks : Fin 75 → Fin 8 → ℕ)
    (capacity : Fin 8 → ℕ) (w : CornerAllocation)
    (hd : Pairwise fun a b => Disjoint (pools a) (pools b))
    (hc : ∀ g, capacity g ≤ (pools g).card)
    (hf : ∀ t g i, i ∈ pools g → ∀ k, (masks t g).testBit k.val = true →
      Fits (cubes i) (catalogue t) k)
    (hw : w.Valid masks capacity) : HasSolution cubes := by
  obtain ⟨f, hmem⟩ := Reserve.allocate w.group pools hd (fun g => by
    simpa only [Fintype.card_subtype] using (hw.2 g).trans (hc g))
  exact (hasSolution_iff_catalogue cubes).mpr
    ⟨w.target, f, fun k => hf w.target (w.group k) (f k) (hmem k) k (hw.1 k)⟩

/-- Physical source pools selected by an optional group label. -/
def sourcePools {n : ℕ} (tag : Fin n → Option (Fin 8)) (g : Fin 8) : Finset (Fin n) :=
  Finset.univ.filter fun i => tag i = some g

lemma sourcePools_disjoint {n : ℕ} (tag : Fin n → Option (Fin 8)) :
    Pairwise fun a b => Disjoint (sourcePools tag a) (sourcePools tag b) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hab (Option.some.inj ((Finset.mem_filter.mp hi).2.symm.trans
    (Finset.mem_filter.mp hj).2))

lemma sourcePools_total {n : ℕ} (tag : Fin n → Option (Fin 8)) :
    (∑ g, (sourcePools tag g).card) +
      (Finset.univ.filter fun i => tag i = none).card = n := by
  have hd : ((Finset.univ : Finset (Fin 8)) : Set (Fin 8)).PairwiseDisjoint (sourcePools tag) :=
    fun _ _ _ _ h => sourcePools_disjoint tag h
  have hu : Finset.univ.biUnion (sourcePools tag) =
      Finset.univ.filter (fun i => tag i ≠ none) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, sourcePools, Finset.mem_filter]
    cases tag i <;> simp
  have hh := Finset.card_biUnion hd
  rw [hu] at hh
  have hp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => tag i = none)
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  rw [← hh, Nat.add_comm]
  exact hp

end FiveColour.Physical
