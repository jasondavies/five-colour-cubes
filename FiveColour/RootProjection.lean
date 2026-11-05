module
public import Mathlib.Tactic.Positivity
public import FiveColour.BudgetProjection
public import FiveColour.RootReduction
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- Only coordinates in the Hall budget set receive a smaller cap. -/
def projectedUpper (r : Fin 357) (s : Nat) (i : Fin 75) : Nat :=
  if i ∈ rootBad (rootCapacity r) then min (rootUpper (rootCapacity r) i) s
  else rootUpper (rootCapacity r) i

def projectedBox (r : Fin 357) (s : Nat) : Certificate.Box 75 where
  lower := (rootBox (rootCapacity r)).lower
  upper i := projectedUpper r s i

/-- The same 75 target-failure families, with a reduced total and anchor budget. -/
def projectedProblem (r : Fin 357) (s G : Nat) : Certificate.Problem 75 78 :=
  caseProblem r s G

/-- Conditions checked separately for each concrete projected header. -/
def ProjectionValid (r : Fin 357) (s G : Nat) : Prop :=
  canonicalAnchor (rootCapacity r).kind ∉ rootBad (rootCapacity r) ∧
  s ≤ (rootCapacity r).budget ∧
  (G : Int) = 15 - (rootCapacity r).budget + s ∧
  (rootCapacity r).copies.val ≤ G

instance (r : Fin 357) (s G : Nat) : Decidable (ProjectionValid r s G) := by
  unfold ProjectionValid
  infer_instance

/-- Project an already selected root. No new anchor selection or case coverage
is asserted for the smaller collection. All inherited bounds remain valid. -/
theorem root_projection (r : Fin 357) (s G : Nat) (hv : ProjectionValid r s G)
    {x : Certificate.Vector 75} (hx : (rootBox (rootCapacity r)).Contains x)
    (hp : (rootProblem r).Admissible x) :
    ∃ y, (projectedBox r s).Contains y ∧ (projectedProblem r s G).Admissible y := by
  obtain ⟨ha, hs, hG, hm⟩ := hv
  have hn (i : Fin 75) : 0 ≤ x i := by
    have hl : 0 ≤ (rootBox (rootCapacity r)).lower i := by
      simp only [rootBox]
      split <;> positivity
    exact hl.trans (hx i).1
  have hanchor : x (canonicalAnchor (rootCapacity r).kind) = (rootCapacity r).copies.val := by
    have h := hx (canonicalAnchor (rootCapacity r).kind)
    simp only [rootBox, rootUpper, ↓reduceIte] at h
    exact le_antisymm h.2 h.1
  obtain ⟨ht, hb, hh⟩ := (root_admissible_iff r x).mp hp
  obtain ⟨y, hy, hya, hyt, hys⟩ := Certificate.exists_budget_projection x hn
    (canonicalAnchor (rootCapacity r).kind) (rootBad (rootCapacity r)) ha
    15 (rootCapacity r).budget s ht hb (Int.natCast_nonneg _) (Int.ofNat_le.mpr hs)
    (by rw [← hG, hanchor]; exact Int.ofNat_le.mpr hm)
  have htotal : Certificate.mass y Finset.univ = G := hyt.trans hG.symm
  refine ⟨y, ?_, (caseProblem_admissible_iff r s G y).mpr
    ⟨htotal, hys, Certificate.hall_families_mono Replay.hallCuts (fun i => (hy i).2) hh⟩⟩
  · intro i
    constructor
    · change (if i = canonicalAnchor (rootCapacity r).kind then _ else 0) ≤ y i
      split
      · next hi => subst i; rw [hya, hanchor]
      · exact (hy i).1
    · change y i ≤ (projectedUpper r s i : Int)
      unfold projectedUpper
      split
      · next hi =>
        have hc : y i ≤ Certificate.mass y (rootBad (rootCapacity r)) := by
          exact Finset.single_le_sum (fun j _ => (hy j).1) hi
        rw [Nat.cast_min]
        exact le_min ((hy i).2.trans (hx i).2) (hc.trans hys)
      · exact (hy i).2.trans (hx i).2

end FiveColour.Physical
