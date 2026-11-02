module
public import FiveColour.RootCapacityChecks
@[expose] public section
namespace FiveColour.Physical

/-- A Hall budget bounds each member of its neighbourhood separately. -/
lemma multiplicity_le_budget {n : Nat} (cubes : Fin n → Cube)
    (S : Finset (Fin 75)) (b : Nat)
    (h : Certificate.mass (multiplicityVector cubes) S ≤ (b : Int))
    (i : Fin 75) (hi : i ∈ S) : multiplicity cubes i ≤ b := by
  have hs : multiplicityVector cubes i ≤ Certificate.mass (multiplicityVector cubes) S :=
    Finset.single_le_sum (fun j _ => multiplicity_nonneg cubes j) hi
  change (multiplicity cubes i : Int) ≤ _ at hs
  omega

/-- Soundness of the combined class, budget and two-variety upper bound.
Anchor selection and the Hall-budget premise are separate coverage obligations. -/
theorem combined_capacity_bound {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (r : RootCapacity)
    (hm : multiplicity cubes (canonicalAnchor r.kind) = r.copies.val)
    (hclass : ∀ i, multiplicity cubes i ≤ classCap r.kind r.copies i)
    (hbudget : Certificate.mass (multiplicityVector cubes) (rootBad r) ≤ (r.budget : Int))
    (i : Fin 75) : multiplicity cubes i ≤ combinedCap r i := by
  unfold combinedCap
  split
  next he => simpa only [he] using hm.le
  next =>
    refine le_min (hclass i) (le_min ?_ ?_)
    · split
      next hi => exact multiplicity_le_budget cubes _ _ hbudget i hi
      next => exact multiplicity_le_seven cubes hc h i
    · exact pair_capacity_bound cubes hc h r.kind r.copies (by omega) i

/-- The actual exported upper vectors are sound under their stated root premises.
This theorem checks all 357 rows; it does not assert that those rows cover every
physical counterexample. -/
theorem exported_root_capacity_bound {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (r : Fin 357)
    (hm : multiplicity cubes (canonicalAnchor (rootCapacity r).kind) = (rootCapacity r).copies.val)
    (hclass : ∀ i, multiplicity cubes i ≤ classCap (rootCapacity r).kind (rootCapacity r).copies i)
    (hbudget : Certificate.mass (multiplicityVector cubes) (rootBad (rootCapacity r)) ≤
      ((rootCapacity r).budget : Int)) (i : Fin 75) :
    multiplicity cubes i ≤ rootUpper (rootCapacity r) i := by
  rw [root_caps_match]
  exact combined_capacity_bound cubes hc h (rootCapacity r) hm hclass hbudget i

/-- The ordinary integer box corresponding to an exported root. -/
def rootBox (r : RootCapacity) : Certificate.Box 75 where
  lower i := if i = canonicalAnchor r.kind then (r.copies.val : Int) else 0
  upper i := rootUpper r i

/-- Under the case premises, the physical multiplicity vector belongs to the
exported root box, including its fixed anchor coordinate. -/
theorem exported_root_contains {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (h : ¬ HasSolution cubes)
    (r : Fin 357)
    (hm : multiplicity cubes (canonicalAnchor (rootCapacity r).kind) = (rootCapacity r).copies.val)
    (hclass : ∀ i, multiplicity cubes i ≤ classCap (rootCapacity r).kind (rootCapacity r).copies i)
    (hbudget : Certificate.mass (multiplicityVector cubes) (rootBad (rootCapacity r)) ≤
      ((rootCapacity r).budget : Int)) :
    (rootBox (rootCapacity r)).Contains (multiplicityVector cubes) := by
  intro i
  constructor
  · change (if i = canonicalAnchor (rootCapacity r).kind then
      ((rootCapacity r).copies.val : Int) else 0) ≤ (multiplicity cubes i : Int)
    split
    next hi => simp only [hi, hm, le_refl]
    next => exact Int.natCast_nonneg _
  · change (multiplicity cubes i : Int) ≤ (rootUpper (rootCapacity r) i : Int)
    exact_mod_cast exported_root_capacity_bound cubes hc h r hm hclass hbudget i

end FiveColour.Physical
