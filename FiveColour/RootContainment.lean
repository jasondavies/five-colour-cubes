module
public import FiveColour.CaseProblem
@[expose] public section

namespace FiveColour.Certificate

/-- For nonnegative coordinates, weakening both a cut's set and its bound
preserves every vector satisfying the original cut. -/
lemma Cut.holds_of_subset {n : Nat} {strong weak : Cut n} {x : Vector n}
    (hx : ∀ i, 0 ≤ x i) (hs : weak.neighbours ⊆ strong.neighbours)
    (hb : strong.rhs ≤ weak.rhs) (h : strong.Holds x) : weak.Holds x := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => hx i)).trans (h.trans hb)

/-- Coordinatewise wider bounds contain every vector in the narrower box. -/
lemma Box.contains_of_bounds {n : Nat} {small large : Box n} {x : Vector n}
    (h : ∀ i, large.lower i ≤ small.lower i ∧ small.upper i ≤ large.upper i)
    (hx : small.Contains x) : large.Contains x := by
  intro i
  exact ⟨(h i).1.trans (hx i).1, (hx i).2.trans (h i).2⟩

end FiveColour.Certificate

namespace FiveColour.Physical

/-- A sufficient, finite condition for the parent root to contain the child.
The total and all 75 target-failure families are common to every root. -/
def RootContains (parent child : Fin 357) : Prop :=
  (∀ i, (rootBox (rootCapacity parent)).lower i ≤ (rootBox (rootCapacity child)).lower i ∧
    rootUpper (rootCapacity child) i ≤ rootUpper (rootCapacity parent) i) ∧
  rootBad (rootCapacity parent) ⊆ rootBad (rootCapacity child) ∧
  (rootCapacity child).budget ≤ (rootCapacity parent).budget

instance (parent child : Fin 357) : Decidable (RootContains parent child) := by
  unfold RootContains
  infer_instance

lemma RootContains.refl (r : Fin 357) : RootContains r r :=
  ⟨fun _ => ⟨le_rfl, le_rfl⟩, Finset.Subset.refl _, le_rfl⟩

/-- Isolate the only constraint family that changes between roots. -/
lemma root_admissible_iff (r : Fin 357) (x : Certificate.Vector 75) :
    (rootProblem r).Admissible x ↔
      Certificate.mass x Finset.univ = 15 ∧
      Certificate.mass x (rootBad (rootCapacity r)) ≤ ((rootCapacity r).budget : Int) ∧
      ∀ t, ∃ c ∈ Replay.hallCuts t, c.Holds x := by
  exact caseProblem_admissible_iff r (rootCapacity r).budget 15 x

/-- Transport the entire integer problem, including the box and Hall families. -/
theorem RootContains.transport {parent child : Fin 357} (h : RootContains parent child)
    {x : Certificate.Vector 75} (hx : (rootBox (rootCapacity child)).Contains x)
    (hp : (rootProblem child).Admissible x) :
    (rootBox (rootCapacity parent)).Contains x ∧ (rootProblem parent).Admissible x := by
  have hn (i : Fin 75) : 0 ≤ x i := by
    have hl : 0 ≤ (rootBox (rootCapacity child)).lower i := by
      simp only [rootBox]
      split <;> positivity
    exact hl.trans (hx i).1
  obtain ⟨ht, hb, hh⟩ := (root_admissible_iff child x).mp hp
  constructor
  · apply Certificate.Box.contains_of_bounds ?_ hx
    intro i
    refine ⟨(h.1 i).1, ?_⟩
    change (rootUpper (rootCapacity child) i : Int) ≤ (rootUpper (rootCapacity parent) i : Int)
    exact Int.ofNat_le.mpr (h.1 i).2
  · apply (root_admissible_iff parent x).mpr
    refine ⟨ht, ?_, hh⟩
    exact Certificate.Cut.holds_of_subset
      (strong := ⟨rootBad (rootCapacity child), (rootCapacity child).budget⟩)
      (weak := ⟨rootBad (rootCapacity parent), (rootCapacity parent).budget⟩)
      hn h.2.1 (Int.ofNat_le.mpr h.2.2) hb

/-- A root exclusion is reusable for every contained root. -/
theorem RootContains.exclusion {parent child : Fin 357} (h : RootContains parent child)
    (hexclude : ∀ x, (rootBox (rootCapacity parent)).Contains x →
      ¬ (rootProblem parent).Admissible x) :
    ∀ x, (rootBox (rootCapacity child)).Contains x → ¬ (rootProblem child).Admissible x := by
  intro x hx hp
  obtain ⟨hx', hp'⟩ := h.transport hx hp
  exact hexclude x hx' hp'

/-- A failed initial Hall-budget capacity test excludes a root without replay. -/
theorem root_excluded_of_impossible_budget (r : Fin 357)
    (h : ¬ (⟨rootBad (rootCapacity r), (rootCapacity r).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity r)) 15) :
    ∀ x, (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x := by
  intro x hx hp
  obtain ⟨ht, hb, _⟩ := (root_admissible_iff r x).mp hp
  exact h (Certificate.possible_of_holds
    (c := ⟨rootBad (rootCapacity r), (rootCapacity r).budget⟩) hx hb ht)

end FiveColour.Physical
