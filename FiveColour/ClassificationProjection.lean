module
public import FiveColour.RootProjection
public import FiveColour.EnumerationRoot
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical
/-- Conditions checked separately for each concrete projected header. -/
def ProjectionValidAt (N : Nat) (r : Fin 357) (s G : Nat) : Prop :=
  canonicalAnchor (rootCapacity r).kind ∉ rootBad (rootCapacity r) ∧
  s ≤ (rootCapacity r).budget ∧
  (G : Int) = (N : Int) - (rootCapacity r).budget + s ∧
  (rootCapacity r).copies.val ≤ G

instance (N : Nat) (r : Fin 357) (s G : Nat) : Decidable (ProjectionValidAt N r s G) := by
  unfold ProjectionValidAt
  infer_instance

/-- Project an already selected root. No new anchor selection or case coverage
is asserted for the smaller collection. All inherited bounds remain valid. -/
theorem root_projection_at (N : Nat) (r : Fin 357) (s G : Nat) (hv : ProjectionValidAt N r s G)
    {x : Certificate.Vector 75} (hx : (rootBox (rootCapacity r)).Contains x)
    (hp : (caseProblem r (rootCapacity r).budget N).Admissible x) :
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
  obtain ⟨ht, hb, hh⟩ := (caseProblem_admissible_iff r _ N x).mp hp
  obtain ⟨y, hy, hya, hyt, hys⟩ := Certificate.exists_budget_projection x hn
    (canonicalAnchor (rootCapacity r).kind) (rootBad (rootCapacity r)) ha
    N (rootCapacity r).budget s ht hb (Int.natCast_nonneg _) (Int.ofNat_le.mpr hs)
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
