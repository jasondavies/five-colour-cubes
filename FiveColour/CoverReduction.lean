module
public import FiveColour.CoverChecks
public import FiveColour.RootCapacities
@[expose] public section
namespace FiveColour.Physical

/-- Every eligible cover has a physical symmetry witness into an actual exported
root, preserving its anchor, multiplicity class and Hall budget. -/
theorem exported_cover (kind : Fin 2) (m : Fin 8) (d : Fin 256)
    (h : CoverEligible kind m d) :
    ∃ (s : PuzzleSymmetry) (r : Fin 357),
      varietyEquiv s (canonicalAnchor kind) = canonicalAnchor kind ∧
      (rootCapacity r).kind = kind ∧ (rootCapacity r).copies = m ∧
      (rootCapacity r).budget + (cornerSet d.val).card + m.val = 7 ∧
      rootBad (rootCapacity r) =
        (anchorBad (canonicalAnchor kind) (cornerSet d.val)).image (varietyEquiv s) := by
  obtain ⟨hfix, _, hmask⟩ := cover_orbit_valid kind d
  obtain ⟨hk, hm, _, hb, hbad⟩ := cover_root_valid kind m d h
  refine ⟨stabiliserSymmetry (coverTransform kind d), coverRoot kind m d,
    ?_, hk, hm, hb, ?_⟩
  · rw [stabiliser_variety]
    exact hfix
  · change decodeVarieties (rootCapacity (coverRoot kind m d)).badMask = _
    rw [hbad, ← hmask, transportMask_model, coverBadMask_model]
    have he : stabiliserAction (coverTransform kind d) =
        varietyEquiv (stabiliserSymmetry (coverTransform kind d)) :=
      funext fun i => (stabiliser_variety _ i).symm
    rw [he]

lemma classCap_varietyEquiv (s : PuzzleSymmetry) (kind : Fin 2) (m : Fin 8) (i : Fin 75) :
    classCap kind m (varietyEquiv s i) = classCap kind m i := by
  simp only [classCap, oppositeRepeat_varietyEquiv]

/-- Class bounds survive every global symmetry used by the cover witnesses. -/
theorem class_capacity_apply {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (kind : Fin 2) (m : Fin 8)
    (h : ∀ i, multiplicity cubes i ≤ classCap kind m i) :
    ∀ i, multiplicity (fun j => s.apply (cubes j)) i ≤ classCap kind m i := by
  intro i
  obtain ⟨j, rfl⟩ := (varietyEquiv s).surjective i
  rw [multiplicity_apply s cubes hc, classCap_varietyEquiv]
  exact h j

/-- The three mathematical premises attached to an exported root. -/
def RootPremises {n : Nat} (cubes : Fin n → Cube) (r : Fin 357) : Prop :=
  multiplicity cubes (canonicalAnchor (rootCapacity r).kind) = (rootCapacity r).copies.val ∧
    (∀ i, multiplicity cubes i ≤ classCap (rootCapacity r).kind (rootCapacity r).copies i) ∧
    Certificate.mass (multiplicityVector cubes) (rootBad (rootCapacity r)) ≤
      ((rootCapacity r).budget : Int)

/-- Finite cover coverage and the capacity theorem together place a transformed
physical counterexample inside an exported root box. Eligibility still includes
the explicit distinct/all-adjacent exception. -/
theorem reduce_eligible_cover {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes)
    (kind : Fin 2) (m : Fin 8) (d : Fin 256) (hd : CoverEligible kind m d)
    (hm : multiplicity cubes (canonicalAnchor kind) = m.val)
    (hclass : ∀ i, multiplicity cubes i ≤ classCap kind m i)
    (hbudget : Certificate.mass (multiplicityVector cubes)
      (anchorBad (canonicalAnchor kind) (cornerSet d.val)) ≤
        (7 : Int) - m.val - (cornerSet d.val).card) :
    ∃ (s : PuzzleSymmetry) (r : Fin 357),
      (∀ j, UsesAllColours (s.apply (cubes j))) ∧
      ¬ HasSolution (fun j => s.apply (cubes j)) ∧
      (rootCapacity r).kind = kind ∧ (rootCapacity r).copies = m ∧
      RootPremises (fun j => s.apply (cubes j)) r ∧
      (rootBox (rootCapacity r)).Contains (multiplicityVector (fun j => s.apply (cubes j))) := by
  obtain ⟨s, r, hs, hk, hrm, hb, hbad⟩ := exported_cover kind m d hd
  have hc' : ∀ j, UsesAllColours (s.apply (cubes j)) := fun j => (s.usesAllColours_apply _).mpr (hc j)
  have h' : ¬ HasSolution (fun j => s.apply (cubes j)) := fun hsol => h ((s.hasSolution_apply cubes).mp hsol)
  have hm' : multiplicity (fun j => s.apply (cubes j)) (canonicalAnchor (rootCapacity r).kind) =
      (rootCapacity r).copies.val := by
    rw [hk, hrm, ← hs, multiplicity_apply s cubes hc]
    exact hm
  have hclass' : ∀ i, multiplicity (fun j => s.apply (cubes j)) i ≤
      classCap (rootCapacity r).kind (rootCapacity r).copies i := by
    rw [hk, hrm]
    exact class_capacity_apply s cubes hc kind m hclass
  have hbudget' : Certificate.mass (multiplicityVector (fun j => s.apply (cubes j)))
      (rootBad (rootCapacity r)) ≤ ((rootCapacity r).budget : Int) := by
    rw [hbad, mass_apply s cubes hc]
    omega
  exact ⟨s, r, hc', h', hk, hrm, ⟨hm', hclass', hbudget'⟩,
    exported_root_contains _ hc' h' r hm' hclass' hbudget'⟩

/-- The same reduction for an arbitrary physical corner set, without assuming
that a chosen cover was already supplied as a bit mask. -/
theorem reduce_anchor_cover {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (h : ¬ HasSolution cubes)
    (kind : Fin 2) (m : Fin 8) (K : Finset (Fin 8))
    (hmpos : 0 < m.val) (hK : K.card + m.val ≤ 7)
    (hex : ¬ (kind = 0 ∧ m = 1 ∧ K = cornerSet omittedCover.val))
    (hm : multiplicity cubes (canonicalAnchor kind) = m.val)
    (hclass : ∀ i, multiplicity cubes i ≤ classCap kind m i)
    (hbudget : Certificate.mass (multiplicityVector cubes) (anchorBad (canonicalAnchor kind) K) ≤
      (7 : Int) - m.val - K.card) :
    ∃ (s : PuzzleSymmetry) (r : Fin 357),
      (∀ j, UsesAllColours (s.apply (cubes j))) ∧
      ¬ HasSolution (fun j => s.apply (cubes j)) ∧
      (rootCapacity r).kind = kind ∧ (rootCapacity r).copies = m ∧
      RootPremises (fun j => s.apply (cubes j)) r ∧
      (rootBox (rootCapacity r)).Contains (multiplicityVector (fun j => s.apply (cubes j))) := by
  let d : Fin 256 := ⟨cornerMask K, cornerMask_lt K⟩
  have he : cornerSet d.val = K := cornerSet_cornerMask K
  have hd : CoverEligible kind m d := by
    refine ⟨hmpos, by simpa only [he] using hK, ?_⟩
    rintro ⟨hk, hm1, hd⟩
    exact hex ⟨hk, hm1, by rw [← he, hd]⟩
  apply reduce_eligible_cover cubes hc h kind m d hd hm hclass
  simpa only [he] using hbudget

end FiveColour.Physical
