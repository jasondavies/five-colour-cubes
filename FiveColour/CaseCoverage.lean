module
public import FiveColour.AnchorSelection
@[expose] public section
namespace FiveColour.Physical

/-- Complete physical coverage by the exported roots, for every counterexample
with at least eleven copies. Anchor selection and cover eligibility are proved,
not assumed. The transformed family still consists of the same indexed copies. -/
theorem physical_root_cover {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (hn : 10 < n) (h : ¬ HasSolution cubes) :
    ∃ (a : Fin 75) (s : PuzzleSymmetry) (r : Fin 357),
      (∀ q, UsesAllColours (s.apply ((anchorSymmetry a).apply (cubes q)))) ∧
      ¬ HasSolution (fun q => s.apply ((anchorSymmetry a).apply (cubes q))) ∧
      RootPremises (fun q => s.apply ((anchorSymmetry a).apply (cubes q))) r ∧
      (rootBox (rootCapacity r)).Contains
        (multiplicityVector (fun q => s.apply ((anchorSymmetry a).apply (cubes q)))) := by
  obtain ⟨a, kind, m, ha, hmpos, hm, hclass, hextra⟩ :=
    select_anchor cubes hc hn (multiplicity_le_seven cubes hc h)
  obtain ⟨hc', h', hm'⟩ := normalised_counterexample cubes hc h a
  rw [ha, hm] at hm'
  have hclass' := class_capacity_apply (anchorSymmetry a) cubes hc kind m hclass
  obtain ⟨K, hK, hbudget⟩ := anchor_cover (fun q => (anchorSymmetry a).apply (cubes q))
    hc' h' (canonicalAnchor kind)
  rw [hm'] at hK hbudget
  have hex : ¬ (kind = 0 ∧ m = 1 ∧ K = cornerSet omittedCover.val) := by
    rintro ⟨hk0, hm1, hKe⟩
    have hpos := hextra hk0 hm1
    have hz : Certificate.mass (multiplicityVector (fun q => (anchorSymmetry a).apply (cubes q)))
        (anchorBad 3 (cornerSet omittedCover.val)) ≤ 0 := by
      simpa [hk0, hm1, hKe, canonicalAnchor, omittedCover_card] using hbudget
    exact (not_lt_of_ge hz) hpos
  obtain ⟨s, r, hc'', h'', _, _, hp, hb⟩ := reduce_anchor_cover
    (fun q => (anchorSymmetry a).apply (cubes q)) hc' h' kind m K hmpos hK hex hm' hclass' hbudget
  exact ⟨a, s, r, hc'', h'', hp, hb⟩

end FiveColour.Physical
