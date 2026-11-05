module
public import FiveColour.SubmissionModel
public import FiveColour.ComparatorBridge
public import FiveColour.BoxThresholds
public import FiveColour.ExtremalClassification
public import FiveColour.ExtremalFamilyTheorems
@[expose] public section
namespace FiveColour.Submission
open scoped BigOperators

/-- The independently stated slot model is the physical model used by the proof. -/
lemma frame_model_iff {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) :
    FrameSolvable a b c cubes ↔ Physical.BoxFrameSolvable a b c cubes := Iff.rfl
lemma box_model_iff {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) :
    BoxSolvable a b c cubes ↔ Physical.BoxSolvable a b c cubes := Iff.rfl

/-- Catalogue equality is equivalent to geometric proper-rotation equivalence. -/
lemma sameVariety_iff (c d : Cube) (hc : UsesAllColours c) (hd : UsesAllColours d) :
    SameVariety c d ↔ Physical.catalogueIndex c = Physical.catalogueIndex d := by
  constructor
  · rintro ⟨r,hr,h⟩
    obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
    have he : Physical.rotate c r = d := funext h
    rw [← he,Physical.catalogueIndex_rotate c hc r]
  · intro h
    obtain ⟨r,hr⟩ := Physical.catalogueIndex_spec c hc
    obtain ⟨s,hs⟩ := Physical.catalogueIndex_spec d hd
    obtain ⟨v,hv⟩ := ColourCubes.rotation_inverse r
    obtain ⟨u,hu⟩ := ColourCubes.rotation_composition v s
    refine ⟨ColourCubes.rotations u,(ColourCubes.proper_rotation_iff _).mpr ⟨u,rfl⟩,?_⟩
    intro f
    rw [hr,hs]
    change Physical.catalogue (Physical.catalogueIndex c)
      (ColourCubes.rotations r (ColourCubes.rotations u f)) =
      Physical.catalogue (Physical.catalogueIndex d) (ColourCubes.rotations s f)
    rw [hu,hv,h]

lemma copiesOf_eq {n : ℕ} (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (c : Cube) (hcol : UsesAllColours c) :
    copiesOf cubes c = Finset.univ.filter
      (fun i => Physical.catalogueIndex (cubes i) = Physical.catalogueIndex c) := by
  ext i
  simp only [copiesOf,Finset.mem_filter,Finset.mem_univ,true_and]
  exact sameVariety_iff _ _ (hc i) hcol

lemma copyCount_eq {n : ℕ} (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (c : Cube) (hcol : UsesAllColours c) :
    copyCount cubes c = Physical.multiplicity cubes (Physical.catalogueIndex c) := by
  rw [copyCount,copiesOf_eq cubes hc c hcol]
  rfl

lemma varietyCount_eq {n : ℕ} (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    varietyCount cubes = (Physical.varietySupport cubes).card := by
  classical
  let fiber := fun a : Fin 75 => Finset.univ.filter
    (fun i : Fin n => Physical.catalogueIndex (cubes i) = a)
  have he : (Finset.univ.image fun i => copiesOf cubes (cubes i)) =
      (Physical.varietySupport cubes).image fiber := by
    simp only [Physical.varietySupport,Finset.image_image]
    congr 1
    funext i
    exact copiesOf_eq cubes hc (cubes i) (hc i)
  unfold varietyCount
  rw [he]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  have hmem : i ∈ fiber a := by simp [fiber,hi]
  rw [hab] at hmem
  exact hi.symm.trans (Finset.mem_filter.mp hmem).2

lemma transform_eq_apply (p : Equiv.Perm (Fin 5)) (b : Bool) (c : Cube) :
    transform p b c = (Physical.PuzzleSymmetry.mk p b).apply c := by
  cases b <;> rfl

lemma equivalent_iff {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
    (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i)) :
    Equivalent a b ↔ Physical.SymmetryEquivalent a b := by
  constructor
  · rintro ⟨p,mirror,h⟩
    let s : Physical.PuzzleSymmetry := ⟨p,mirror⟩
    refine ⟨s,?_⟩
    intro i
    have hh := h (Physical.catalogue i) (Physical.catalogue_uses_all_colours i)
    have ha' : ∀ j, UsesAllColours (transform p mirror (a j)) := fun j => by
      rw [transform_eq_apply]
      exact (s.usesAllColours_apply _).mpr (ha j)
    rw [copyCount_eq _ ha' _ (Physical.catalogue_uses_all_colours i),
      copyCount_eq _ hb _ (Physical.catalogue_uses_all_colours i),
      Physical.catalogue_index_faces] at hh
    simpa only [transform_eq_apply] using hh
  · rintro ⟨s,hs⟩
    refine ⟨s.colour,s.mirror,?_⟩
    intro c hc
    have ha' : ∀ j, UsesAllColours (transform s.colour s.mirror (a j)) := fun j => by
      rw [transform_eq_apply]
      exact (s.usesAllColours_apply _).mpr (ha j)
    rw [copyCount_eq _ ha' _ hc,copyCount_eq _ hb _ hc]
    simpa only [transform_eq_apply] using hs (Physical.catalogueIndex c)

lemma anchor_eq : anchor = Physical.catalogue 0 := by decide +kernel
lemma leftVariety_eq : ∀ i, leftVariety i = Physical.catalogue (Physical.extremalBGroup i) := by
  decide +kernel
lemma rightVariety_eq : ∀ i, rightVariety i = Physical.catalogue (Physical.extremalCGroup i) := by
  decide +kernel
lemma extremalFamily_eq : ∀ j, extremalFamily j = Physical.extremalFamily j := by
  decide +kernel
lemma generalizedFamily_eq (x y : Fin 3 → ℕ) :
    generalizedFamily x y = Physical.generalizedFamily x y := by
  funext i
  unfold generalizedFamily Physical.generalizedFamily Physical.generalizedVariety
  split_ifs <;> simp only [anchor_eq,leftVariety_eq,rightVariety_eq]
  all_goals rfl

lemma supportGuarantee_iff (k v : ℕ) :
    SupportGuarantee k v ↔ Physical.SupportGuarantee k v := by
  constructor
  · intro h n cubes hc hs hn
    exact (Puzzle.hasSolution_iff cubes).mp (h n cubes hc
      (by simpa only [varietyCount_eq cubes hc] using hs) hn)
  · intro h n cubes hc hs hn
    exact (Puzzle.hasSolution_iff cubes).mpr (h n cubes hc
      (by simpa only [varietyCount_eq cubes hc] using hs) hn)

/-- Every fourteen-source obstruction has maximum variety multiplicity five. -/
theorem multiplicity_bound (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes)
    (c : Cube) (hcol : UsesAllColours c) : copyCount cubes c ≤ 5 := by
  rw [copyCount_eq cubes hc c hcol]
  exact Physical.fourteen_multiplicity_le_five cubes hc
    (fun h => hno ((Puzzle.hasSolution_iff cubes).mpr h)) _

/-- Complete classification of the obstructions using three varieties. -/
theorem three_variety_classification (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : varietyCount cubes = 3) :
    ¬ HasSolution cubes ↔ ∃ j : Fin 5, Equivalent cubes (extremalFamily j) := by
  rw [varietyCount_eq cubes hc] at hs
  simp only [extremalFamily_eq,
    equivalent_iff cubes _ hc (Physical.extremal_uses_all _),Puzzle.hasSolution_iff]
  exact Physical.three_variety_obstruction_iff cubes hc hs

/-- All five representatives use exactly three varieties and fail to assemble. -/
theorem extremal_examples (j : Fin 5) :
    (∀ i, UsesAllColours (extremalFamily j i)) ∧
    varietyCount (extremalFamily j) = 3 ∧ ¬ HasSolution (extremalFamily j) := by
  rw [extremalFamily_eq]
  refine ⟨Physical.extremal_uses_all j,?_,?_⟩
  · rw [varietyCount_eq _ (Physical.extremal_uses_all j)]
    exact Physical.extremal_support j
  · exact fun h => Physical.extremal_no_solution j ((Puzzle.hasSolution_iff _).mp h)

/-- No common colour permutation and simultaneous reflection identifies two entries. -/
theorem extremal_inequivalent (j k : Fin 5)
    (h : Equivalent (extremalFamily j) (extremalFamily k)) : j = k := by
  simp only [extremalFamily_eq,
    equivalent_iff _ _ (Physical.extremal_uses_all _) (Physical.extremal_uses_all _)] at h
  exact Physical.extremal_inequivalent j k h

/-- Exactly the distributions with disjoint repeated-colour supports obstruct assembly. -/
theorem generalized_obstructions (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 5) (hy : ∑ i, y i = 5) :
    (∀ i, UsesAllColours (generalizedFamily x y i)) ∧
      (¬ HasSolution (generalizedFamily x y) ↔ x 0 * y 1 = 0 ∧ x 2 * y 2 = 0) := by
  rw [generalizedFamily_eq]
  exact ⟨Physical.generalized_uses_all x y,
    by
      change (¬ Puzzle.HasSolution (Physical.generalizedFamily x y)) ↔ _
      rw [Puzzle.hasSolution_iff]
      exact Physical.generalized_no_solution_iff x y hx hy⟩

end FiveColour.Submission
