module
public import FiveColour.Symmetry
public import FiveColour.Multiplicity
@[expose] public section
namespace FiveColour.Physical

/-- The global transformations used in the case generator. -/
structure PuzzleSymmetry where
  colour : Equiv.Perm (Fin 5)
  mirror : Bool

namespace PuzzleSymmetry

def apply (s : PuzzleSymmetry) (c : Cube) : Cube :=
  recolour s.colour (if s.mirror then reflectCube c else c)

def inverse (s : PuzzleSymmetry) : PuzzleSymmetry := ⟨s.colour.symm, s.mirror⟩

def slots (s : PuzzleSymmetry) : Equiv.Perm (Fin 8) :=
  if s.mirror then reflectionSlots else Equiv.refl _

@[simp] lemma inverse_apply (s : PuzzleSymmetry) (c : Cube) : s.inverse.apply (s.apply c) = c := by
  cases s with
  | mk p b =>
    cases b <;> funext f <;> simp [apply, inverse, recolour, reflectCube, reflectFace_involutive]

@[simp] lemma apply_inverse (s : PuzzleSymmetry) (c : Cube) : s.apply (s.inverse.apply c) = c := by
  cases s with
  | mk p b =>
    cases b <;> funext f <;> simp [apply, inverse, recolour, reflectCube, reflectFace_involutive]

theorem usesAllColours_apply (s : PuzzleSymmetry) (c : Cube) :
    UsesAllColours (s.apply c) ↔ UsesAllColours c := by
  cases s with
  | mk p b => cases b <;> simp [apply, usesAllColours_recolour, usesAllColours_reflect]

theorem fits_apply (s : PuzzleSymmetry) (c t : Cube) (k : Fin 8) :
    Fits (s.apply c) (s.apply t) k ↔ Fits c t (s.slots k) := by
  cases s with
  | mk p b => cases b <;> simp [apply, slots, reflectionSlots, fits_recolour, fits_reflect]

theorem hasSolution_apply {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube) :
    HasSolution (fun j => s.apply (cubes j)) ↔ HasSolution cubes := by
  cases s with
  | mk p b => cases b <;> simp [apply, hasSolution_recolour, hasSolution_reflect]

lemma apply_rotate (s : PuzzleSymmetry) (c : Cube) (r : Fin 24) :
    ∃ q : Fin 24, s.apply (rotate c r) = rotate (s.apply c) q := by
  cases s with
  | mk p b =>
    cases b
    · exact ⟨r, rfl⟩
    · obtain ⟨q, hq⟩ := reflect_rotate c r
      exact ⟨q, by simpa only [apply, Bool.true_eq, ↓reduceIte, recolour_rotate] using congrArg (recolour p) hq⟩

end PuzzleSymmetry

/-- The physical orientation of a cube does not affect its catalogue index. -/
lemma catalogueIndex_spec (c : Cube) (hc : UsesAllColours c) :
    ∃ r : Fin 24, c = rotate (catalogue (catalogueIndex c)) r := by
  obtain ⟨i, r, hr⟩ := catalogue_complete c hc
  have hi : catalogueIndex c = i := by
    rw [funext hr]
    exact catalogue_index_rotations i r
  exact ⟨r, by rw [hi]; exact funext hr⟩

lemma catalogueIndex_rotate (c : Cube) (hc : UsesAllColours c) (r : Fin 24) :
    catalogueIndex (rotate c r) = catalogueIndex c := by
  obtain ⟨s, hs⟩ := catalogueIndex_spec c hc
  obtain ⟨q, hq⟩ := MacMahon.rotation_composition s r
  have he : rotate c r = rotate (catalogue (catalogueIndex c)) q := by
    funext f
    change c (MacMahon.rotations r f) = catalogue (catalogueIndex c) (MacMahon.rotations q f)
    rw [hq]
    exact congrFun hs (MacMahon.rotations r f)
  rw [he]
  exact catalogue_index_rotations _ _

/-- Induced action on the 75 proper-rotation varieties. -/
def varietyAction (s : PuzzleSymmetry) (i : Fin 75) : Fin 75 :=
  catalogueIndex (s.apply (catalogue i))

/-- Classifying before or after a global transformation gives the same variety. -/
theorem catalogueIndex_apply (s : PuzzleSymmetry) (c : Cube) (hc : UsesAllColours c) :
    catalogueIndex (s.apply c) = varietyAction s (catalogueIndex c) := by
  obtain ⟨r, hr⟩ := catalogueIndex_spec c hc
  obtain ⟨q, hq⟩ := s.apply_rotate (catalogue (catalogueIndex c)) r
  have he : s.apply c = rotate (s.apply (catalogue (catalogueIndex c))) q := by
    conv_lhs => rw [hr]
    exact hq
  rw [he]
  exact catalogueIndex_rotate _ ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours _)) q

lemma varietyAction_inverse (s : PuzzleSymmetry) (i : Fin 75) :
    varietyAction s.inverse (varietyAction s i) = i := by
  have h := catalogueIndex_apply s.inverse (s.apply (catalogue i))
    ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours i))
  simpa only [PuzzleSymmetry.inverse_apply, catalogue_index_faces, varietyAction] using h.symm

lemma varietyAction_apply_inverse (s : PuzzleSymmetry) (i : Fin 75) :
    varietyAction s (varietyAction s.inverse i) = i := by
  have h := catalogueIndex_apply s (s.inverse.apply (catalogue i))
    ((s.inverse.usesAllColours_apply _).mpr (catalogue_uses_all_colours i))
  simpa only [PuzzleSymmetry.apply_inverse, catalogue_index_faces, varietyAction] using h.symm

/-- Global transformations permute varieties; no two distinct varieties collapse. -/
def varietyEquiv (s : PuzzleSymmetry) : Equiv.Perm (Fin 75) where
  toFun := varietyAction s
  invFun := varietyAction s.inverse
  left_inv := varietyAction_inverse s
  right_inv := varietyAction_apply_inverse s

/-- Every multiplicity is transported exactly by the induced variety permutation. -/
theorem multiplicity_apply {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (i : Fin 75) :
    multiplicity (fun j => s.apply (cubes j)) (varietyEquiv s i) = multiplicity cubes i := by
  unfold multiplicity
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, catalogueIndex_apply s _ (hc j)]
  change varietyEquiv s (catalogueIndex (cubes j)) = varietyEquiv s i ↔ catalogueIndex (cubes j) = i
  exact (varietyEquiv s).injective.eq_iff

/-- The same transport for sums over arbitrary sets of varieties, including root budgets. -/
theorem mass_apply {n : Nat} (s : PuzzleSymmetry) (cubes : Fin n → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (S : Finset (Fin 75)) :
    Certificate.mass (multiplicityVector (fun j => s.apply (cubes j))) (S.image (varietyEquiv s)) =
      Certificate.mass (multiplicityVector cubes) S := by
  unfold Certificate.mass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun v : Nat => (v : Int)) (multiplicity_apply s cubes hc i)
  · exact fun _ _ _ _ h => (varietyEquiv s).injective h

end FiveColour.Physical
