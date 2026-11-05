module
public import Mathlib
@[expose] public section

/-! Standalone comparator challenge, importing only Mathlib.
Faces are +x,-x,+y,-y,+z,-z. ProperRotation specifies signed permutations
with determinant +1; no rotation or variety catalogue is assumed. The eight
positions have their usual binary coordinates, as exposed_face_rule states.
Repeated copies are allowed, colours remain fixed, and interior faces are
unrestricted. Each deliberate theorem hole is a comparator target; this file
is never imported by the proof library. Solution.lean supplies the completed
proofs, including the cuboid thresholds and extremal classifications below.
-/
namespace ColourCubes

def exposedFaces : Fin 8 → Fin 3 → Fin 6 := ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + 1 else f - 1
def fromAxes (a b c : Fin 6) : Fin 6 → Fin 6 :=
  ![a, opposite a, b, opposite b, c, opposite c]

/-- Distinct coordinate axes and determinant +1. -/
def ValidAxes (a b c : Fin 6) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ c.val / 2 ∧
  (a.val % 2 + b.val % 2 + c.val % 2) % 2 =
    ((if a.val / 2 > b.val / 2 then 1 else 0) +
     (if a.val / 2 > c.val / 2 then 1 else 0) +
     (if b.val / 2 > c.val / 2 then 1 else 0)) % 2
instance (a b c : Fin 6) : Decidable (ValidAxes a b c) := by
  unfold ValidAxes; infer_instance

def ProperRotation (r : Fin 6 → Fin 6) : Prop :=
  ∃ a b c, ValidAxes a b c ∧ r = fromAxes a b c

/-- Face colours from an arbitrary palette; colours may repeat. -/
abbrev Cube (α : Type*) := Fin 6 → α

/-- Every colour in the palette occurs. -/
def UsesAllColours {α : Type*} (c : Cube α) : Prop := ∀ a, ∃ f, c f = a

instance {α : Type*} [Fintype α] [DecidableEq α] (c : Cube α) :
    Decidable (UsesAllColours c) := by
  unfold UsesAllColours
  infer_instance

/-- Matching the three exterior faces by a geometric proper rotation. -/
def Fits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 6 → Fin 6, ProperRotation r ∧ ∀ f : Fin 3,
    c (r (exposedFaces k f)) = t (exposedFaces k f)

/-- Build a specified target using eight distinct indexed copies. -/
def Builds {α ι : Type*} (cubes : ι → Cube α) (target : Cube α) : Prop :=
  ∃ placement : Fin 8 ↪ ι, ∀ k, Fits (cubes (placement k)) target k

/-- Each application chooses its own admissible target predicate. -/
def HasSolution {α ι : Type*} (allowed : Cube α → Prop) (cubes : ι → Cube α) : Prop :=
  ∃ target, allowed target ∧ Builds cubes target

theorem exposed_face_rule : ∀ k : Fin 8, ∀ d : Fin 3,
    (exposedFaces k d).val = 2*d.val + (k.val / 2^(2-d.val)) % 2 := by sorry

end ColourCubes

namespace FiveColour.Puzzle

abbrev Cube := ColourCubes.Cube (Fin 5)

def UsesAllColours (c : Cube) : Prop := ColourCubes.UsesAllColours c

/-- Eight distinct copies, each properly rotated to match its three exterior faces.
The target uses all five fixed colours; interior faces impose no conditions. -/
def HasSolution {n : Nat} (cubes : Fin n → Cube) : Prop :=
  ColourCubes.HasSolution UsesAllColours cubes

def cubeA : Cube := ![0,0,1,2,3,4]
def cubeB : Cube := ![0,1,2,3,2,4]
def cubeC : Cube := ![0,3,1,2,4,1]
def lowerFamily (i : Fin 14) : Cube :=
  if i.val < 4 then cubeA else if i.val < 9 then cubeB else cubeC

/-- The explicit fourteen-cube obstruction, including palette validity. -/
theorem lower_bound :
    (∀ i, UsesAllColours (lowerFamily i)) ∧ ¬ HasSolution lowerFamily := by sorry

/-- Every fifteen-cube collection has a five-colour corner solution. -/
theorem threshold15 (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : HasSolution cubes := by sorry

/-- A solution is guaranteed at fifteen, and fourteen can fail. -/
theorem sharp_threshold15 :
    (∀ cubes : Fin 15 → Cube, (∀ i, UsesAllColours (cubes i)) → HasSolution cubes) ∧
    ∃ cubes : Fin 14 → Cube, (∀ i, UsesAllColours (cubes i)) ∧ ¬ HasSolution cubes := by sorry

/-- The least guaranteed size, including every larger collection. -/
theorem least_guaranteed_size :
    IsLeast {m : Nat | ∀ n, ∀ cubes : Fin n → Cube,
      (∀ i, UsesAllColours (cubes i)) → m ≤ n → HasSolution cubes} 15 := by sorry

end FiveColour.Puzzle

namespace FiveColour.Submission
open scoped BigOperators

-- Named instances keep independently compiled finite tuples identical.
theorem threeNonzero : NeZero 3 := by infer_instance
theorem fiveNonzero : NeZero 5 := by infer_instance
theorem sixNonzero : NeZero 6 := by infer_instance
attribute [local instance] threeNonzero fiveNonzero sixNonzero

abbrev Cube := FiveColour.Puzzle.Cube
abbrev UsesAllColours := FiveColour.Puzzle.UsesAllColours
abbrev HasSolution := @FiveColour.Puzzle.HasSolution

/-- All exposed faces of a position must match one properly rotated source. -/
def FacesFit (source target : Cube) (faces : Finset (Fin 6)) : Prop :=
  ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧
    ∀ f ∈ faces, source (r f) = target f

/-- The twelve edges, specified by their two exterior face normals. -/
def edgeFaces : Fin 12 → Fin 2 → Fin 6 :=
  ![![0,2], ![0,3], ![0,4], ![0,5], ![1,2], ![1,3],
    ![1,4], ![1,5], ![2,4], ![2,5], ![3,4], ![3,5]]
/-- The free coordinate along each edge. -/
def edgeAxis : Fin 12 → Fin 3 := ![2,2,1,1,2,2,1,1,0,0,0,0]

/-- Eight corners and the noncorner positions on each of twelve edges.
The three entries of l are the side lengths minus two. -/
abbrev FrameSlot (l : Fin 3 → ℕ) :=
  Fin 8 ⊕ (Σ e : Fin 12, Fin (l (edgeAxis e)))
def frameExposed (l : Fin 3 → ℕ) : FrameSlot l → Finset (Fin 6)
  | .inl k => Finset.univ.image (ColourCubes.exposedFaces k)
  | .inr e => {edgeFaces e.1 0, edgeFaces e.1 1}

/-- The two free coordinates in the interior of each face. -/
def faceAxis₁ : Fin 6 → Fin 3 := ![1,1,0,0,0,0]
def faceAxis₂ : Fin 6 → Fin 3 := ![2,2,2,2,1,1]
/-- Face interiors, followed by the interior of the box. -/
abbrev Filler (l : Fin 3 → ℕ) :=
  (Σ f : Fin 6, Fin (l (faceAxis₁ f)) × Fin (l (faceAxis₂ f))) ⊕
    (Fin (l 0) × Fin (l 1) × Fin (l 2))
abbrev BoxSlot (l : Fin 3 → ℕ) := FrameSlot l ⊕ Filler l
def boxExposed (l : Fin 3 → ℕ) : BoxSlot l → Finset (Fin 6)
  | .inl p => frameExposed l p
  | .inr (.inl p) => {p.1}
  | .inr (.inr _) => ∅

/-- A frame uses distinct physical copies. The axis assignment is part of the
assembly; source moves are still proper rotations only. -/
def FrameSolvable {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ axes : Equiv.Perm (Fin 3),
    let l := fun i => ![a-2,b-2,c-2] (axes i)
    ∃ target, UsesAllColours target ∧ ∃ placement : FrameSlot l ↪ Fin n,
      ∀ p, FacesFit (cubes (placement p)) target (frameExposed l p)
/-- A complete box additionally fills face interiors and interior positions. -/
def BoxSolvable {n : ℕ} (a b c : ℕ) (cubes : Fin n → Cube) : Prop :=
  ∃ axes : Equiv.Perm (Fin 3),
    let l := fun i => ![a-2,b-2,c-2] (axes i)
    ∃ target, UsesAllColours target ∧ ∃ placement : BoxSlot l ↪ Fin n,
      ∀ p, FacesFit (cubes (placement p)) target (boxExposed l p)

def FrameGuarantee (a b c n : ℕ) : Prop :=
  ∀ cubes : Fin n → Cube, (∀ i, UsesAllColours (cubes i)) → FrameSolvable a b c cubes
def BoxGuarantee (a b c n : ℕ) : Prop :=
  ∀ cubes : Fin n → Cube, (∀ i, UsesAllColours (cubes i)) → BoxSolvable a b c cubes

/-- Two colourings represent the same variety exactly when a proper rotation
matches all six faces. No catalogue or canonical representative is assumed. -/
def SameVariety (c d : Cube) : Prop :=
  ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧ ∀ f, c (r f) = d f

/-- Physical copies belonging to the variety represented by c. -/
noncomputable def copiesOf {n : ℕ} (cubes : Fin n → Cube) (c : Cube) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => SameVariety (cubes i) c
noncomputable def copyCount {n : ℕ} (cubes : Fin n → Cube) (c : Cube) : ℕ :=
  (copiesOf cubes c).card
/-- Number of equivalence classes of sources under proper rotation. -/
noncomputable def varietyCount {n : ℕ} (cubes : Fin n → Cube) : ℕ := by
  classical
  exact (Finset.univ.image fun i => copiesOf cubes (cubes i)).card
noncomputable def SupportGuarantee (k v : ℕ) : Prop :=
  ∀ n, ∀ cubes : Fin n → Cube, (∀ i, UsesAllColours (cubes i)) →
    varietyCount cubes ≤ k → v ≤ n → HasSolution cubes

/-- Apply a common colour permutation and, optionally, reflection across the
 yz-plane. Reflection is a symmetry of collections, not an individual move. -/
def transform (p : Equiv.Perm (Fin 5)) (mirror : Bool) (c : Cube) : Cube :=
  fun f => p (c (if mirror then ![1,0,2,3,4,5] f else f))
/-- Equality of physical variety counts after one common global symmetry. -/
noncomputable def Equivalent {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube) : Prop :=
  ∃ p : Equiv.Perm (Fin 5), ∃ mirror : Bool, ∀ c : Cube, UsesAllColours c →
    copyCount (fun i => transform p mirror (a i)) c = copyCount b c

/-- The opposite-repeat anchor; face order is +x,-x,+y,-y,+z,-z. -/
def anchor : Cube := ![0,0,1,2,3,4]
/-- Adjacent cut C(01), with repeated colours 2,3,4 respectively. -/
def leftVariety : Fin 3 → Cube :=
  ![![0,1,2,3,2,4], ![0,1,2,3,3,4], ![0,1,2,4,3,4]]
/-- Adjacent cut C(124), with repeated colours 1,2,4 respectively. -/
def rightVariety : Fin 3 → Cube :=
  ![![0,3,1,2,4,1], ![0,3,1,2,4,2], ![0,3,1,4,4,2]]
/-- The five pairs of adjacent varieties in the classification. -/
def representativeLeft : Fin 5 → Fin 3 := ![0,0,1,1,2]
def representativeRight : Fin 5 → Fin 3 := ![0,2,0,1,1]
def extremalFamily (j : Fin 5) (i : Fin 14) : Cube :=
  if i.val < 4 then anchor else if i.val < 9 then
    leftVariety (representativeLeft j) else rightVariety (representativeRight j)

/-- Assign an index within a five-copy block to its variety. -/
def distributionType (v : Fin 3 → ℕ) (i : ℕ) : Fin 3 :=
  if i < v 0 then 0 else if i < v 0 + v 1 then 1 else 2
/-- Four anchor copies and two blocks of five adjacent sources. -/
def generalizedFamily (x y : Fin 3 → ℕ) (i : Fin 14) : Cube :=
  if i.val < 4 then anchor else if i.val < 9 then
    leftVariety (distributionType x (i.val-4)) else
    rightVariety (distributionType y (i.val-9))

end FiveColour.Submission

namespace FiveColour.Submission
open scoped BigOperators

/-- Exact number of available sources guaranteeing a cuboid frame. -/
theorem frame_threshold (a b c n : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    FrameGuarantee a b c n ↔ max 15 (max (4*(a+b+c)-16) (2*(a+b+c)+1)) ≤ n := by sorry

/-- Exact number of available sources guaranteeing a complete cuboid. -/
theorem box_threshold (a b c n : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    BoxGuarantee a b c n ↔ max (a*b*c) (max 15 (2*(a+b+c)+1)) ≤ n := by sorry

/-- Exact corner thresholds for a bound on the number of proper-rotation varieties. -/
theorem support_threshold (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {v | SupportGuarantee k v} (if k = 1 then 8 else if k = 2 then 13 else 15) := by sorry

/-- Every fourteen-source obstruction has maximum variety multiplicity at most five. -/
theorem multiplicity_bound (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes)
    (c : Cube) (hcol : UsesAllColours c) : copyCount cubes c ≤ 5 := by sorry

/-- Complete classification of the obstructions using three varieties. -/
theorem three_variety_classification (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : varietyCount cubes = 3) :
    ¬ HasSolution cubes ↔ ∃ j : Fin 5, Equivalent cubes (extremalFamily j) := by sorry

/-- All five representatives use exactly three varieties and fail to assemble. -/
theorem extremal_examples (j : Fin 5) :
    (∀ i, UsesAllColours (extremalFamily j i)) ∧
    varietyCount (extremalFamily j) = 3 ∧ ¬ HasSolution (extremalFamily j) := by sorry

/-- No common colour permutation and simultaneous reflection identifies two entries. -/
theorem extremal_inequivalent (j k : Fin 5)
    (h : Equivalent (extremalFamily j) (extremalFamily k)) : j = k := by sorry

/-- Exactly the distributions with disjoint repeated-colour supports obstruct assembly. -/
theorem generalized_obstructions (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 5) (hy : ∑ i, y i = 5) :
    (∀ i, UsesAllColours (generalizedFamily x y i)) ∧
      (¬ HasSolution (generalizedFamily x y) ↔ x 0 * y 1 = 0 ∧ x 2 * y 2 = 0) := by sorry

end FiveColour.Submission
