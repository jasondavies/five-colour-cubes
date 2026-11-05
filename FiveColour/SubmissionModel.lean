module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Fin
public import FiveColour.Puzzle
@[expose] public section

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
