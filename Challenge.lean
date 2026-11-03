module
public import Mathlib
@[expose] public section

/-! Standalone comparator challenge, importing only Mathlib.
Faces are +x,-x,+y,-y,+z,-z. ProperRotation specifies signed permutations
with determinant +1; no rotation or variety catalogue is assumed. The eight
positions have their usual binary coordinates, as exposed_face_rule states.
Repeated copies are allowed, colours remain fixed, and interior faces are
unrestricted. Each deliberate theorem hole is a comparator target; this file
is never imported by the proof library. The full solution awaits archive replay.
-/
namespace ColourCubes

abbrev Face := Fin 6
abbrev Slot := Fin 8
def exposedFaces : Slot → Fin 3 → Fin 6 := ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

def rotations : Fin 24 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4], ![0, 1, 4, 5, 3, 2], ![0, 1, 5, 4, 2, 3], ![1, 0, 2, 3, 5, 4], ![1, 0, 3, 2, 4, 5], ![1, 0, 4, 5, 2, 3], ![1, 0, 5, 4, 3, 2], ![2, 3, 0, 1, 5, 4], ![2, 3, 1, 0, 4, 5], ![2, 3, 4, 5, 0, 1], ![2, 3, 5, 4, 1, 0], ![3, 2, 0, 1, 4, 5], ![3, 2, 1, 0, 5, 4], ![3, 2, 4, 5, 1, 0], ![3, 2, 5, 4, 0, 1], ![4, 5, 0, 1, 2, 3], ![4, 5, 1, 0, 3, 2], ![4, 5, 2, 3, 1, 0], ![4, 5, 3, 2, 0, 1], ![5, 4, 0, 1, 3, 2], ![5, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]]

theorem faceOne_bound : 1 < 6 := by decide

def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + ⟨1, faceOne_bound⟩ else f - ⟨1, faceOne_bound⟩
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

/-- Exactly `n` distinct colours occur on the six faces. -/
def Uses {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Prop :=
  (Finset.univ.image c).card = n

instance {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Decidable (Uses n c) := by
  unfold Uses
  infer_instance

/-- Every colour in the palette occurs. -/
def UsesAllColours {α : Type*} (c : Cube α) : Prop := ∀ a, ∃ f, c f = a

instance {α : Type*} [Fintype α] [DecidableEq α] (c : Cube α) :
    Decidable (UsesAllColours c) := by
  unfold UsesAllColours
  infer_instance

/-- Matching by an index in the verified rotation table. -/
def TableFits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 24, ∀ f : Fin 3,
    c (rotations r (exposedFaces k f)) = t (exposedFaces k f)

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

theorem exposed_face_rule : ∀ k : Slot, ∀ d : Fin 3,
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
