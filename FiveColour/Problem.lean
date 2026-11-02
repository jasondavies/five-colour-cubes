module
public import ThreeColour.CornerGeometry
@[expose] public section
namespace FiveColour.Physical

abbrev Cube := Fin 6 → Fin 5

def UsesAllColours (c : Cube) : Prop := ∀ a, ∃ f, c f = a

/-- A physical copy can be rotated to match the three exposed target faces. -/
def Fits (c t : Cube) (k : Fin 8) : Prop :=
  ∃ r : Fin 24, ∀ f : Fin 3,
    c (MacMahon.rotations r (MacMahon.exposedFaces k f)) = t (MacMahon.exposedFaces k f)

/-- The pinned geometric theorem applies to repeated colours as well. -/
theorem fits_iff_corner (c t : Cube) (k : Fin 8) :
    Fits c t k ↔ ∃ l : Fin 8,
      ThreeColour.Geometry.CyclicEq (ThreeColour.Geometry.corner c l)
        (ThreeColour.Geometry.corner t k) :=
  ThreeColour.Geometry.corner_rotation_iff c t k

/-- Distinct indices are distinct physical copies, even when colours agree. -/
def HasSolution {n : Nat} (cubes : Fin n → Cube) : Prop :=
  ∃ target : Cube, UsesAllColours target ∧
    ∃ copies : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (copies k)) target k

def Threshold15 : Prop :=
  ∀ cubes : Fin 15 → Cube, (∀ i, UsesAllColours (cubes i)) → HasSolution cubes

def cubeA : Cube := ![0,0,1,2,3,4]
def cubeB : Cube := ![0,1,2,3,2,4]
def cubeC : Cube := ![0,3,1,2,4,1]
def lowerFamily (i : Fin 14) : Cube :=
  if i.val < 4 then cubeA else if i.val < 9 then cubeB else cubeC

theorem lower_uses_all_colours : ∀ i, UsesAllColours (lowerFamily i) := by
  unfold UsesAllColours
  decide +kernel

/-- These are the intended physical conclusions; no proof is asserted here. -/
def SharpThreshold15 : Prop := Threshold15 ∧ ¬ HasSolution lowerFamily
end FiveColour.Physical
