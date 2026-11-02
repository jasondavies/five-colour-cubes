module
public import MacMahon.Rotations
@[expose] public section

/-! Geometric statement definitions. No five-colour catalogue or certificates. -/
namespace FiveColour.Puzzle

abbrev Cube := Fin 6 → Fin 5

def UsesAllColours (c : Cube) : Prop := ∀ a, ∃ f, c f = a

/-- Eight distinct copies, each properly rotated to match its three exterior faces.
The target uses all five fixed colours; interior faces impose no conditions. -/
def HasSolution {n : Nat} (cubes : Fin n → Cube) : Prop :=
  ∃ target : Cube, UsesAllColours target ∧
    ∃ copies : Fin 8 ↪ Fin n, ∀ k,
      ∃ r : Fin 6 → Fin 6, MacMahon.ProperRotation r ∧
        ∀ axis : Fin 3,
          cubes (copies k) (r (MacMahon.exposedFaces k axis)) =
            target (MacMahon.exposedFaces k axis)

def cubeA : Cube := ![0,0,1,2,3,4]
def cubeB : Cube := ![0,1,2,3,2,4]
def cubeC : Cube := ![0,3,1,2,4,1]
def lowerFamily (i : Fin 14) : Cube :=
  if i.val < 4 then cubeA else if i.val < 9 then cubeB else cubeC

end FiveColour.Puzzle
