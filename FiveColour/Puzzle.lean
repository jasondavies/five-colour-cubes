module
public import ColourCubes.Physical
@[expose] public section

/-! Geometric statement definitions. No five-colour catalogue or certificates. -/
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

end FiveColour.Puzzle
