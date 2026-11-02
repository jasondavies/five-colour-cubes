module
public import FiveColour.CatalogueData
@[expose] public section
namespace FiveColour.Physical

/-- One explicit deficient corner set for each target; bit k denotes corner k. -/
def lowerCutMask : Fin 75 → Nat :=
  ![31,1,1,1,1,1,1,1,1,32,16,1,4,1,32,128,249,4,4,4,4,8,8,4,1,1,1,1,32,32,64,16,1,4,4,4,4,4,1,128,8,8,4,1,1,1,4,1,16,250,128,32,128,1,4,1,1,1,16,4,1,4,1,32,64,64,32,16,1,1,1,4,4,1,64]

def lowerCut (t : Fin 75) : Finset (Fin 8) :=
  Finset.univ.filter fun k => (lowerCutMask t).testBit k.val

end FiveColour.Physical
