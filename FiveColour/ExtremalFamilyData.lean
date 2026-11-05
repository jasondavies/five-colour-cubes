module
public import FiveColour.ExtremalFamily
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

def uniformDeficit : Fin 4 → Fin 75 → ℕ :=
![![31,1,1,1,1,1,1,1,1,32,16,1,4,1,32,128,249,252,4,4,4,8,252,8,1,1,1,1,32,32,64,16,1,32,4,4,4,4,1,128,8,32,8,1,1,1,4,1,64,250,128,128,128,1,4,1,1,1,64,64,1,4,1,32,64,64,64,64,1,1,1,64,4,1,64],![31,1,1,1,1,1,1,1,1,32,16,1,4,1,32,128,249,252,4,4,4,8,128,8,1,1,1,1,32,32,64,16,1,32,4,4,4,4,1,128,8,32,8,1,1,1,4,1,64,250,128,128,128,1,4,1,1,1,64,246,1,4,1,32,64,64,32,16,1,1,1,64,4,1,128],![31,1,1,1,1,1,1,1,1,32,16,1,4,1,32,128,16,252,4,4,4,8,252,8,1,1,1,1,32,32,64,16,1,32,4,4,4,4,1,32,8,32,8,1,1,1,4,1,64,250,250,128,128,1,4,1,1,1,64,64,1,4,1,32,64,64,64,64,1,1,1,64,4,1,64],![31,1,1,1,1,1,1,1,1,32,16,1,4,1,32,128,16,252,4,4,4,8,128,8,1,1,1,1,32,32,64,16,1,32,4,4,4,4,1,32,8,32,8,1,1,1,4,1,64,250,250,128,128,1,4,1,1,1,64,246,1,4,1,32,64,64,32,16,1,1,1,64,4,1,128]]

lemma uniform_deficits (p : Fin 4) : ∀ t : Fin 75,
    uniformDeficit p t < 256 ∧
    (uniformNeighbours p t (uniformDeficit p t)).card < (cornerSet (uniformDeficit p t)).card := by
  fin_cases p <;> decide +kernel

def familyCompletion : Fin 2 → CornerAllocation := ![⟨16,![3,0,0,2,1,2,2,2]⟩,⟨22,![0,0,2,3,2,2,2,1]⟩]
lemma family_completion_capacity : ∀ (r : Fin 2) (g : Fin 8),
    (Finset.univ.filter fun k => (familyCompletion r).group k = g).card ≤ completionCapacity g := by
  decide +kernel

lemma family_completion_fits : ∀ (r : Fin 2) (k : Fin 8) (s : Fin 75),
    completionAllowed r ((familyCompletion r).group k) s →
      (Replay.fits (familyCompletion r).target s).testBit k.val = true := by
  decide +kernel

end FiveColour.Physical
