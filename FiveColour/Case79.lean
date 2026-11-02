module
public import FiveColour.Incidence
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Replay.Case79
open Certificate
open scoped BigOperators
def root : Box 75 := { lower := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], upper := ![2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] }
def bad : Finset (Fin 75) := {1,2,3,4,5,6,8,9,10,11,12,14,15,16,17,20,21,22,24,26,27,28,29,30,31,32,33,34,35,36,37,39,40,41,42,43,44,45,48,49,50,51,52,53,54,55,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,74}
def problem : Problem 75 78 where
  goal := 15
  alternatives r :=
    if r.val = 0 then [{ neighbours := ∅, rhs := 0 }]
    else if r.val = 1 then [{ neighbours := Finset.univ, rhs := 15 }]
    else if r.val = 2 then [{ neighbours := bad, rhs := 1 }]
    else hallCuts ⟨r.val - 3, by omega⟩
def proof : Proof 75 78 := (.step 2 (.close 6))
theorem accepted : check problem root proof = true := by decide +kernel
theorem excludes : ∀ x, root.Contains x → ¬ problem.Admissible x :=
  check_sound problem proof root accepted
end FiveColour.Replay.Case79
