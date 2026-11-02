module
public import FiveColour.PackedCalibration
public import FiveColour.PackedVerified
@[expose] public section
namespace FiveColour.Packed.Replay165
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def root : Box := ⟨3,5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102984587902778241877863493039901399371263796604286144121676364744842310441402164107420723690746717535762448132994484786846237699⟩
def families (r : Fin 78) : List Cut :=
  if r.val=0 then [⟨0, 0, 0⟩]
  else if r.val=1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val=2 then [⟨35390078503202014101502, 5653548961323977941106329334149636230834382024899345816765989398247113357360444308706969489112206482570655852878300101049798490493935305494313846245092879000572939700782106487339445782328873872231040107873767697761174529, 1⟩]
  else (cuts[r.val-3]!).toList
-- Generated from the archived Q5P2 certificate; checked by the Lean kernel.
def proof : Certificate.Proof 75 78 := (.step 2 (.step 12 (.step 18 (.step 32 (.step 40 (.step 42 (.step 51 (.step 55 (.step 69 (.step 34 (.close 2)))))))))))
theorem accepted : Verified.check 15 families root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

theorem excludes : ∀ x, root.model.Contains x → ¬ (Verified.problem 15 families).Admissible x :=
  Verified.check_sound 15 families families_valid proof root root_valid accepted
end FiveColour.Packed.Replay165
