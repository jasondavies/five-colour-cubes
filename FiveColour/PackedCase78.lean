module
public import FiveColour.PackedCalibration
public import FiveColour.PackedVerified
@[expose] public section
namespace FiveColour.Packed.Replay78
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def root : Box := ⟨2,5789234136395753411692881238169227500374411343012498997361331656212907769098245984562169002127015908277226114944835056582655132436110218345276409496704667659165840661608791535934022489219257755193906216122845178590347133954⟩
def families (r : Fin 78) : List Cut :=
  if r.val=0 then [⟨0, 0, 0⟩]
  else if r.val=1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val=2 then [⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 1⟩]
  else (cuts[r.val-3]!).toList
-- Generated from the archived Q5P2 certificate; checked by the Lean kernel.
def proof : Certificate.Proof 75 78 := (.split 40 1 (.split 60 1 (.split 1 0 (.split 2 0 (.split 3 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.step 2 (.step 4 (.close 5))) (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.step 55 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 8 (.step 12 (.close 16))))))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 5 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.close 5)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.close 5))) (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.step 55 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.close 6))))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 5 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.close 5))) (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 10 (.step 12 (.close 16)))))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 10)))) (.step 2 (.step 4 (.close 5)))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.split 31 0 (.split 32 0 (.split 33 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 5 (.step 6 (.close 2)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 5 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16)))))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.close 12))))) (.step 2 (.step 4 (.step 6 (.close 12))))) (.step 2 (.step 4 (.step 6 (.close 12))))) (.step 2 (.close 5)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.close 8))))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 5)))) (.split 3 0 (.split 1 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.step 68 (.step 2 (.step 4 (.close 5)))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 5 (.close 2))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 5 (.close 2))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4)))) (.step 5 (.split 3 0 (.split 1 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 6 (.step 8 (.step 12 (.close 16))))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.close 5))) (.step 5 (.step 24 (.close 2)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.close 5))) (.step 5 (.step 24 (.close 2)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.step 8 (.close 16)))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.close 16)))))))
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
end FiveColour.Packed.Replay78
