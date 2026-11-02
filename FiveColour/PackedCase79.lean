module
public import FiveColour.PackedCalibration
public import FiveColour.PackedVerified
@[expose] public section
namespace FiveColour.Packed.Replay79
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def root : Box := ⟨2,5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955202⟩
def families (r : Fin 78) : List Cut :=
  if r.val=0 then [⟨0, 0, 0⟩]
  else if r.val=1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val=2 then [⟨28333982513054604320638, 5653548961323977936207446023492293789637427680963565645079116961171007703958153517710676933081192149104274965168909591535334047588824900222804598519983799630397728618045415955558607618852931956421013581412778303766396929, 1⟩]
  else (cuts[r.val-3]!).toList
-- Generated from the archived Q5P2 certificate; checked by the Lean kernel.
def proof : Certificate.Proof 75 78 := (.step 2 (.close 6))
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
end FiveColour.Packed.Replay79
