module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case128
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11296055834832869987796435368818511453405415647414046721704491883222870508335826053969275537834712255323917684155888125811076046762591213145750531405297272894356834555768415900411033161219002711630447295525258236675489795⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨28333982513054604320638, 5653548961323977936207446023492293789637427680963565645079116961171007703958153517710676933081192149104274965168909591535334047588824900222804598519983799630397728618045415955558607618852931956421013581412778303766396929, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3, 11296055834832869987796435368818511453405415647414046721704491883222870508335826053969275537834712255323917684155888125811076046762591213145750531405297272894356834555768415900411033161219002711630447295525258236675489795⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 1 (.split 18 1 (.split 19 1 (.step 41 (.step 59 (.step 60 (.step 16 (.step 28 (.step 60 (.step 16 (.step 21 (.close 26))))))))) (.step 16 (.step 41 (.step 59 (.step 26 (.step 28 (.step 49 (.step 22 (.close 60))))))))) (.step 16 (.step 76 (.step 41 (.step 21 (.step 28 (.step 21 (.close 49)))))))) (.step 10 (.step 28 (.step 41 (.step 47 (.step 10 (.close 49))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case128
