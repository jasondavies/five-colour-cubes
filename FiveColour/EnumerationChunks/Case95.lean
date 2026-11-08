module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case95
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5521038642265172833200147547967109089353045885300071091523950175381210239080945455680487378812237807309374308743922137730250255167048851371801048557727439395436265562530597376489739476867741587587473242199939463774209⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨30666541081021128896446, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124037639541146111563493128984644470311576664498607971097082070547331612438551329471180924412418929488251918999356417, 0⟩]
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
def root : Box := ⟨1, 5521038642265172833200147547967109089353045885300071091523950175381210239080945455680487378812237807309374308743922137730250255167048851371801048557727439395436265562530597376489739476867741587587473242199939463774209⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.step 39 (.close 11)) (.step 15 (.step 11 (.close 21)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case95
