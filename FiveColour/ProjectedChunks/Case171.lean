module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case171
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 28917902937172147168773571194107361348028707608564358790441414591489567237846093247577167047201785708323742081000904862807664589671867092959920745359742744217496139613819135257856398130140019888022462615677321759353029525504⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩]
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
def root : Box := ⟨5368709120, 28917902937172147168773571194107361348028707608564358790441414591489567237846093247577167047201785708323742081000904862807664589671867092959920745359742744217496139613819135257856398130140019888022462615677321759353029525504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.split 14 2 (.step 31 (.split 38 2 (.step 3 (.step 5 (.split 56 2 (.split 74 2 (.step 18 (.close 5)) (.split 2 1 (.step 18 (.step 5 (.step 11 (.step 17 (.close 31))))) (.step 5 (.close 77)))) (.split 2 1 (.step 31 (.step 5 (.step 18 (.close 59)))) (.step 5 (.close 59)))))) (.step 5 (.split 14 1 (.step 41 (.step 3 (.split 2 1 (.step 31 (.step 18 (.step 28 (.step 5 (.close 3))))) (.step 5 (.close 41))))) (.step 5 (.close 41)))))) (.step 5 (.split 38 1 (.step 17 (.step 3 (.step 31 (.split 2 1 (.step 18 (.step 5 (.step 11 (.step 17 (.close 3))))) (.step 5 (.close 17)))))) (.step 5 (.close 17)))))))
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
end FiveColour.Packed.ProjectedChunks.Case171
