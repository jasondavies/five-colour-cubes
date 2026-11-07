module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case221
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538570652252943810507720632926822189942115497904467042503875047231814006925688832⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593704327342179793651, 5789228615357111146520043253955950924962759905236944250816662429627930946143174768881773115736627492968050798482740711356931196351281104609431181736320982633118032348601960626826787145704805298534408245321323047477072364544, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538570652252943810507720632926822189942115497904467042503875047231814006925688832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 0 (.split 10 0 (.split 17 0 (.split 14 0 (.split 63 0 (.step 7 (.split 35 0 (.step 24 (.close 33)) (.step 33 (.close 20)))) (.step 37 (.step 3 (.step 7 (.close 24))))) (.step 37 (.step 5 (.step 7 (.close 24))))) (.split 14 0 (.step 39 (.step 4 (.step 7 (.step 11 (.close 19))))) (.step 7 (.split 16 0 (.step 37 (.step 5 (.close 20))) (.step 13 (.step 19 (.close 20))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 63 0 (.step 7 (.split 35 0 (.split 38 0 (.step 3 (.close 24)) (.step 3 (.close 5))) (.step 33 (.close 20)))) (.step 37 (.step 7 (.close 13)))) (.step 7 (.step 39 (.step 4 (.step 11 (.close 25)))))) (.step 7 (.split 35 0 (.step 13 (.split 38 0 (.split 36 0 (.step 17 (.close 24)) (.step 20 (.close 24))) (.step 33 (.step 5 (.close 14))))) (.step 33 (.step 17 (.close 38)))))) (.step 7 (.step 13 (.close 3))))) (.split 14 0 (.split 26 0 (.step 7 (.close 5)) (.step 7 (.close 29))) (.split 16 0 (.step 7 (.step 5 (.close 11))) (.step 7 (.close 11))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case221
