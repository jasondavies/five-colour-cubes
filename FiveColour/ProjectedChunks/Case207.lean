module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case207
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538572461504338143573274126223462950690675705247977443137688163756565230079967232⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538572461504338143573274126223462950690675705247977443137688163756565230079967232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 0 (.split 10 0 (.split 17 0 (.split 14 0 (.split 16 0 (.step 29 (.step 3 (.close 24))) (.step 7 (.step 38 (.step 4 (.close 24))))) (.step 37 (.step 5 (.step 7 (.close 19))))) (.step 7 (.step 39 (.step 5 (.step 7 (.step 11 (.close 19))))))) (.step 7 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.step 3 (.close 13))) (.step 7 (.step 4 (.close 24)))) (.step 7 (.step 13 (.step 20 (.close 4))))) (.step 7 (.step 13 (.split 35 0 (.split 36 0 (.step 5 (.close 20)) (.step 20 (.close 19))) (.step 33 (.close 19)))))) (.step 7 (.close 13))))) (.step 7 (.step 5 (.close 28)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case207
