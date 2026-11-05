module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case240
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671950575509780998251715943100744157061746766997448621089428693307308219943280967680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11593776385211095628535, 5789234131009374248507341982684158355876555513350053335929015326897327162342062193097593244396629436776638632267636611235444786831573185258760290656459859266733554791122816590519108237010294841316599838966919287400980022272, 0⟩]
  else (cuts[r.val-3]!).toList

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

namespace Part0
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671950575509780998251715943100744157061746766997448621089428693307308219943280967680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 0 (.split 10 0 (.split 16 0 (.split 22 0 (.step 29 (.split 14 0 (.step 20 (.step 15 (.close 19))) (.step 13 (.step 20 (.close 17))))) (.step 7 (.step 45 (.step 11 (.step 24 (.step 13 (.step 17 (.close 19)))))))) (.split 17 0 (.step 7 (.step 67 (.step 11 (.step 19 (.step 13 (.step 15 (.close 17))))))) (.split 26 0 (.split 14 0 (.split 22 0 (.step 24 (.close 19)) (.step 19 (.step 20 (.close 11)))) (.step 13 (.step 19 (.step 20 (.close 11))))) (.step 7 (.close 19))))) (.step 7 (.step 13 (.split 35 0 (.split 64 0 (.split 36 0 (.step 17 (.step 11 (.close 20))) (.step 20 (.step 11 (.close 15)))) (.step 33 (.step 17 (.step 11 (.step 19 (.close 20)))))) (.step 33 (.step 17 (.step 19 (.step 11 (.close 20))))))))) (.split 16 0 (.split 17 0 (.split 34 0 (.split 35 0 (.step 7 (.close 11)) (.step 29 (.close 7))) (.step 29 (.step 7 (.close 11)))) (.step 7 (.close 11))) (.split 17 0 (.step 7 (.close 11)) (.step 7 (.close 11))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case240
