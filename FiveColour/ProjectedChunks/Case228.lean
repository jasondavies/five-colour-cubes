module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case228
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197375162060191278563328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩]
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197375162060191278563328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 22 0 (.split 42 0 (.split 26 0 (.split 16 0 (.split 30 0 (.split 34 0 (.step 9 (.close 71)) (.step 15 (.close 39))) (.step 53 (.step 9 (.close 39)))) (.step 53 (.step 4 (.close 17)))) (.step 46 (.step 71 (.close 7)))) (.step 70 (.split 16 0 (.step 62 (.step 7 (.step 18 (.close 33)))) (.step 7 (.step 24 (.step 43 (.close 4))))))) (.split 30 0 (.split 34 0 (.split 17 0 (.step 62 (.step 68 (.close 13))) (.step 7 (.step 54 (.step 4 (.close 24))))) (.step 7 (.step 68 (.step 70 (.close 20))))) (.step 7 (.step 70 (.step 33 (.step 24 (.close 4))))))) (.split 16 0 (.split 22 0 (.step 52 (.split 17 0 (.split 30 0 (.step 15 (.step 7 (.close 18))) (.step 7 (.step 33 (.step 13 (.close 9))))) (.step 7 (.step 54 (.step 4 (.close 15)))))) (.step 7 (.step 70 (.step 13 (.step 15 (.close 39)))))) (.step 7 (.split 12 0 (.step 13 (.split 35 0 (.split 50 0 (.split 62 0 (.step 39 (.close 15)) (.step 23 (.close 40))) (.step 33 (.close 43))) (.step 24 (.close 38)))) (.step 13 (.close 4)))))))
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
end FiveColour.Packed.ProjectedChunks.Case228
