module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case210
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197376314982795397038080⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32016031753816107707303, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697928522998852134929247591988189268012958721, 0⟩]
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197376314982795397038080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 16 0 (.split 30 0 (.step 9 (.step 18 (.close 7))) (.step 33 (.step 7 (.step 9 (.step 15 (.step 13 (.close 18))))))) (.step 53 (.step 4 (.close 7)))) (.step 46 (.step 7 (.close 15)))) (.step 70 (.step 7 (.step 43 (.close 4))))) (.step 54 (.step 7 (.step 54 (.step 43 (.step 13 (.step 4 (.close 14)))))))) (.split 16 0 (.split 17 0 (.step 52 (.step 7 (.step 52 (.step 9 (.step 13 (.step 4 (.close 18))))))) (.step 7 (.step 13 (.step 24 (.step 15 (.step 4 (.close 9))))))) (.step 7 (.step 13 (.split 35 0 (.split 17 0 (.step 24 (.step 4 (.step 9 (.close 15)))) (.step 23 (.step 15 (.step 9 (.close 19))))) (.step 24 (.step 4 (.step 9 (.close 15))))))))) (.split 26 0 (.split 35 0 (.step 7 (.step 4 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case210
