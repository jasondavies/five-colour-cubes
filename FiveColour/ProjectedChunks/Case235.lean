module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case235
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5136856365239144160511821461895676803098098203906065863435968310709567554884586152995250217751349323138580355361835765296975865335368111197387003884827978599168176226223504222468253027787886623593264972824576⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37033564156298044177383, 5789234131004114112605798393242650429804653116085229495907826956687667789266125362145452370754004878501022282187955398943580153440264784719876785736443695986532384820264588047565369260442422522659787644311954017558436250625, 0⟩]
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
def root : Box := ⟨1073741824, 5136856365239144160511821461895676803098098203906065863435968310709567554884586152995250217751349323138580355361835765296975865335368111197387003884827978599168176226223504222468253027787886623593264972824576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 0 (.split 61 0 (.split 50 0 (.step 20 (.step 14 (.close 16))) (.step 33 (.step 14 (.step 15 (.close 19))))) (.step 13 (.split 50 0 (.step 20 (.step 14 (.close 33))) (.step 33 (.step 14 (.step 15 (.close 19))))))) (.step 13 (.split 50 0 (.step 20 (.close 16)) (.step 33 (.step 17 (.close 19))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case235
