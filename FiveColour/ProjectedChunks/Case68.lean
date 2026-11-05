module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case68
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5521038642265172833200147547967109093502561454181064050036358039072371390093391693737634073175397067519661474380473399108094805148002877135841565576802259044784170226608573741233322099101874768194929960324856838881282⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨30666541043489288744894, 5653548961323972924649819221030976445153133834664318320894055915633373970312978306221952124172187412202403697552556976832140169149520348233180031118858191672351478379158650493494278216967794504680829880264136510559749121, 0⟩]
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
def root : Box := ⟨2, 5521038642265172833200147547967109093502561454181064050036358039072371390093391693737634073175397067519661474380473399108094805148002877135841565576802259044784170226608573741233322099101874768194929960324856838881282⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 37 1 (.split 40 1 (.split 45 1 (.split 60 1 (.split 31 0 (.split 33 0 (.step 24 (.step 6 (.step 7 (.close 15)))) (.step 4 (.step 23 (.step 6 (.step 15 (.close 19)))))) (.step 4 (.step 31 (.close 6)))) (.step 4 (.step 15 (.close 6)))) (.step 4 (.step 15 (.close 31)))) (.step 4 (.step 31 (.step 7 (.close 15))))) (.step 4 (.step 31 (.step 6 (.close 15)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case68
