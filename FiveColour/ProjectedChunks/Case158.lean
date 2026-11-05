module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case158
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609052407963891564844801750966025983656641259262978284425460518535197400462954156266032212493897119243892514764004194515870889048924768709411534538613749021637209072652814126988171297727720763216437870813442473984⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩]
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
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025983656641259262978284425460518535197400462954156266032212493897119243892514764004194515870889048924768709411534538613749021637209072652814126988171297727720763216437870813442473984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 31 (.split 26 2 (.split 35 2 (.step 31 (.split 16 1 (.step 3 (.split 17 1 (.step 3 (.step 9 (.step 29 (.step 3 (.close 18))))) (.step 3 (.step 18 (.close 29))))) (.step 3 (.step 18 (.close 29))))) (.step 9 (.step 29 (.step 38 (.step 3 (.step 18 (.step 29 (.step 3 (.step 26 (.close 31)))))))))) (.step 9 (.step 29 (.step 3 (.step 18 (.step 26 (.close 29)))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case158
