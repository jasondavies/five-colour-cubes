module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case167
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4, 16159137489556603414258021608585868786251622001897329545425639517879283187557791481814961215911765811483823385224561263526939013288355611914398530557596530201573000985896641947927905288757043373883567639036310847492⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨35390078503202014101502, 5653548961323977941106329334149636230834382024899345816765989398247113357360444308706969489112206482570655852878300101049798490493935305494313846245092879000572939700782106487339445782328873872231040107873767697761174529, 0⟩]
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
def root : Box := ⟨4, 16159137489556603414258021608585868786251622001897329545425639517879283187557791481814961215911765811483823385224561263526939013288355611914398530557596530201573000985896641947927905288757043373883567639036310847492⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 33 1 (.step 34 (.step 66 (.step 34 (.step 66 (.step 34 (.close 67)))))) (.step 36 (.step 34 (.step 66 (.step 34 (.step 74 (.step 36 (.step 66 (.step 34 (.close 36)))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case167
