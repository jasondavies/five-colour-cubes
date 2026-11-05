module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case174
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 27578261315509951190293573009181879821591769750344375331181694856734734084824678774284926034156302484953028786068393433627153006591828477985447283404083304479089702709126428102159652818623773131050019927839648969129984⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨5368709120, 27578261315509951190293573009181879821591769750344375331181694856734734084824678774284926034156302484953028786068393433627153006591828477985447283404083304479089702709126428102159652818623773131050019927839648969129984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 29 (.step 31 (.step 75 (.split 35 2 (.split 16 1 (.step 29 (.split 17 1 (.step 3 (.step 29 (.step 3 (.step 9 (.step 29 (.step 3 (.step 18 (.step 29 (.step 3 (.step 26 (.close 31))))))))))) (.step 3 (.step 18 (.close 29))))) (.step 3 (.step 18 (.close 29)))) (.step 9 (.step 29 (.step 32 (.step 38 (.step 31 (.step 75 (.step 3 (.close 18)))))))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case174
