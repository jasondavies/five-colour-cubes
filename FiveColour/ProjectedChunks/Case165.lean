module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case165
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4, 16944083752249304981694653053227767180124721533385000441821735681254984351434983749170886024335023870794441833078052531515354776169681293489499272249430950793523776392226349558863848659660562254030664299314485006593687556⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨28332973916744803409790, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817695038019906389503288666496898347799934006886082109530042226608181194165891837046351977983017174142770775990320198592700397491585025, 0⟩]
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
def root : Box := ⟨4, 16944083752249304981694653053227767180124721533385000441821735681254984351434983749170886024335023870794441833078052531515354776169681293489499272249430950793523776392226349558863848659660562254030664299314485006593687556⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 2 (.split 60 2 (.split 40 1 (.split 60 1 (.split 7 1 (.split 13 1 (.step 28 (.step 4 (.step 41 (.step 4 (.step 6 (.close 7)))))) (.step 16 (.step 28 (.step 16 (.step 4 (.step 6 (.close 41))))))) (.step 10 (.step 6 (.step 7 (.step 10 (.close 28)))))) (.step 4 (.step 10 (.step 16 (.step 28 (.step 7 (.step 41 (.step 7 (.close 59))))))))) (.step 4 (.step 28 (.step 41 (.step 10 (.step 6 (.step 16 (.step 6 (.close 59))))))))) (.step 4 (.step 10 (.step 16 (.step 63 (.step 7 (.step 28 (.step 41 (.close 59))))))))) (.step 4 (.step 28 (.step 41 (.step 43 (.step 6 (.step 10 (.step 16 (.close 43))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case165
