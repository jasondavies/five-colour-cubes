module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case135
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11296055834832869987796435368818511453417864194112960625533994590124553288006993314858004828523347800500274732351475520277676143797107188367664178404898905068963101492058577636625592941266863917295407072111847831819517955⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨3, 11296055834832869987796435368818511453417864194112960625533994590124553288006993314858004828523347800500274732351475520277676143797107188367664178404898905068963101492058577636625592941266863917295407072111847831819517955⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.step 10 (.step 16 (.step 6 (.step 5 (.step 7 (.step 28 (.step 7 (.close 41)))))))) (.step 5 (.step 28 (.step 41 (.step 6 (.step 10 (.step 6 (.close 16)))))))))
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
end FiveColour.Packed.ProjectedChunks.Case135
