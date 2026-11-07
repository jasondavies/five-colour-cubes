module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case175
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 25684272028429099487874233413777581212211281975066764066744015121745437991995180082018078058234010403492737585833200607766258852075668606616028452204973642856602513356453301391012234419195431465963846415417344⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37033564156298044177399, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497705040614186417671967029225310810172032001, 0⟩]
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
def root : Box := ⟨5368709120, 25684272028429099487874233413777581212211281975066764066744015121745437991995180082018078058234010403492737585833200607766258852075668606616028452204973642856602513356453301391012234419195431465963846415417344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.step 31 (.step 62 (.step 72 (.split 49 2 (.split 50 2 (.split 61 2 (.split 62 2 (.split 59 2 (.split 69 2 (.step 18 (.step 31 (.close 3))) (.step 3 (.step 72 (.step 18 (.close 31))))) (.step 3 (.step 62 (.step 18 (.close 31))))) (.step 72 (.step 3 (.split 16 1 (.split 17 1 (.step 64 (.step 18 (.close 31))) (.step 18 (.close 64))) (.step 18 (.close 64)))))) (.step 64 (.step 72 (.step 3 (.split 16 1 (.split 17 1 (.step 64 (.step 18 (.close 31))) (.step 18 (.close 64))) (.step 18 (.close 64))))))) (.step 62 (.step 3 (.split 16 1 (.split 17 1 (.step 52 (.step 18 (.close 31))) (.step 18 (.close 52))) (.step 18 (.close 52)))))) (.step 52 (.step 62 (.step 3 (.split 16 1 (.split 17 1 (.step 52 (.step 18 (.close 31))) (.step 18 (.close 52))) (.step 18 (.close 52))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case175
