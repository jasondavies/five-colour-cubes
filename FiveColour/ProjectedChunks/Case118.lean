module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case118
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230375543532185472512661620688359060973719211940700356793929934630577975494023695412101357501761304679310398946797439422013954760976597242535182865627558794462127668686304338627264512⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230375543532185472512661620688359060973719211940700356793929934630577975494023695412101357501761304679310398946797439422013954760976597242535182865627558794462127668686304338627264512⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 43 1 (.split 42 1 (.split 51 1 (.step 7 (.split 17 0 (.step 28 (.step 59 (.step 3 (.step 75 (.close 3))))) (.step 3 (.close 59)))) (.step 3 (.close 7))) (.step 7 (.close 45))) (.step 3 (.step 7 (.close 46)))) (.step 3 (.step 41 (.step 45 (.split 72 1 (.step 3 (.step 28 (.close 41))) (.step 41 (.close 3))))))) (.step 7 (.step 39 (.close 3)))) (.step 3 (.step 38 (.step 39 (.step 45 (.split 56 1 (.split 38 1 (.step 3 (.step 29 (.close 38))) (.step 28 (.close 38))) (.step 38 (.step 3 (.close 41))))))))) (.step 7 (.step 38 (.step 41 (.step 59 (.step 75 (.step 37 (.step 7 (.close 37))))))))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 18 (.step 7 (.close 19)))))
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
end FiveColour.Packed.ProjectedChunks.Case118
