module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case70
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5653543569679536981196946412616686640498315936812243935685725083698590658270650634706916204403427661912866746291945337247102666105685933582966387019461497053753410440467153841998707561271549610527107888750601742428667906⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨23611742337562385305406, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340647030340707156299050781889704801152725612693487204679141161216171784460345221283290785923672815928606721, 0⟩]
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
def root : Box := ⟨2, 5653543569679536981196946412616686640498315936812243935685725083698590658270650634706916204403427661912866746291945337247102666105685933582966387019461497053753410440467153841998707561271549610527107888750601742428667906⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.step 18 (.close 7)) (.step 18 (.step 9 (.step 6 (.step 12 (.step 15 (.close 18))))))))
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
end FiveColour.Packed.ProjectedChunks.Case70
