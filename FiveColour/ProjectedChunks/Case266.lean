module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case266
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5521043907542942304444273349974256210237858414479900115351655871710218330848335100272209500492439451204401349345248359448319927274980396901890324052043390889644925427693797469519555930583350056309401939094551710925825⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨28556685682855072753564, 5521043902401079285245703114100180852279210293007498667362342662451989309891206542789498860922644088213908551180839958200813931295309341388374755720237955488435477265172545430290149588851967973593695416591434567910401, 0⟩]
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
def root : Box := ⟨1, 5521043907542942304444273349974256210237858414479900115351655871710218330848335100272209500492439451204401349345248359448319927274980396901890324052043390889644925427693797469519555930583350056309401939094551710924801⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 5 0 (.split 6 0 (.split 11 0 (.split 12 0 (.split 21 0 (.step 71 (.split 26 0 (.split 31 0 (.step 40 (.step 63 (.step 4 (.close 31)))) (.step 31 (.step 4 (.close 63)))) (.step 4 (.step 31 (.step 40 (.close 39)))))) (.step 4 (.step 40 (.close 4)))) (.step 31 (.step 4 (.step 68 (.split 21 0 (.step 31 (.close 4)) (.step 4 (.close 24))))))) (.step 31 (.step 4 (.step 68 (.split 21 0 (.step 31 (.close 4)) (.step 4 (.close 24))))))) (.split 11 0 (.split 12 0 (.step 31 (.step 4 (.step 68 (.split 21 0 (.step 31 (.close 4)) (.step 4 (.close 24)))))) (.split 21 0 (.split 26 0 (.split 28 0 (.step 4 (.step 15 (.step 31 (.close 4)))) (.step 31 (.close 4))) (.step 68 (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 34 0 (.step 6 (.step 4 (.close 10))) (.step 7 (.close 15))) (.step 6 (.close 15))) (.step 4 (.close 7))) (.step 6 (.close 15))) (.step 4 (.close 7))))) (.step 15 (.step 4 (.close 24))))) (.step 31 (.step 4 (.close 7))))) (.split 6 0 (.split 11 0 (.step 31 (.step 4 (.step 68 (.split 21 0 (.step 31 (.close 4)) (.step 4 (.close 24)))))) (.split 21 0 (.split 26 0 (.step 31 (.step 68 (.split 27 0 (.step 4 (.step 14 (.close 71))) (.split 31 0 (.step 4 (.step 7 (.close 11))) (.step 14 (.close 4)))))) (.split 27 0 (.step 4 (.close 6)) (.step 7 (.step 4 (.close 6))))) (.step 14 (.step 4 (.close 24))))) (.step 68 (.split 11 0 (.step 4 (.close 7)) (.step 24 (.close 31)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1, 5521043907542942304444273349974256210237858414479900115351655871710218330848335100272209500492439451204401349345248359448319927274980396901890324052043390889644925427693797469519555930583350056309401939094551710925825⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 1 0 (.reuse 0) (.run (.split 5 0 (.split 6 0 (.step 4 (.close 40)) (.split 28 0 (.step 4 (.close 7)) (.step 4 (.close 15)))) (.split 6 0 (.split 28 0 (.step 4 (.close 6)) (.step 4 (.close 14))) (.split 11 0 (.step 4 (.close 7)) (.step 4 (.close 6)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case266
