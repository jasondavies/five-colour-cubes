module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case56
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520661873432413930091811010963534734505009995389894990493733299354520747423412594371113130017162316079069306338423024812671756013854899244834558871948243410637680861614365895957676032⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨18741817655939057892083, 5789228615357111146520043253955950924962759905236944250816662429627930946143177890630323431728858874565283113377443029201743447180998372957674332211373112187324901345482895844991322794115058517540719501872435874350517715968, 0⟩]
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
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520661873432413930091811010963534734505009995389894990493733299354520747423412594371113130017162316079069306338423024812671756013854899244834558871948243410637680861614365895957676032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 14 0 (.split 38 0 (.split 16 0 (.step 20 (.step 14 (.close 39))) (.split 22 0 (.step 20 (.step 14 (.close 39))) (.step 45 (.close 20)))) (.step 33 (.step 23 (.step 14 (.close 16))))) (.step 13 (.split 38 0 (.step 43 (.step 11 (.step 5 (.step 17 (.close 20))))) (.step 33 (.step 5 (.step 19 (.close 20)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case56
