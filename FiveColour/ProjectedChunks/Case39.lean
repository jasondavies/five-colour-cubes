module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case39
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945775553919410948789671030933787587844363013977094851835157240217396749799522304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630669409018422557671, 5789234131004114112605798393242650429804653116085229495907826956687667789262928691629928794709070122937714079890866485902908449148557118512623615738864880308980283049286057048738638195494140525221857074735173807150830978049, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945775553919410948789671030933787587844363013977094851835157240217396749799522304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.step 58 (.split 25 0 (.step 7 (.close 58)) (.split 34 0 (.split 36 0 (.split 42 0 (.step 55 (.step 9 (.step 7 (.close 58)))) (.step 7 (.close 21))) (.step 7 (.close 22))) (.step 7 (.close 28))))) (.step 7 (.step 52 (.close 58)))) (.step 54 (.step 7 (.step 52 (.close 54))))) (.step 46 (.step 7 (.step 9 (.close 46))))) (.step 7 (.close 58))) (.step 58 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.step 58 (.step 7 (.close 21))) (.step 7 (.step 9 (.close 58)))) (.step 7 (.step 9 (.step 52 (.close 54))))) (.step 7 (.close 9))) (.step 7 (.close 58))))) (.step 7 (.step 29 (.close 58)))) (.step 7 (.split 49 1 (.step 45 (.step 7 (.step 37 (.close 21)))) (.step 7 (.close 37))))) (.split 34 1 (.split 36 1 (.split 42 1 (.step 58 (.split 43 1 (.split 51 1 (.split 67 1 (.step 58 (.step 7 (.close 28))) (.step 7 (.step 26 (.close 28)))) (.step 7 (.step 54 (.close 21)))) (.step 7 (.close 46)))) (.step 7 (.close 28))) (.step 28 (.close 7))) (.step 7 (.step 16 (.step 28 (.close 4)))))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 19))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case39
