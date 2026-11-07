module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case199
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409449891788137011620874289152⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨8697816018884211022451, 5789228615357111146515144370645293582521562950893008474422619893061853696606201481707084707191459675456370831556440846149949944370837561739506646933964126675846887447766945946864215253787366754672169104713068902630525239296, 0⟩]
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036172141798081453496374777585074176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 36 0 (.step 5 (.close 18)) (.step 54 (.close 58))) (.step 5 (.step 54 (.close 5)))) (.split 36 0 (.step 53 (.step 5 (.close 10))) (.step 54 (.close 58)))) (.step 70 (.split 30 0 (.step 5 (.close 11)) (.step 33 (.close 5))))) (.split 22 0 (.step 54 (.step 5 (.step 24 (.close 20)))) (.step 70 (.step 5 (.close 20))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 5 (.step 19 (.close 13))) (.step 54 (.close 5))) (.step 33 (.step 53 (.close 10)))) (.step 70 (.step 5 (.step 19 (.close 13))))) (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 63 (.close 17)) (.step 54 (.close 63))) (.step 23 (.close 20))) (.step 23 (.close 24))) (.step 53 (.step 20 (.step 23 (.close 11))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 52 (.split 36 0 (.step 10 (.step 5 (.close 13))) (.step 40 (.step 10 (.close 18))))) (.step 65 (.step 13 (.close 58)))) (.step 5 (.close 40))) (.step 55 (.step 5 (.close 17)))) (.step 63 (.step 55 (.step 5 (.step 18 (.close 27)))))) (.step 63 (.step 5 (.close 16))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409449890607545390903462985728⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 13 0 (.split 14 0 (.split 17 0 (.split 36 0 (.split 56 0 (.split 58 0 (.step 13 (.step 5 (.step 33 (.close 5)))) (.step 52 (.step 54 (.step 5 (.close 11))))) (.step 54 (.step 64 (.close 5)))) (.step 54 (.step 13 (.step 5 (.close 45))))) (.split 16 0 (.step 54 (.step 13 (.step 5 (.close 70)))) (.split 22 0 (.step 13 (.step 54 (.step 23 (.close 11)))) (.step 70 (.step 19 (.close 20)))))) (.split 39 0 (.step 13 (.close 5)) (.step 31 (.step 13 (.close 5))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.step 16 (.close 5))) (.step 40 (.close 13))) (.step 13 (.close 5))) (.step 13 (.close 5))) (.step 13 (.close 5))) (.step 13 (.step 24 (.close 13)))) (.step 13 (.step 31 (.close 13))))))) (.run (.split 14 0 (.split 16 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 51 0 (.step 5 (.close 7)) (.step 46 (.step 5 (.close 7)))) (.step 7 (.close 48))) (.step 7 (.close 48))) (.step 7 (.close 63))) (.step 7 (.close 48))) (.step 7 (.step 63 (.close 7)))) (.step 7 (.step 63 (.step 7 (.close 5)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409449891788137011620874289152⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 7 0 (.reuse 0) (.run (.split 8 0 (.split 14 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 13 0 (.split 30 0 (.split 38 0 (.split 36 0 (.step 5 (.close 7)) (.step 7 (.close 5))) (.step 55 (.step 7 (.close 10)))) (.step 7 (.close 5))) (.split 22 0 (.split 38 0 (.split 42 0 (.step 52 (.step 10 (.close 5))) (.step 7 (.step 52 (.step 7 (.close 5))))) (.step 7 (.step 10 (.close 5)))) (.step 7 (.close 5)))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 65 (.close 5)))) (.step 7 (.step 5 (.close 10)))) (.step 7 (.split 13 0 (.step 63 (.step 5 (.close 7))) (.split 43 0 (.step 63 (.close 16)) (.step 5 (.close 7)))))) (.step 7 (.split 34 0 (.split 13 0 (.step 63 (.close 10)) (.split 14 0 (.step 5 (.close 7)) (.step 5 (.close 7)))) (.step 7 (.close 5)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case199
