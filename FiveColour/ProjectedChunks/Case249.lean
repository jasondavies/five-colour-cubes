module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case249
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046469715305779158844648997153197260800⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046468415963913924909512463032411750400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 28 (.step 48 (.close 16))) (.split 34 0 (.step 55 (.close 28)) (.step 33 (.step 55 (.close 33))))) (.split 30 0 (.step 55 (.close 16)) (.step 33 (.close 55)))) (.split 22 0 (.split 30 0 (.step 55 (.close 16)) (.step 33 (.close 55))) (.split 34 0 (.split 36 0 (.step 55 (.close 19)) (.step 39 (.close 54))) (.step 39 (.split 38 0 (.step 23 (.close 24)) (.step 19 (.close 23))))))) (.split 17 0 (.split 22 0 (.split 30 0 (.step 55 (.close 16)) (.step 33 (.close 41))) (.split 34 0 (.split 36 0 (.step 55 (.close 19)) (.split 38 0 (.step 20 (.close 25)) (.step 19 (.close 20)))) (.split 38 0 (.split 47 0 (.step 23 (.close 24)) (.step 19 (.close 23))) (.step 19 (.close 23))))) (.split 22 0 (.split 34 0 (.split 36 0 (.step 55 (.close 19)) (.step 39 (.close 54))) (.step 39 (.split 38 0 (.step 23 (.close 24)) (.step 19 (.close 23))))) (.step 19 (.step 20 (.close 25)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046469715305779158844648997153197260800⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.split 10 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 55 (.close 13)) (.step 33 (.step 16 (.close 55)))) (.step 13 (.step 33 (.close 45)))) (.step 13 (.split 38 0 (.step 55 (.close 45)) (.step 33 (.close 55))))) (.step 13 (.split 38 0 (.split 47 0 (.split 50 0 (.step 20 (.close 43)) (.step 33 (.close 43))) (.step 33 (.step 23 (.close 25)))) (.step 33 (.step 20 (.close 43)))))) (.split 17 0 (.step 13 (.split 38 0 (.split 47 0 (.split 50 0 (.step 40 (.close 45)) (.step 33 (.close 43))) (.step 33 (.step 23 (.close 25)))) (.step 33 (.step 23 (.close 5))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 19 (.close 25))) (.step 13 (.close 19))) (.step 13 (.close 20))) (.step 13 (.step 14 (.close 17)))) (.step 13 (.step 33 (.step 20 (.step 25 (.close 20)))))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 10 0 (.split 30 0 (.split 43 0 (.step 16 (.close 23)) (.step 28 (.close 48))) (.step 13 (.step 33 (.close 55)))) (.step 13 (.step 16 (.close 13)))) (.step 13 (.step 40 (.close 25)))) (.step 13 (.split 22 0 (.step 40 (.close 33)) (.step 20 (.close 25))))) (.split 17 0 (.step 13 (.split 22 0 (.step 40 (.close 19)) (.step 19 (.close 25)))) (.step 19 (.step 13 (.step 20 (.close 25))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case249
