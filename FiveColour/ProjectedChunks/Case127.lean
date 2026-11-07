module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case127
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11296055834832869987796435368818511453417864194120689700580029106813943991788863392666002848534704523507489598839644234544871451708202478136968726934564552664183699148951526715310563556638837228935648028408997749503033347⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 0⟩]
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
def root : Box := ⟨3, 11296055834832869987796435368818511453417864194120689700580029106813943991788863392666002848534704523507489598839644234544871451708202478136968726934564552664183699148951526715310563556638837228935648028408997749503033347⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 60 1 (.split 7 1 (.split 13 1 (.split 25 1 (.split 31 1 (.split 33 1 (.split 41 1 (.split 31 0 (.step 41 (.step 59 (.step 49 (.step 55 (.close 60))))) (.step 4 (.step 41 (.step 49 (.step 59 (.step 24 (.step 32 (.close 55)))))))) (.step 43 (.step 24 (.close 32)))) (.step 18 (.step 43 (.step 24 (.close 32))))) (.step 18 (.split 33 1 (.step 43 (.step 24 (.close 32))) (.step 34 (.close 43))))) (.split 31 1 (.split 33 1 (.step 28 (.step 4 (.step 28 (.close 43)))) (.step 4 (.step 28 (.close 43)))) (.step 43 (.close 28)))) (.step 16 (.split 31 1 (.split 33 1 (.split 41 1 (.step 28 (.step 41 (.step 16 (.step 50 (.step 16 (.close 21)))))) (.step 16 (.step 24 (.close 22)))) (.step 16 (.step 22 (.close 24)))) (.step 16 (.close 24))))) (.step 10 (.split 31 1 (.split 33 1 (.split 41 1 (.step 28 (.step 41 (.step 59 (.step 47 (.step 49 (.step 10 (.close 24))))))) (.step 6 (.step 24 (.close 10)))) (.step 6 (.step 22 (.step 24 (.close 10))))) (.step 6 (.step 24 (.close 34)))))) (.split 7 1 (.split 13 1 (.split 25 1 (.split 31 1 (.split 33 1 (.step 18 (.step 41 (.step 49 (.step 50 (.close 63))))) (.step 4 (.close 18))) (.step 4 (.close 18))) (.step 5 (.close 28))) (.step 5 (.close 16))) (.step 5 (.close 10)))) (.step 5 (.step 28 (.step 41 (.step 43 (.step 24 (.close 59))))))))
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
end FiveColour.Packed.ProjectedChunks.Case127
