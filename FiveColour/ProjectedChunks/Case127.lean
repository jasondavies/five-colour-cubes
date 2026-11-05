module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨3, 11296055834832869987796435368818511453409565162982927714663004291086561669486838500201517974734713203683608537043001238940233693604284521888980745502894925424500195765505459131012400547679902741285862792995850784960675843⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 1 (.split 13 1 (.split 25 1 (.split 31 1 (.split 33 1 (.split 41 1 (.split 31 0 (.step 41 (.step 59 (.step 49 (.step 55 (.step 7 (.close 16)))))) (.step 4 (.step 41 (.step 49 (.step 55 (.step 59 (.step 24 (.step 32 (.step 16 (.step 6 (.close 22))))))))))) (.step 4 (.step 43 (.step 24 (.close 32))))) (.step 18 (.step 43 (.step 24 (.close 32))))) (.step 18 (.step 43 (.split 33 1 (.step 43 (.step 24 (.close 32))) (.step 34 (.close 43)))))) (.step 28 (.split 31 1 (.split 33 1 (.step 28 (.step 4 (.step 28 (.close 43)))) (.step 4 (.step 6 (.step 28 (.step 34 (.close 43)))))) (.step 4 (.step 6 (.step 43 (.step 16 (.step 21 (.close 28))))))))) (.step 16 (.split 31 1 (.step 49 (.split 33 1 (.split 41 1 (.step 28 (.step 41 (.step 16 (.step 49 (.step 50 (.step 16 (.close 21))))))) (.step 4 (.step 16 (.step 24 (.close 22))))) (.step 4 (.step 16 (.step 22 (.step 21 (.close 24))))))) (.step 4 (.step 16 (.close 24)))))) (.step 10 (.split 31 1 (.split 33 1 (.split 41 1 (.step 28 (.step 41 (.step 59 (.step 47 (.step 49 (.step 10 (.step 16 (.close 21)))))))) (.step 4 (.step 6 (.step 24 (.close 10))))) (.step 4 (.step 6 (.step 22 (.step 24 (.close 10)))))) (.step 4 (.step 6 (.step 16 (.step 24 (.step 10 (.close 22))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3, 11296055834832869987796435368818511453417864194120689700580029106813943991788863392666002848534704523507489598839644234544871451708202478136968726934564552664183699148951526715310563556638837228935648028408997749503033347⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 60 1 (.reuse 0) (.run (.step 5 (.split 7 1 (.split 13 1 (.split 25 1 (.split 31 1 (.split 33 1 (.step 18 (.step 41 (.step 49 (.step 50 (.step 45 (.step 59 (.step 7 (.close 45)))))))) (.step 4 (.step 17 (.close 18)))) (.step 4 (.step 17 (.close 18)))) (.step 4 (.step 5 (.step 7 (.close 28))))) (.step 4 (.step 5 (.close 16)))) (.step 4 (.step 5 (.step 7 (.close 10)))))))) (.run (.step 5 (.step 28 (.step 41 (.step 43 (.step 24 (.step 6 (.step 8 (.step 24 (.close 49)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case127
