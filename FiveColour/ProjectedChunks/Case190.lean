module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case190
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771019609799623546659451080723385482094035334207167706959323862783369045321187328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨8697816018884160690787, 5789228615351851010613595997138052592638682822227458134619796719202355412426545471141122180311221556529185888591485252639940046211353397484466286064875003982802949791475817793838739904160783699852089509014813351896620728320, 0⟩]
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771019609799623546659451080723385482094035334207166439307513528142731102520344576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 24 0 (.split 49 0 (.step 58 (.close 5)) (.step 5 (.step 7 (.step 10 (.close 13))))) (.step 5 (.close 46))) (.split 42 0 (.step 53 (.step 5 (.close 7))) (.step 7 (.step 33 (.close 5))))) (.split 30 0 (.split 42 0 (.step 5 (.step 7 (.step 5 (.close 11)))) (.step 7 (.step 5 (.close 11)))) (.step 7 (.step 33 (.close 5))))) (.split 14 0 (.split 22 0 (.step 54 (.step 5 (.close 7))) (.step 7 (.step 54 (.step 5 (.close 11))))) (.step 63 (.step 7 (.step 17 (.step 5 (.close 11))))))) (.split 14 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 5 (.step 46 (.close 5))) (.step 7 (.step 5 (.step 33 (.close 5))))) (.step 7 (.step 70 (.close 5)))) (.split 22 0 (.step 7 (.step 54 (.step 5 (.close 11)))) (.step 70 (.step 19 (.step 7 (.step 19 (.close 5))))))) (.step 63 (.step 7 (.step 17 (.step 11 (.step 5 (.close 19)))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 52 (.step 58 (.close 10))) (.step 55 (.step 16 (.step 10 (.step 7 (.close 5)))))) (.step 5 (.close 7))) (.step 5 (.step 7 (.step 10 (.close 13))))) (.step 55 (.step 5 (.step 7 (.close 5))))) (.step 55 (.step 63 (.step 65 (.close 5))))) (.step 63 (.step 5 (.step 7 (.step 10 (.close 13))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771019609799623546659451080723385482094035334207167706958113756372133698735177728⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 4 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 10 (.step 18 (.step 5 (.close 7)))) (.step 7 (.step 54 (.step 5 (.close 7))))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.step 63 (.close 7)))) (.step 7 (.step 13 (.split 16 0 (.step 7 (.step 5 (.close 7))) (.step 7 (.close 5)))))))) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 4 0 (.split 22 0 (.split 30 0 (.split 42 0 (.step 52 (.split 36 0 (.step 18 (.step 10 (.close 5))) (.step 7 (.step 13 (.close 5))))) (.step 7 (.step 13 (.step 52 (.step 5 (.close 10)))))) (.step 7 (.step 13 (.step 33 (.step 5 (.close 10)))))) (.step 7 (.step 13 (.step 70 (.close 5))))) (.step 7 (.close 5))) (.step 7 (.step 13 (.step 54 (.step 5 (.step 13 (.close 5))))))) (.step 7 (.step 13 (.split 13 0 (.step 13 (.split 38 0 (.split 39 0 (.split 50 0 (.step 20 (.step 5 (.close 10))) (.step 33 (.step 5 (.close 11)))) (.step 33 (.step 5 (.close 11)))) (.step 33 (.step 5 (.step 10 (.close 14)))))) (.step 13 (.close 5)))))) (.step 7 (.step 13 (.step 52 (.step 13 (.close 5))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771019609799623546659451080723385482094035334207167706959323862783369045321187328⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 7 0 (.split 8 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.split 10 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 5 (.close 7)) (.step 7 (.close 5))) (.step 5 (.close 7))) (.step 5 (.step 7 (.close 11)))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 48 (.close 5)))) (.step 7 (.step 63 (.close 7)))) (.step 7 (.step 63 (.step 7 (.close 5))))))) (.run (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 4 0 (.split 10 0 (.split 13 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 36 0 (.step 46 (.step 5 (.close 7))) (.step 7 (.close 5))) (.step 7 (.step 46 (.close 5)))) (.step 5 (.close 7))) (.step 5 (.close 7))) (.split 22 0 (.split 25 0 (.split 38 0 (.step 52 (.step 46 (.close 7))) (.step 7 (.step 10 (.close 5)))) (.step 7 (.step 10 (.close 5)))) (.step 7 (.close 5)))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 65 (.close 5)))) (.step 7 (.split 13 0 (.step 63 (.step 5 (.close 7))) (.split 43 0 (.step 63 (.close 16)) (.step 5 (.close 7)))))) (.step 7 (.split 24 0 (.split 13 0 (.step 63 (.step 5 (.close 7))) (.split 43 0 (.step 63 (.close 10)) (.step 5 (.close 7)))) (.step 24 (.step 5 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case190
