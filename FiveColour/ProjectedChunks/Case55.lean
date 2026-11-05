module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case55
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138612676846049625343512027709798489669117743896486821272943871589502533568036864⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260032287596181804126590577603936934133866658330096003181493260345104267962343596764330681434112⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.step 7 (.split 38 1 (.split 42 1 (.step 7 (.split 43 1 (.step 7 (.close 5)) (.step 3 (.close 7)))) (.step 7 (.close 5))) (.split 42 1 (.step 5 (.step 7 (.split 16 0 (.step 7 (.step 10 (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 7))))) (.step 7 (.step 5 (.step 37 (.close 41))))))) (.step 7 (.step 45 (.step 7 (.step 5 (.step 37 (.close 39))))))) (.step 7 (.step 45 (.split 74 1 (.step 37 (.step 7 (.step 5 (.close 37)))) (.step 5 (.step 7 (.step 5 (.close 37)))))))) (.step 7 (.close 5))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 7 (.split 38 1 (.step 20 (.step 7 (.step 5 (.close 19)))) (.step 5 (.step 7 (.step 5 (.close 19))))))) (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 5 (.step 7 (.split 42 1 (.split 34 0 (.step 7 (.step 27 (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 7))) (.step 5 (.close 7))))) (.step 3 (.step 5 (.close 37)))) (.step 5 (.step 7 (.step 5 (.step 37 (.close 39)))))) (.step 5 (.step 7 (.close 37)))) (.step 7 (.step 5 (.close 17)))) (.step 7 (.step 11 (.step 20 (.step 3 (.close 5)))))) (.step 7 (.step 11 (.step 19 (.step 7 (.step 5 (.close 17)))))))) (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.step 5 (.step 3 (.step 5 (.step 37 (.step 39 (.close 41)))))) (.step 3 (.step 5 (.close 20)))) (.step 3 (.step 5 (.close 19)))) (.step 5 (.close 17))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138612676846049625343512027709798489669117743896486821272943871589502533568036864⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 7 (.reuse 0))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case55
