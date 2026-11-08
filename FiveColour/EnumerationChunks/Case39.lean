module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case39
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨22571190701410939325431, 5789234131009374248507346766749891415332201699601028324943030613121803494466317085117916158989304575885048303495590499993157750471180935527552348589417886828906416525556182006279541058153209277181346261459170290961901158401, 0⟩]
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
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969808844451456296024370513526645249545828128004728409323851379820724224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 54 0 (.split 56 0 (.step 71 (.step 9 (.close 10))) (.step 22 (.step 18 (.close 10)))) (.step 54 (.step 9 (.step 18 (.close 21))))) (.split 43 0 (.step 18 (.step 22 (.close 18))) (.step 54 (.step 18 (.close 9))))) (.split 35 0 (.split 36 0 (.step 58 (.step 16 (.step 18 (.close 10)))) (.split 38 0 (.step 54 (.step 15 (.close 18))) (.step 58 (.step 10 (.step 18 (.step 21 (.close 37))))))) (.step 71 (.step 29 (.step 37 (.step 18 (.close 21))))))) (.split 34 0 (.split 36 0 (.split 54 0 (.step 18 (.step 53 (.close 10))) (.step 18 (.step 53 (.step 9 (.step 13 (.close 18)))))) (.step 54 (.step 18 (.step 9 (.close 13))))) (.split 35 0 (.split 36 0 (.split 54 0 (.step 18 (.step 58 (.step 10 (.close 33)))) (.step 18 (.close 9))) (.step 54 (.step 33 (.step 18 (.step 10 (.close 13)))))) (.step 18 (.step 33 (.step 9 (.step 13 (.step 18 (.close 33))))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 70 (.split 36 0 (.step 10 (.step 26 (.close 21))) (.step 22 (.step 9 (.close 18))))) (.step 26 (.step 10 (.close 18)))) (.split 35 0 (.split 36 0 (.step 70 (.step 16 (.step 10 (.step 15 (.close 18))))) (.step 18 (.step 15 (.step 16 (.step 18 (.step 21 (.close 18))))))) (.step 15 (.step 75 (.close 18))))) (.split 34 0 (.step 18 (.step 26 (.step 9 (.close 52)))) (.step 18 (.step 37 (.step 18 (.close 22))))))))
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
def root : Box := ⟨1569275433846670190958947355801916604025588861117082370048, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124562214791526885279147220101032242858843698492564804993024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 22 (.step 54 (.step 9 (.step 13 (.close 18))))) (.split 36 0 (.split 38 0 (.step 18 (.step 9 (.step 21 (.close 22)))) (.step 18 (.step 21 (.close 18)))) (.step 18 (.step 21 (.step 18 (.close 22)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 18 (.step 9 (.step 15 (.close 16)))) (.step 16 (.step 18 (.close 15)))) (.step 18 (.step 15 (.step 16 (.step 18 (.step 21 (.close 18))))))) (.step 15 (.split 49 0 (.step 21 (.step 18 (.step 9 (.close 22)))) (.step 9 (.step 16 (.close 18))))))) (.split 34 0 (.step 18 (.step 22 (.step 9 (.close 52)))) (.step 18 (.step 37 (.step 18 (.close 22)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 22 (.step 9 (.close 18)))) (.step 18 (.close 22))) (.step 9 (.step 21 (.step 22 (.close 18))))) (.split 35 0 (.split 36 0 (.step 18 (.step 22 (.step 9 (.step 15 (.step 16 (.close 18)))))) (.step 22 (.step 9 (.close 10)))) (.step 9 (.step 15 (.step 21 (.step 22 (.step 18 (.close 16))))))))) (.split 23 0 (.split 30 0 (.step 26 (.step 18 (.step 54 (.close 4)))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.close 26)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1532495540865888858358347027150309183618739123257344000, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448122994471853221080977046631092257476564001728370570979966976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 38 0 (.split 36 0 (.split 42 0 (.step 9 (.step 21 (.close 13))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 9 (.close 21)))) (.step 21 (.step 10 (.close 9)))) (.step 21 (.step 9 (.close 10)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 18 (.step 9 (.step 15 (.close 16)))) (.step 16 (.step 18 (.close 15)))) (.step 18 (.step 15 (.step 16 (.step 18 (.close 21)))))) (.step 15 (.split 49 0 (.step 21 (.step 9 (.close 10))) (.step 9 (.step 16 (.close 18))))))) (.split 34 0 (.step 18 (.close 53)) (.step 18 (.step 37 (.step 18 (.close 21)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 21 (.step 70 (.step 9 (.step 18 (.close 21)))))) (.step 18 (.step 21 (.step 18 (.step 9 (.close 22)))))) (.step 9 (.close 21))) (.split 35 0 (.split 36 0 (.step 18 (.step 21 (.step 18 (.step 9 (.close 15))))) (.step 22 (.step 18 (.step 15 (.step 16 (.step 18 (.close 21))))))) (.step 9 (.step 15 (.step 21 (.close 18))))))) (.split 23 0 (.split 30 0 (.step 26 (.step 18 (.step 55 (.step 4 (.close 35))))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.close 26)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751168005578448059393168027317231686988595200⟩
def references : Fin 3 → Box := ![Part0.root, Part1.root, Part2.root]
def proof : Chunks.Proof 3 := (.split 18 0 (.split 19 0 (.split 22 0 (.reuse 0) (.run (.split 23 0 (.split 30 0 (.split 34 0 (.step 70 (.step 18 (.step 54 (.step 4 (.close 5))))) (.split 35 0 (.step 70 (.split 38 0 (.step 58 (.step 39 (.close 13))) (.step 18 (.step 16 (.step 10 (.step 5 (.step 18 (.close 37)))))))) (.step 18 (.step 33 (.step 18 (.step 15 (.step 9 (.step 18 (.step 37 (.close 38)))))))))) (.split 42 0 (.step 70 (.step 33 (.step 4 (.close 5)))) (.step 33 (.step 40 (.close 43))))) (.split 30 0 (.step 26 (.step 18 (.step 26 (.step 4 (.step 54 (.step 4 (.close 52))))))) (.step 18 (.step 40 (.step 13 (.close 18)))))))) (.reuse 1)) (.split 19 0 (.reuse 2) (.run (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 54 (.split 56 0 (.split 72 0 (.step 10 (.step 4 (.step 13 (.step 18 (.close 21))))) (.step 9 (.step 4 (.step 18 (.close 21))))) (.step 10 (.step 18 (.close 21))))) (.step 18 (.step 10 (.close 21)))) (.step 18 (.step 21 (.step 18 (.step 9 (.close 22)))))) (.split 36 0 (.step 18 (.step 9 (.close 21))) (.step 9 (.step 21 (.step 4 (.close 18)))))) (.split 35 0 (.split 36 0 (.step 18 (.step 21 (.step 18 (.step 9 (.close 15))))) (.step 22 (.close 18))) (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.step 29 (.step 21 (.step 4 (.close 18)))) (.step 4 (.step 9 (.close 15)))) (.step 9 (.step 15 (.step 18 (.close 21))))) (.step 9 (.step 15 (.step 18 (.close 21))))) (.step 9 (.step 15 (.step 18 (.step 16 (.close 21)))))))) (.step 26 (.step 21 (.step 10 (.close 18))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124562216288104561905991808341605511560317510620239729000448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 54 (.step 5 (.close 4))) (.step 70 (.step 18 (.step 10 (.close 13))))) (.split 49 0 (.split 50 0 (.step 39 (.close 4)) (.step 18 (.step 33 (.step 18 (.close 39))))) (.step 58 (.step 13 (.step 39 (.step 4 (.step 16 (.close 33)))))))) (.split 36 0 (.step 54 (.step 33 (.step 5 (.close 4)))) (.step 33 (.step 39 (.close 4))))) (.split 30 0 (.step 22 (.step 18 (.step 54 (.close 4)))) (.step 18 (.step 40 (.step 13 (.close 18)))))) (.split 30 0 (.split 23 0 (.split 36 0 (.step 54 (.step 70 (.step 4 (.close 5)))) (.step 54 (.close 4))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 33 (.step 23 (.close 24))))) (.split 22 0 (.split 23 0 (.split 30 0 (.step 22 (.step 18 (.step 22 (.step 4 (.close 54))))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.close 22))) (.split 35 0 (.split 38 0 (.split 30 0 (.step 18 (.step 23 (.step 13 (.close 18)))) (.step 23 (.close 4))) (.step 5 (.step 18 (.step 10 (.close 20))))) (.step 18 (.step 9 (.close 20)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124562214792988386916478123019235927691559981512220737536000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 54 0 (.step 18 (.step 54 (.step 18 (.step 13 (.close 52))))) (.step 18 (.step 4 (.step 9 (.close 52))))) (.step 54 (.step 18 (.step 9 (.close 13))))) (.split 35 0 (.split 36 0 (.split 54 0 (.step 18 (.step 55 (.step 13 (.step 15 (.close 16))))) (.step 18 (.close 9))) (.step 40 (.step 43 (.step 54 (.step 18 (.step 13 (.step 15 (.close 16)))))))) (.step 18 (.step 33 (.step 18 (.step 15 (.step 9 (.step 18 (.step 37 (.close 38)))))))))) (.split 34 0 (.step 53 (.step 33 (.step 5 (.step 10 (.close 4))))) (.step 33 (.step 40 (.step 37 (.step 4 (.close 9))))))) (.split 30 0 (.split 34 0 (.step 18 (.step 4 (.close 52))) (.step 18 (.step 37 (.step 18 (.close 21))))) (.step 18 (.step 40 (.step 13 (.close 18)))))) (.split 30 0 (.split 23 0 (.split 42 0 (.step 70 (.split 35 0 (.step 58 (.step 54 (.step 18 (.close 13)))) (.step 18 (.step 24 (.step 4 (.close 13)))))) (.step 70 (.close 4))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 33 (.step 23 (.close 24))))) (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 4 (.close 52))) (.step 18 (.step 37 (.step 18 (.close 21))))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.split 35 0 (.split 38 0 (.split 49 0 (.step 24 (.step 18 (.step 23 (.close 18)))) (.step 13 (.step 18 (.step 20 (.close 9))))) (.step 5 (.step 18 (.step 10 (.close 20))))) (.step 18 (.step 9 (.close 20)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432181069606836346702217412379017845145600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 18 (.step 54 (.step 18 (.step 10 (.close 13))))) (.split 18 0 (.step 54 (.step 4 (.close 18))) (.step 18 (.step 19 (.close 4))))) (.step 18 (.step 33 (.step 18 (.step 24 (.step 4 (.step 9 (.close 13)))))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.step 40 (.step 43 (.step 54 (.step 18 (.step 23 (.close 13)))))) (.step 24 (.step 4 (.close 17)))) (.step 18 (.step 23 (.step 4 (.close 14))))) (.step 18 (.step 23 (.step 4 (.close 14))))) (.step 18 (.step 23 (.step 4 (.close 14)))))) (.split 18 0 (.split 34 0 (.split 35 0 (.step 33 (.step 24 (.step 23 (.close 13)))) (.step 23 (.step 9 (.step 19 (.step 20 (.close 24)))))) (.step 23 (.step 17 (.close 24)))) (.step 23 (.step 4 (.close 18))))) (.split 18 0 (.split 19 0 (.split 34 0 (.split 35 0 (.split 23 0 (.step 54 (.step 23 (.step 24 (.step 25 (.close 13))))) (.step 23 (.step 18 (.step 20 (.step 18 (.close 24)))))) (.step 23 (.step 19 (.close 9)))) (.step 23 (.step 24 (.step 20 (.close 4))))) (.step 23 (.step 18 (.close 20)))) (.step 23 (.step 18 (.step 19 (.step 13 (.close 18))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432181069606836346702217412379017845145600⟩
def references : Fin 4 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 16 0 (.split 17 0 (.reuse 0) (.split 18 0 (.reuse 1) (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.step 22 (.step 18 (.step 54 (.close 4)))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.step 22 (.step 18 (.close 4))))) (.split 35 0 (.split 38 0 (.split 49 0 (.step 24 (.step 18 (.step 23 (.close 18)))) (.step 13 (.step 18 (.step 19 (.step 9 (.step 17 (.close 20))))))) (.step 5 (.step 18 (.step 10 (.close 19))))) (.step 18 (.step 9 (.close 19))))) (.split 22 0 (.step 18 (.close 22)) (.step 18 (.close 20))))))) (.split 17 0 (.split 18 0 (.reuse 2) (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 4 (.close 35))) (.step 18 (.step 37 (.step 18 (.close 21))))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 18 (.step 21 (.step 9 (.close 10))))) (.split 35 0 (.split 38 0 (.split 49 0 (.step 24 (.step 18 (.step 23 (.close 18)))) (.step 13 (.step 18 (.step 19 (.step 9 (.step 17 (.close 20))))))) (.step 5 (.step 18 (.step 10 (.close 19))))) (.step 18 (.step 9 (.close 19))))) (.split 22 0 (.step 18 (.step 21 (.step 9 (.close 10)))) (.step 18 (.close 20)))))) (.reuse 3)))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969808844451456296024370513526646610675295811758582262822281106893570048⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 30 0 (.split 34 0 (.split 38 0 (.split 36 0 (.step 52 (.step 71 (.close 9))) (.step 72 (.step 22 (.step 15 (.step 9 (.step 16 (.close 18))))))) (.split 35 0 (.split 42 0 (.step 58 (.step 10 (.step 16 (.step 18 (.step 15 (.close 21)))))) (.step 58 (.step 10 (.step 18 (.step 13 (.close 15)))))) (.step 21 (.step 18 (.step 15 (.step 16 (.close 18))))))) (.split 35 0 (.split 36 0 (.step 16 (.close 9)) (.split 43 0 (.step 16 (.step 13 (.close 18))) (.step 18 (.close 10)))) (.split 49 0 (.split 50 0 (.step 71 (.step 9 (.step 15 (.close 16)))) (.step 15 (.step 18 (.close 16)))) (.step 15 (.step 16 (.step 9 (.close 18))))))) (.split 34 0 (.step 18 (.step 65 (.split 36 0 (.step 10 (.step 13 (.step 16 (.close 18)))) (.step 13 (.step 18 (.close 10)))))) (.step 52 (.step 37 (.close 10))))) (.split 34 0 (.split 35 0 (.split 38 0 (.step 70 (.split 36 0 (.step 70 (.step 9 (.step 15 (.step 16 (.close 18))))) (.step 18 (.step 22 (.step 9 (.step 15 (.step 16 (.close 18)))))))) (.step 10 (.step 16 (.step 18 (.step 21 (.step 18 (.close 15))))))) (.step 15 (.step 21 (.step 26 (.step 10 (.step 16 (.close 18))))))) (.step 16 (.step 9 (.close 18))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1532495540865890219487814710904163037117168850330189824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751169366707915743147021880815661414061441024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.split 42 0 (.step 65 (.step 9 (.step 15 (.step 16 (.close 18))))) (.step 18 (.step 26 (.step 10 (.step 15 (.step 16 (.close 18))))))) (.step 18 (.close 4))) (.step 18 (.step 22 (.step 21 (.step 9 (.step 13 (.close 16))))))) (.split 36 0 (.step 18 (.step 15 (.close 21))) (.step 15 (.step 22 (.step 18 (.step 16 (.step 18 (.close 21)))))))) (.split 35 0 (.split 36 0 (.step 18 (.step 16 (.close 9))) (.step 16 (.step 4 (.step 9 (.close 18))))) (.step 15 (.step 16 (.step 5 (.step 9 (.close 18))))))) (.step 26 (.step 10 (.step 16 (.step 21 (.close 13)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 72 (.split 59 0 (.step 10 (.step 21 (.step 18 (.step 4 (.close 15))))) (.step 5 (.step 9 (.step 15 (.step 21 (.step 18 (.close 16)))))))) (.step 10 (.step 21 (.step 18 (.step 22 (.step 13 (.step 15 (.close 16)))))))) (.step 10 (.close 21))) (.step 10 (.step 21 (.close 22)))) (.step 21 (.close 4))) (.step 22 (.step 10 (.step 21 (.step 16 (.step 4 (.close 18)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751169366707915743147021880815661414061441024⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 18 0 (.split 19 0 (.split 22 0 (.reuse 0) (.run (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 70 (.split 36 0 (.step 5 (.close 10)) (.step 13 (.step 5 (.close 10)))))) (.step 52 (.step 37 (.step 4 (.close 5))))) (.step 13 (.step 18 (.split 35 0 (.step 18 (.step 40 (.step 5 (.close 18)))) (.step 4 (.close 5)))))) (.step 18 (.step 26 (.step 10 (.step 13 (.close 16)))))))) (.run (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 72 (.split 22 0 (.split 42 0 (.step 54 (.step 10 (.step 15 (.step 16 (.close 18))))) (.step 18 (.step 26 (.step 10 (.step 15 (.step 16 (.close 18))))))) (.step 5 (.step 4 (.step 10 (.step 13 (.close 18))))))) (.step 18 (.step 22 (.close 10)))) (.split 36 0 (.step 18 (.step 15 (.step 21 (.step 22 (.step 9 (.close 16)))))) (.step 15 (.step 22 (.close 4))))) (.split 35 0 (.split 36 0 (.step 18 (.step 16 (.close 9))) (.step 16 (.step 4 (.step 9 (.close 18))))) (.step 15 (.step 16 (.step 5 (.step 9 (.close 18))))))) (.step 26 (.step 10 (.step 16 (.step 22 (.close 13)))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1461501638692032385887438686569781449384079130624, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433542199074520100556070910808744917991424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 65 (.step 5 (.step 13 (.step 5 (.close 4)))))) (.step 52 (.step 37 (.step 4 (.close 5))))) (.step 13 (.step 18 (.split 35 0 (.step 18 (.step 40 (.step 5 (.close 18)))) (.step 4 (.close 5)))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 13 (.split 23 0 (.step 23 (.step 18 (.split 34 0 (.step 18 (.step 23 (.step 5 (.step 10 (.close 18))))) (.step 23 (.step 5 (.close 16)))))) (.step 4 (.step 18 (.close 20)))))) (.split 22 0 (.step 18 (.step 21 (.step 72 (.step 22 (.step 5 (.step 4 (.step 10 (.close 13)))))))) (.step 18 (.close 20)))) (.split 19 0 (.split 22 0 (.step 18 (.step 21 (.step 4 (.step 10 (.step 13 (.close 16)))))) (.step 18 (.close 20))) (.step 21 (.step 4 (.step 10 (.step 13 (.step 16 (.close 18)))))))) (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 34 0 (.split 36 0 (.step 18 (.step 13 (.step 10 (.step 19 (.close 20))))) (.step 13 (.step 23 (.step 4 (.close 18))))) (.step 13 (.step 23 (.step 5 (.close 16))))) (.step 18 (.step 17 (.step 19 (.close 20))))) (.step 18 (.step 17 (.close 20)))) (.step 5 (.step 18 (.step 13 (.step 23 (.step 10 (.step 16 (.close 19)))))))) (.step 18 (.step 4 (.step 17 (.close 19))))) (.step 18 (.split 19 0 (.step 5 (.step 13 (.step 18 (.step 19 (.close 20))))) (.step 18 (.step 4 (.close 5))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448122992939357680215088189601973226111170691013438509076709376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 64 (.step 58 (.close 9))) (.split 38 0 (.step 18 (.step 54 (.step 9 (.step 15 (.step 13 (.close 18)))))) (.step 18 (.step 15 (.step 16 (.close 18)))))) (.split 36 0 (.split 49 0 (.step 21 (.step 18 (.close 9))) (.step 9 (.step 15 (.step 16 (.close 13))))) (.step 57 (.step 13 (.close 18))))) (.split 35 0 (.step 64 (.step 15 (.close 10))) (.step 15 (.step 10 (.close 18))))) (.split 34 0 (.step 18 (.step 53 (.split 35 0 (.step 18 (.close 9)) (.step 13 (.step 18 (.close 9)))))) (.step 64 (.step 37 (.close 9))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 70 (.step 16 (.step 10 (.step 18 (.close 15)))))) (.step 18 (.step 22 (.step 26 (.step 9 (.close 13)))))) (.step 9 (.step 15 (.step 21 (.step 26 (.step 13 (.close 18))))))) (.step 15 (.step 10 (.close 18))))) (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 62 (.step 4 (.close 9)))) (.step 64 (.step 37 (.close 4)))) (.step 13 (.step 18 (.split 35 0 (.step 43 (.step 4 (.close 18))) (.step 4 (.step 9 (.step 15 (.close 33)))))))) (.step 18 (.step 26 (.close 9))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1532495540865888859687575022935225056522546183537688576, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751168006907676055178083900221038747268939776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 54 0 (.step 53 (.step 4 (.step 10 (.step 15 (.step 13 (.close 18)))))) (.step 54 (.step 9 (.step 15 (.step 18 (.step 4 (.close 16))))))) (.step 18 (.step 16 (.close 21)))) (.step 18 (.step 22 (.step 57 (.step 9 (.step 13 (.step 15 (.close 18)))))))) (.split 36 0 (.step 18 (.step 9 (.step 15 (.close 21)))) (.step 9 (.step 15 (.step 21 (.step 13 (.close 18))))))) (.split 35 0 (.split 36 0 (.step 18 (.step 15 (.step 10 (.close 18)))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 15 (.close 4)))) (.step 26 (.step 9 (.step 21 (.step 15 (.close 13)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.split 56 0 (.step 53 (.step 9 (.step 4 (.step 15 (.step 16 (.close 21)))))) (.step 16 (.step 4 (.step 9 (.step 18 (.step 21 (.close 15))))))) (.step 9 (.step 21 (.step 15 (.step 22 (.step 4 (.close 13))))))) (.step 9 (.step 21 (.step 18 (.step 22 (.step 13 (.close 15))))))) (.step 21 (.close 4))) (.step 9 (.step 21 (.close 22)))) (.step 9 (.close 21))) (.step 22 (.step 9 (.step 15 (.step 4 (.close 18))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1496577676626845917468569053617346715934736278093824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794851495916628446785374033166422192947200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 54 (.split 35 0 (.step 4 (.close 9)) (.step 13 (.step 4 (.close 9)))))) (.step 64 (.step 37 (.close 4)))) (.step 13 (.step 18 (.split 35 0 (.step 43 (.step 4 (.close 18))) (.step 4 (.step 9 (.step 15 (.close 33)))))))) (.step 18 (.step 22 (.step 15 (.step 5 (.step 9 (.close 13))))))) (.step 13 (.split 23 0 (.step 24 (.step 18 (.split 34 0 (.step 18 (.step 24 (.step 4 (.step 9 (.close 18))))) (.step 24 (.step 4 (.close 15)))))) (.step 4 (.step 18 (.close 20)))))) (.split 22 0 (.step 18 (.step 22 (.step 9 (.step 13 (.close 15))))) (.step 18 (.close 20)))) (.split 19 0 (.split 22 0 (.step 18 (.step 22 (.split 34 0 (.step 9 (.step 15 (.step 18 (.step 4 (.close 21))))) (.step 15 (.close 4))))) (.step 18 (.close 20))) (.step 22 (.close 9)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1461501637332232146199469748589186826717286629376, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432182398834832131618090316186078125490176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 53 (.step 4 (.step 13 (.step 4 (.close 5)))))) (.step 64 (.step 37 (.close 4)))) (.step 13 (.step 18 (.split 35 0 (.step 43 (.step 4 (.close 18))) (.step 4 (.step 9 (.step 15 (.close 33)))))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 13 (.split 23 0 (.step 24 (.step 18 (.split 34 0 (.step 18 (.step 24 (.step 4 (.step 9 (.close 18))))) (.step 24 (.step 4 (.close 15)))))) (.step 4 (.step 18 (.close 20)))))) (.split 22 0 (.step 18 (.step 21 (.split 34 0 (.step 18 (.close 4)) (.step 15 (.close 4))))) (.step 18 (.close 20)))) (.split 19 0 (.split 22 0 (.step 18 (.step 21 (.step 5 (.step 9 (.step 13 (.close 15)))))) (.step 18 (.close 20))) (.step 21 (.step 4 (.step 9 (.step 13 (.step 15 (.close 18)))))))) (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 19 0 (.split 22 0 (.step 24 (.step 18 (.step 24 (.close 4)))) (.step 24 (.close 14))) (.step 5 (.step 18 (.close 20)))) (.step 18 (.close 24))) (.step 13 (.step 4 (.close 17)))) (.step 18 (.step 5 (.step 14 (.close 19))))) (.step 18 (.step 13 (.step 24 (.step 9 (.step 15 (.close 19))))))) (.step 18 (.split 19 0 (.step 4 (.step 13 (.step 18 (.step 19 (.close 20))))) (.step 18 (.close 4)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1362458695679538769726402236788426932224, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751169368037143738931937753719468474341785600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.split 30 0 (.step 16 (.close 9)) (.step 13 (.step 15 (.close 9)))) (.step 13 (.close 4))) (.step 13 (.step 22 (.step 15 (.close 10))))) (.split 36 0 (.step 13 (.step 15 (.step 10 (.close 13)))) (.step 15 (.step 4 (.step 10 (.close 13)))))) (.split 35 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.close 15)) (.step 22 (.step 13 (.close 15)))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 15 (.step 4 (.step 13 (.close 16)))))) (.step 26 (.step 15 (.step 10 (.close 13))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 72 (.step 15 (.step 4 (.close 9)))) (.step 15 (.step 4 (.step 10 (.close 13))))) (.step 16 (.close 4))) (.step 15 (.step 4 (.step 10 (.step 13 (.close 16)))))) (.step 15 (.close 4))) (.step 15 (.step 16 (.step 4 (.close 9)))))) (.split 19 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 4 (.step 10 (.step 15 (.close 13)))) (.step 5 (.step 9 (.close 15)))) (.step 5 (.step 9 (.close 15)))) (.step 15 (.step 4 (.step 10 (.close 13))))) (.step 16 (.close 4))) (.step 15 (.step 4 (.step 10 (.step 13 (.close 16)))))) (.step 15 (.close 4))) (.step 15 (.step 16 (.step 4 (.close 9))))) (.step 21 (.step 15 (.step 9 (.step 13 (.close 16))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528302515885471943814615805198336000⟩
def references : Fin 5 → Box := ![Part12.root, Part13.root, Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 5 := (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.split 30 0 (.split 42 0 (.step 16 (.step 10 (.step 15 (.close 22)))) (.step 26 (.step 10 (.step 15 (.step 16 (.close 18)))))) (.step 18 (.step 9 (.step 15 (.step 16 (.close 22)))))) (.step 4 (.step 5 (.step 9 (.step 13 (.close 18)))))) (.step 18 (.step 22 (.close 9)))) (.split 36 0 (.step 18 (.step 9 (.step 15 (.step 21 (.step 16 (.close 18)))))) (.step 9 (.step 15 (.step 21 (.step 22 (.step 13 (.close 18)))))))) (.split 35 0 (.split 36 0 (.step 18 (.step 15 (.step 10 (.close 18)))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 15 (.close 4)))) (.step 26 (.step 9 (.step 22 (.step 15 (.close 13)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 16 0 (.split 17 0 (.reuse 4) (.run (.split 18 0 (.split 19 0 (.step 13 (.step 22 (.step 15 (.step 4 (.close 5))))) (.step 4 (.close 22))) (.step 4 (.step 21 (.step 22 (.step 4 (.close 5)))))))) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.step 13 (.step 21 (.split 34 0 (.step 13 (.close 4)) (.step 13 (.close 15))))) (.step 4 (.step 21 (.step 4 (.step 5 (.close 15)))))) (.step 4 (.close 21))) (.split 18 0 (.step 13 (.step 18 (.close 4))) (.step 4 (.close 5)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448122992939357680215088188272746497976855046339032945499570176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 54 0 (.step 18 (.step 52 (.close 10))) (.step 18 (.step 52 (.step 9 (.close 18))))) (.step 54 (.step 18 (.step 9 (.close 13))))) (.split 35 0 (.step 64 (.step 15 (.close 10))) (.step 15 (.close 16)))) (.split 34 0 (.split 36 0 (.split 54 0 (.split 56 0 (.split 42 0 (.step 18 (.close 13)) (.step 13 (.close 18))) (.step 13 (.step 18 (.close 10)))) (.step 18 (.step 9 (.close 13)))) (.step 33 (.step 13 (.close 18)))) (.step 33 (.step 13 (.step 18 (.close 39)))))) (.split 30 0 (.split 34 0 (.step 18 (.step 26 (.step 9 (.close 52)))) (.step 15 (.step 10 (.close 16)))) (.step 18 (.step 70 (.step 13 (.close 18)))))) (.split 30 0 (.split 23 0 (.split 42 0 (.step 70 (.step 13 (.step 18 (.close 9)))) (.step 70 (.close 4))) (.step 18 (.step 40 (.step 13 (.close 18))))) (.step 13 (.step 33 (.step 45 (.step 18 (.close 39))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1532495540865888858358348294800909411848140619960549376, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563747287067751168005578449327043768255546633183691800576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 52 (.close 9))) (.step 15 (.step 10 (.close 16)))) (.step 18 (.split 35 0 (.step 18 (.step 53 (.step 10 (.step 13 (.step 16 (.close 18)))))) (.step 18 (.close 9))))) (.step 18 (.split 34 0 (.split 35 0 (.step 18 (.step 9 (.step 21 (.close 22)))) (.step 9 (.step 18 (.close 21)))) (.step 15 (.step 10 (.close 16)))))) (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 56 0 (.step 70 (.step 18 (.step 10 (.close 13)))) (.step 4 (.step 13 (.step 16 (.step 10 (.close 18)))))) (.step 4 (.step 18 (.step 9 (.close 15))))) (.step 13 (.step 4 (.step 13 (.step 4 (.step 9 (.close 18))))))) (.step 4 (.step 18 (.step 10 (.close 16))))) (.step 4 (.step 18 (.step 9 (.close 15)))))) (.split 22 0 (.step 18 (.split 34 0 (.split 35 0 (.split 36 0 (.step 18 (.split 38 0 (.step 18 (.step 54 (.step 9 (.close 21)))) (.step 10 (.step 18 (.close 21))))) (.step 18 (.close 21))) (.step 9 (.step 18 (.close 21)))) (.step 18 (.close 15)))) (.step 18 (.close 39)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794850166689900312469729358760858615808000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 18 (.step 54 (.step 13 (.close 5)))) (.split 19 0 (.step 54 (.close 4)) (.step 18 (.step 13 (.close 4))))) (.step 18 (.step 13 (.step 33 (.step 4 (.step 9 (.close 38))))))) (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.step 40 (.step 18 (.close 9))) (.step 40 (.step 13 (.step 15 (.step 5 (.close 16)))))) (.step 40 (.close 13))) (.step 40 (.step 39 (.step 4 (.step 5 (.step 10 (.close 16))))))) (.step 68 (.step 4 (.close 15))))) (.split 35 0 (.split 19 0 (.step 33 (.split 34 0 (.split 36 0 (.split 38 0 (.step 13 (.step 18 (.close 10))) (.step 18 (.step 13 (.step 5 (.step 10 (.close 33)))))) (.step 13 (.step 33 (.step 18 (.close 39))))) (.step 13 (.step 33 (.step 39 (.step 16 (.close 9))))))) (.split 38 0 (.split 36 0 (.step 18 (.step 13 (.step 4 (.step 18 (.step 15 (.close 10)))))) (.step 39 (.close 18))) (.step 4 (.step 18 (.step 10 (.close 16)))))) (.split 38 0 (.split 18 0 (.step 33 (.close 18)) (.step 4 (.step 18 (.step 9 (.close 15))))) (.step 4 (.step 5 (.step 13 (.step 4 (.step 5 (.close 33))))))))) (.split 35 0 (.split 18 0 (.split 34 0 (.split 23 0 (.step 13 (.step 23 (.step 24 (.close 20)))) (.step 23 (.step 18 (.step 13 (.close 18))))) (.step 13 (.step 23 (.step 15 (.close 17))))) (.step 23 (.step 18 (.step 13 (.close 18))))) (.step 23 (.step 13 (.step 24 (.close 4)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969808844451457866832301362564362397754450428407074563043872770648702976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 18 (.split 54 0 (.step 18 (.step 64 (.step 5 (.close 10)))) (.step 18 (.close 9)))) (.split 38 0 (.step 54 (.step 18 (.step 13 (.close 18)))) (.step 18 (.step 13 (.step 5 (.step 10 (.close 39))))))) (.step 18 (.step 13 (.step 33 (.step 4 (.step 9 (.close 38))))))) (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.step 40 (.step 18 (.close 9))) (.step 40 (.step 13 (.step 15 (.step 5 (.close 16)))))) (.step 40 (.close 13))) (.step 40 (.step 43 (.step 16 (.close 4))))) (.step 68 (.step 4 (.close 15))))) (.split 35 0 (.split 19 0 (.step 33 (.split 34 0 (.step 65 (.step 13 (.step 18 (.step 33 (.step 18 (.close 9)))))) (.step 13 (.step 33 (.step 38 (.step 16 (.close 39))))))) (.split 38 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 59 0 (.split 61 0 (.step 33 (.step 18 (.step 15 (.step 16 (.close 39))))) (.step 13 (.step 4 (.step 10 (.step 16 (.close 18)))))) (.step 4 (.step 13 (.step 4 (.step 15 (.step 9 (.close 18))))))) (.step 4 (.step 16 (.step 10 (.close 18))))) (.step 4 (.step 18 (.step 9 (.close 15))))) (.step 13 (.step 4 (.step 9 (.step 13 (.step 15 (.close 18))))))) (.step 4 (.step 18 (.step 10 (.close 16)))))) (.split 38 0 (.step 53 (.step 4 (.step 15 (.close 18)))) (.step 4 (.step 5 (.step 13 (.step 4 (.step 5 (.close 33))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432181069608103997302445641780514548350976⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 35 0 (.split 18 0 (.split 34 0 (.split 23 0 (.step 13 (.step 23 (.step 24 (.close 20)))) (.step 23 (.step 18 (.step 13 (.close 18))))) (.step 13 (.step 23 (.step 15 (.close 17))))) (.step 23 (.step 18 (.step 13 (.close 18))))) (.step 23 (.step 13 (.step 24 (.close 4))))))) (.run (.split 35 0 (.split 38 0 (.split 49 0 (.split 18 0 (.split 22 0 (.step 13 (.step 23 (.step 24 (.step 54 (.step 14 (.close 23)))))) (.split 30 0 (.step 23 (.step 13 (.step 24 (.step 20 (.close 14))))) (.step 13 (.step 33 (.step 20 (.step 23 (.step 9 (.close 15)))))))) (.step 23 (.step 18 (.step 13 (.step 18 (.close 19)))))) (.step 24 (.step 53 (.step 13 (.step 4 (.step 9 (.step 13 (.close 18)))))))) (.split 18 0 (.step 33 (.step 23 (.step 4 (.close 18)))) (.step 18 (.step 14 (.close 19))))) (.split 38 0 (.split 18 0 (.step 33 (.step 23 (.step 13 (.step 17 (.step 19 (.step 9 (.close 20))))))) (.step 18 (.step 17 (.close 19)))) (.step 18 (.step 14 (.step 19 (.step 4 (.step 5 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1361129468951404454081727831224849793024, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433542199075787751156299140210241621196800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.split 36 0 (.step 16 (.step 9 (.step 10 (.close 52)))) (.step 13 (.step 18 (.step 10 (.close 13)))))) (.step 16 (.step 13 (.close 15)))) (.step 13 (.step 18 (.split 34 0 (.step 13 (.step 10 (.step 15 (.close 18)))) (.step 13 (.close 15)))))) (.step 18 (.step 15 (.step 10 (.step 13 (.close 16)))))) (.step 13 (.step 18 (.split 34 0 (.step 13 (.step 5 (.close 18))) (.step 13 (.close 4)))))) (.split 22 0 (.step 18 (.step 15 (.step 10 (.close 16)))) (.step 4 (.step 18 (.close 13))))) (.split 19 0 (.split 22 0 (.step 18 (.step 15 (.step 10 (.close 16)))) (.step 4 (.step 18 (.close 13)))) (.split 23 0 (.step 18 (.step 10 (.step 15 (.close 16)))) (.step 10 (.step 22 (.step 15 (.close 13))))))) (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.step 18 (.step 13 (.close 5)))) (.step 18 (.close 13))) (.step 5 (.step 13 (.step 4 (.step 10 (.close 16)))))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 18 (.close 13))))) (.split 17 0 (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.step 18 (.step 13 (.close 5)))) (.step 18 (.close 13))) (.step 5 (.step 13 (.step 4 (.step 10 (.close 16)))))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 18 (.close 13)))) (.split 18 0 (.step 13 (.close 18)) (.step 18 (.close 13))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1329229263435516101133208558057291776, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794851495917896097385602262567918896152576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.split 42 0 (.step 15 (.step 10 (.step 9 (.close 52)))) (.step 13 (.step 18 (.step 9 (.close 13)))))) (.step 15 (.step 13 (.close 16)))) (.step 13 (.step 18 (.split 34 0 (.step 13 (.step 9 (.step 15 (.step 16 (.close 18))))) (.step 13 (.close 15)))))) (.step 18 (.step 15 (.step 10 (.step 13 (.close 16)))))) (.step 13 (.step 18 (.split 34 0 (.step 13 (.step 4 (.close 18))) (.step 13 (.close 4)))))) (.split 22 0 (.step 18 (.step 15 (.step 10 (.close 16)))) (.step 4 (.step 18 (.close 13))))) (.split 19 0 (.split 22 0 (.step 18 (.step 15 (.step 10 (.close 16)))) (.step 4 (.step 18 (.close 13)))) (.split 23 0 (.step 18 (.step 9 (.step 15 (.close 16)))) (.step 9 (.step 22 (.step 15 (.step 4 (.close 13)))))))) (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 13 (.step 18 (.close 13))) (.step 4 (.step 13 (.close 4)))) (.step 13 (.step 4 (.step 9 (.close 18))))) (.step 13 (.close 4))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 13 (.step 4 (.step 9 (.close 15)))))) (.step 4 (.step 18 (.close 13))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def references : Fin 6 → Box := ![Part18.root, Part19.root, Part20.root, Part22.root, Part23.root, Part24.root]
def proof : Chunks.Proof 6 := (.split 12 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 22 (.step 9 (.close 52)))) (.step 15 (.step 10 (.close 16)))) (.step 18 (.step 54 (.step 13 (.close 18))))) (.step 18 (.split 34 0 (.split 35 0 (.step 18 (.step 9 (.step 22 (.close 26)))) (.step 9 (.step 18 (.close 22)))) (.step 15 (.step 10 (.close 16)))))) (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 56 0 (.step 54 (.step 18 (.step 10 (.close 13)))) (.step 4 (.step 13 (.step 16 (.step 10 (.close 18)))))) (.step 4 (.step 18 (.step 9 (.close 15))))) (.step 13 (.step 4 (.step 13 (.step 4 (.step 9 (.close 18))))))) (.step 4 (.step 18 (.step 10 (.close 16))))) (.step 4 (.step 18 (.step 9 (.close 15)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.split 13 0 (.split 16 0 (.reuse 5) (.run (.split 17 0 (.split 18 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 13 (.step 18 (.close 13))) (.step 4 (.step 13 (.close 4)))) (.step 13 (.step 4 (.step 9 (.close 18))))) (.step 13 (.close 4))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 13 (.step 4 (.step 9 (.close 15)))))) (.step 4 (.step 18 (.close 13)))) (.split 18 0 (.step 13 (.close 18)) (.step 18 (.close 13)))))) (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.step 13 (.step 15 (.step 10 (.close 13)))) (.step 4 (.step 15 (.close 10)))) (.step 4 (.step 15 (.step 10 (.step 15 (.close 16)))))) (.step 4 (.step 5 (.close 13)))) (.split 17 0 (.step 4 (.step 5 (.close 13))) (.step 13 (.close 4)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part22.excludes
  · exact Part23.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def references : Fin 5 → Box := ![Part7.root, Part10.root, Part11.root, Part17.root, Part25.root]
def proof : Chunks.Proof 5 := (.split 10 0 (.split 12 0 (.split 13 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.step 18 (.step 54 (.step 5 (.close 10)))) (.step 52 (.step 37 (.step 4 (.close 5))))) (.step 13 (.step 18 (.split 35 0 (.step 18 (.step 40 (.step 5 (.close 18)))) (.step 4 (.close 5)))))) (.step 18 (.step 22 (.step 5 (.step 4 (.close 10)))))) (.step 13 (.split 23 0 (.step 23 (.step 18 (.split 34 0 (.step 18 (.step 23 (.step 5 (.step 10 (.close 18))))) (.step 23 (.step 5 (.close 16)))))) (.step 4 (.step 18 (.close 20)))))) (.split 22 0 (.step 18 (.step 22 (.close 10))) (.step 18 (.close 20)))) (.split 19 0 (.split 22 0 (.step 18 (.step 22 (.step 21 (.step 4 (.close 5))))) (.step 18 (.close 20))) (.step 22 (.close 4)))))) (.reuse 2))) (.reuse 3)) (.reuse 4))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part17.excludes
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part26

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part26.excludes
end FiveColour.Packed.EnumerationChunks.Case39
