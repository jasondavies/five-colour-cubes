module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case227
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
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
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124562214791526885279147220101032242858843698492564804993024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 36 0 (.split 54 0 (.step 18 (.close 10)) (.step 54 (.close 71))) (.split 35 0 (.step 18 (.close 54)) (.step 18 (.close 39)))) (.split 36 0 (.step 18 (.step 54 (.close 58))) (.step 54 (.step 18 (.close 33))))) (.split 34 0 (.split 36 0 (.step 26 (.close 58)) (.step 18 (.step 22 (.step 9 (.close 18))))) (.step 18 (.split 35 0 (.step 70 (.step 16 (.step 10 (.close 71)))) (.step 15 (.step 18 (.step 16 (.close 26)))))))) (.split 23 0 (.step 70 (.split 30 0 (.step 18 (.close 39)) (.step 33 (.close 18)))) (.step 18 (.step 26 (.step 18 (.close 39)))))) (.split 22 0 (.split 34 0 (.split 35 0 (.step 22 (.step 54 (.step 9 (.close 18)))) (.step 18 (.step 21 (.step 22 (.close 18))))) (.split 35 0 (.step 18 (.step 22 (.split 36 0 (.step 15 (.step 16 (.close 18))) (.step 18 (.close 22))))) (.step 15 (.step 29 (.step 21 (.step 22 (.close 18))))))) (.step 26 (.step 18 (.step 54 (.close 4)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794850166688632661869501129359361912602624⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 56 0 (.step 9 (.step 21 (.close 18))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.close 21))) (.step 18 (.step 21 (.step 18 (.step 9 (.close 21)))))) (.split 35 0 (.step 18 (.split 36 0 (.step 21 (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 15 (.step 16 (.close 21)))))) (.step 15 (.step 29 (.step 21 (.close 18)))))) (.step 26 (.step 18 (.step 55 (.step 4 (.close 13)))))) (.split 35 0 (.split 38 0 (.split 34 0 (.step 54 (.split 42 0 (.step 54 (.step 10 (.step 18 (.close 21)))) (.step 18 (.step 21 (.step 9 (.close 18)))))) (.step 18 (.step 21 (.step 22 (.close 18))))) (.step 10 (.step 21 (.close 18)))) (.step 22 (.close 21)))))) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 54 (.split 30 0 (.step 18 (.close 45)) (.step 33 (.close 18)))) (.step 18 (.step 54 (.close 4)))) (.split 23 0 (.step 54 (.step 70 (.split 35 0 (.step 54 (.step 18 (.close 14))) (.step 18 (.close 68))))) (.step 23 (.step 18 (.close 20))))) (.split 22 0 (.step 22 (.step 18 (.close 54))) (.step 18 (.step 23 (.step 18 (.close 20)))))) (.split 22 0 (.step 22 (.step 18 (.step 54 (.step 4 (.close 10))))) (.step 18 (.step 23 (.step 18 (.close 20))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432181069606836346702217412379017845145600⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 36 0 (.step 18 (.step 54 (.close 58))) (.step 54 (.step 18 (.close 38)))) (.step 53 (.close 41))) (.step 18 (.step 55 (.step 4 (.close 13))))) (.split 23 0 (.step 70 (.split 35 0 (.step 70 (.step 24 (.close 65))) (.step 24 (.step 18 (.close 38))))) (.step 23 (.step 18 (.close 20))))) (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.close 4))) (.step 21 (.step 18 (.close 4)))) (.step 18 (.step 23 (.step 18 (.close 20)))))) (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 55 (.step 4 (.close 13)))) (.step 18 (.close 21))) (.step 18 (.step 23 (.step 18 (.close 20))))) (.step 18 (.close 21)))) (.split 35 0 (.split 18 0 (.split 19 0 (.split 36 0 (.split 43 0 (.split 49 0 (.split 22 0 (.step 18 (.close 40)) (.step 23 (.close 19))) (.step 13 (.step 24 (.close 18)))) (.step 54 (.split 38 0 (.split 49 0 (.step 23 (.close 4)) (.step 13 (.step 24 (.close 4)))) (.step 23 (.close 5))))) (.step 54 (.close 4))) (.step 24 (.step 18 (.close 20)))) (.split 49 0 (.step 24 (.step 18 (.close 10))) (.step 18 (.close 23)))) (.split 18 0 (.split 19 0 (.step 24 (.step 33 (.step 18 (.close 38)))) (.step 18 (.close 20))) (.step 18 (.close 19)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427796211296156316415723354627789088985448448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.close 71)) (.split 42 0 (.step 18 (.step 10 (.close 21))) (.step 18 (.close 45)))) (.step 52 (.close 16))) (.step 18 (.step 65 (.step 16 (.step 10 (.close 18)))))) (.split 34 0 (.split 30 0 (.split 42 0 (.split 36 0 (.step 10 (.step 15 (.step 16 (.close 26)))) (.step 22 (.step 15 (.step 16 (.close 18))))) (.step 26 (.close 10))) (.step 18 (.step 9 (.close 26)))) (.step 16 (.close 18)))) (.split 23 0 (.step 18 (.step 70 (.split 30 0 (.step 16 (.close 55)) (.step 13 (.step 18 (.close 33)))))) (.step 26 (.close 18)))) (.split 23 0 (.split 34 0 (.split 35 0 (.step 54 (.step 72 (.split 22 0 (.step 22 (.step 9 (.close 18))) (.step 5 (.close 18))))) (.step 15 (.step 21 (.step 18 (.close 16))))) (.step 16 (.close 18))) (.step 22 (.step 26 (.close 18))))) (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 65 (.step 4 (.step 15 (.close 76)))) (.step 18 (.step 22 (.step 15 (.step 16 (.close 18)))))) (.step 15 (.step 18 (.close 21)))) (.step 16 (.close 18))) (.step 10 (.step 21 (.step 18 (.step 16 (.close 18)))))) (.step 22 (.step 21 (.step 10 (.close 18)))))) (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.step 5 (.close 37)))) (.step 18 (.step 22 (.step 4 (.close 5))))) (.step 13 (.step 23 (.step 18 (.step 23 (.close 5)))))) (.step 18 (.close 22))) (.step 22 (.step 5 (.close 18))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794851495916628446785374033166422192947200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 35 0 (.step 64 (.step 58 (.close 9))) (.split 36 0 (.step 64 (.step 53 (.close 18))) (.step 57 (.step 15 (.close 18))))) (.step 18 (.step 53 (.step 15 (.step 9 (.close 18)))))) (.split 34 0 (.split 30 0 (.step 26 (.step 9 (.close 57))) (.step 18 (.step 9 (.close 26)))) (.step 15 (.close 18)))) (.split 23 0 (.step 18 (.step 62 (.step 13 (.close 43)))) (.step 18 (.close 26)))) (.split 23 0 (.split 34 0 (.split 35 0 (.step 54 (.split 42 0 (.step 54 (.step 4 (.step 9 (.close 58)))) (.step 18 (.step 16 (.step 10 (.close 71)))))) (.step 9 (.step 15 (.step 18 (.step 21 (.close 22)))))) (.step 15 (.close 18))) (.step 9 (.step 22 (.step 15 (.close 26)))))) (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 38 0 (.split 36 0 (.step 53 (.step 4 (.step 9 (.close 76)))) (.step 18 (.step 9 (.close 21)))) (.step 16 (.step 18 (.close 21)))) (.step 9 (.step 18 (.close 21)))) (.step 15 (.close 18))) (.step 9 (.step 21 (.step 18 (.step 15 (.close 18)))))) (.step 22 (.step 9 (.step 21 (.close 18)))))) (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.split 30 0 (.step 15 (.close 68)) (.step 13 (.step 18 (.close 33)))))) (.step 18 (.step 22 (.step 9 (.close 18))))) (.step 13 (.step 24 (.step 18 (.step 24 (.close 4)))))) (.step 22 (.close 18))) (.step 18 (.step 22 (.step 9 (.step 15 (.close 18))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528302515885471943814615805198336000⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 53 (.step 4 (.close 37)))) (.step 21 (.step 4 (.close 18)))) (.step 13 (.step 24 (.step 18 (.step 24 (.close 4)))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 18 (.step 21 (.close 18)))) (.split 38 0 (.split 49 0 (.split 34 0 (.step 18 (.step 24 (.close 4))) (.step 24 (.close 15))) (.step 13 (.close 18))) (.step 4 (.step 5 (.close 24))))))) (.run (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 17 0 (.step 52 (.split 38 0 (.step 13 (.close 9)) (.step 13 (.close 15)))) (.step 13 (.close 4))) (.step 13 (.step 16 (.close 9)))) (.step 13 (.step 15 (.close 13)))) (.split 35 0 (.step 13 (.step 52 (.close 15))) (.step 15 (.close 13)))) (.step 26 (.step 15 (.close 13)))) (.step 22 (.step 15 (.close 13)))) (.split 23 0 (.split 34 0 (.split 35 0 (.split 19 0 (.split 36 0 (.split 38 0 (.split 56 0 (.step 4 (.close 15)) (.step 13 (.close 15))) (.step 13 (.close 16))) (.step 15 (.close 13))) (.step 16 (.close 13))) (.step 15 (.close 4))) (.step 15 (.step 4 (.close 16)))) (.step 21 (.step 15 (.close 13))))) (.split 17 0 (.split 34 0 (.step 21 (.step 13 (.close 4))) (.step 13 (.step 21 (.close 15)))) (.step 13 (.step 18 (.close 4)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748783645427794850166689900312469729358760858615808000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 36 0 (.step 52 (.step 18 (.close 10))) (.step 54 (.step 18 (.close 13)))) (.split 36 0 (.split 54 0 (.step 13 (.step 18 (.close 10))) (.step 18 (.close 33))) (.step 33 (.step 13 (.close 18))))) (.step 18 (.step 70 (.close 18)))) (.split 23 0 (.step 70 (.split 35 0 (.step 13 (.step 40 (.close 43))) (.step 18 (.step 13 (.close 68))))) (.step 18 (.step 13 (.close 40))))) (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.close 18))) (.step 18 (.step 22 (.step 9 (.close 18))))) (.step 18 (.step 13 (.close 40))))) (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.step 18 (.close 52)) (.step 18 (.close 39))) (.step 18 (.step 26 (.step 10 (.close 18))))) (.step 18 (.step 13 (.close 40)))) (.step 18 (.step 22 (.step 18 (.close 21)))))) (.split 35 0 (.split 38 0 (.split 19 0 (.split 36 0 (.split 43 0 (.split 49 0 (.split 50 0 (.step 23 (.step 18 (.close 13))) (.step 18 (.step 13 (.close 43)))) (.step 13 (.close 4))) (.step 54 (.split 22 0 (.step 18 (.step 13 (.close 5))) (.step 13 (.close 23))))) (.step 54 (.close 4))) (.split 22 0 (.step 18 (.step 13 (.close 40))) (.step 13 (.close 23)))) (.split 49 0 (.split 56 0 (.step 33 (.step 18 (.close 40))) (.step 5 (.step 16 (.step 10 (.close 59))))) (.step 18 (.close 13)))) (.split 38 0 (.split 49 0 (.step 33 (.step 40 (.step 39 (.step 4 (.close 43))))) (.step 18 (.close 13))) (.step 5 (.close 33))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929432181069608103997302445641780514548350976⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 35 0 (.split 38 0 (.split 17 0 (.split 22 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 56 0 (.step 40 (.close 18)) (.step 18 (.close 40))) (.step 18 (.close 43))) (.step 33 (.step 18 (.close 15)))) (.step 13 (.step 43 (.close 18)))) (.step 13 (.step 23 (.close 24)))) (.split 22 0 (.step 13 (.step 23 (.close 24))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.step 70 (.step 13 (.close 18))) (.step 18 (.close 54))) (.step 23 (.close 24))) (.step 23 (.close 20))) (.step 23 (.close 17))))) (.split 49 0 (.split 50 0 (.split 56 0 (.step 33 (.split 18 0 (.step 23 (.close 55)) (.step 4 (.step 16 (.close 18))))) (.step 5 (.step 40 (.step 23 (.close 41))))) (.step 18 (.close 33))) (.step 18 (.close 13)))) (.split 38 0 (.split 49 0 (.step 33 (.split 18 0 (.step 24 (.step 18 (.close 38))) (.step 4 (.step 15 (.step 9 (.close 18)))))) (.step 18 (.close 13))) (.step 4 (.close 33))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 13 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.split 30 0 (.step 16 (.close 9)) (.step 13 (.close 15)))) (.step 15 (.close 13))) (.step 18 (.step 13 (.close 5)))) (.step 18 (.step 15 (.close 16)))) (.step 18 (.step 15 (.close 16)))) (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.step 18 (.close 13))) (.step 18 (.close 13))) (.step 5 (.step 13 (.close 16)))) (.step 5 (.close 13)))) (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.split 18 0 (.step 13 (.step 18 (.close 13))) (.step 4 (.step 13 (.close 16))))) (.step 18 (.close 13))) (.step 18 (.close 13))) (.step 5 (.close 13)))))) (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.split 30 0 (.step 15 (.close 10)) (.step 13 (.close 15)))) (.step 15 (.close 16))) (.step 18 (.step 13 (.close 4)))) (.step 18 (.step 15 (.close 16)))) (.step 18 (.step 15 (.close 16)))) (.split 35 0 (.split 49 0 (.split 50 0 (.step 24 (.step 18 (.close 13))) (.step 13 (.close 18))) (.step 13 (.close 4))) (.step 4 (.step 13 (.close 15))))) (.split 35 0 (.split 49 0 (.split 50 0 (.split 17 0 (.step 24 (.step 18 (.close 13))) (.step 13 (.close 4))) (.step 13 (.step 18 (.close 9)))) (.step 13 (.close 4))) (.step 18 (.close 13)))) (.split 18 0 (.step 13 (.step 15 (.close 13))) (.step 4 (.close 15))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712646587177969810529448124563748785106929433543528303783536072172044017301901541376⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part5.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 12 0 (.split 13 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 65 (.step 5 (.close 37)))) (.step 21 (.step 5 (.close 18)))) (.step 13 (.step 23 (.step 18 (.step 23 (.close 5)))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 18 (.step 21 (.close 18)))) (.split 38 0 (.split 34 0 (.step 18 (.step 13 (.step 23 (.close 5)))) (.step 23 (.close 18))) (.step 18 (.close 40))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case227
