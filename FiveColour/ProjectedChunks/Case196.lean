module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case196
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194517791657437357148209152⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨22571190701410838661927, 5789234131004114107584442999818874427577774909498797390504919862074892603295797621317816810655560770433460615551866939002223572355585261041158888636944247803843661476316050640461904472537551981314742120166598634117502337025, 0⟩]
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
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646069297235169759000508779685478634881024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 25 0 (.step 52 (.step 18 (.step 13 (.close 15)))) (.step 28 (.close 16))) (.split 25 0 (.split 26 0 (.step 70 (.step 16 (.close 18))) (.step 10 (.step 15 (.step 7 (.step 16 (.close 7)))))) (.step 10 (.step 16 (.step 7 (.step 15 (.close 28))))))) (.split 23 0 (.step 18 (.close 40)) (.step 18 (.close 26)))) (.split 25 0 (.split 26 0 (.split 34 0 (.step 22 (.step 9 (.close 18))) (.step 16 (.close 18))) (.step 15 (.step 22 (.close 29)))) (.step 10 (.step 16 (.step 22 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 23 0 (.split 35 0 (.step 65 (.step 9 (.close 18))) (.step 15 (.close 21))) (.step 10 (.step 21 (.close 18)))) (.step 16 (.close 18))) (.step 15 (.step 21 (.step 7 (.close 16))))) (.step 10 (.step 16 (.split 42 0 (.step 21 (.close 7)) (.step 26 (.close 28))))))) (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.close 40)) (.step 18 (.step 4 (.close 39)))) (.step 18 (.close 22))) (.step 22 (.close 18)))) (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.close 40)) (.step 18 (.step 4 (.close 45)))) (.step 21 (.close 18))) (.step 18 (.step 21 (.close 7)))) (.step 18 (.step 7 (.step 18 (.step 23 (.close 5))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646069297235169759000508779685478634881024⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 25 0 (.step 18 (.close 9)) (.step 18 (.close 28))) (.step 18 (.step 26 (.close 18)))) (.step 18 (.step 7 (.step 18 (.close 39))))) (.split 25 0 (.split 26 0 (.step 54 (.step 18 (.step 9 (.close 39)))) (.step 18 (.step 22 (.close 29)))) (.step 59 (.step 18 (.step 22 (.close 28)))))) (.split 25 0 (.split 26 0 (.split 19 0 (.split 35 0 (.split 38 0 (.step 18 (.close 9)) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 21 (.close 18))) (.split 34 0 (.step 18 (.step 9 (.step 21 (.close 7)))) (.step 15 (.step 28 (.step 9 (.step 7 (.close 16))))))) (.split 26 0 (.split 34 0 (.step 18 (.step 10 (.step 21 (.close 7)))) (.step 16 (.step 28 (.step 7 (.close 15))))) (.step 9 (.step 21 (.close 28)))))) (.split 18 0 (.split 19 0 (.step 18 (.step 7 (.step 39 (.step 18 (.close 25))))) (.step 18 (.close 22))) (.step 22 (.close 18)))) (.split 17 0 (.split 18 0 (.split 19 0 (.step 18 (.step 7 (.split 49 0 (.step 40 (.close 38)) (.step 13 (.close 43))))) (.step 18 (.step 4 (.close 39)))) (.step 18 (.close 21))) (.step 7 (.split 18 0 (.split 19 0 (.step 54 (.step 18 (.step 54 (.close 23)))) (.step 18 (.close 20))) (.step 18 (.close 19))))))) (.reuse 0))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203644709496995481790062528185062811842379776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 25 0 (.split 26 0 (.step 18 (.close 9)) (.step 29 (.close 15))) (.step 29 (.close 58))) (.split 25 0 (.split 36 0 (.step 15 (.step 9 (.close 71))) (.step 18 (.step 15 (.step 9 (.close 58))))) (.step 26 (.close 28)))) (.step 26 (.step 18 (.close 43)))) (.split 25 0 (.split 26 0 (.split 38 0 (.step 54 (.split 42 0 (.step 9 (.step 15 (.close 18))) (.step 18 (.close 26)))) (.step 18 (.step 21 (.step 15 (.close 18))))) (.step 9 (.step 15 (.step 18 (.step 22 (.close 7)))))) (.step 16 (.step 22 (.close 29))))) (.split 25 0 (.split 26 0 (.split 19 0 (.split 38 0 (.split 42 0 (.step 53 (.step 9 (.close 18))) (.step 18 (.step 9 (.step 15 (.close 18))))) (.step 18 (.close 21))) (.step 9 (.step 21 (.close 18)))) (.step 9 (.step 15 (.split 42 0 (.step 21 (.close 7)) (.step 26 (.close 28)))))) (.step 16 (.step 21 (.step 28 (.close 7)))))) (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.close 39)) (.step 18 (.step 4 (.close 39)))) (.step 18 (.close 24))) (.step 18 (.step 22 (.close 7)))) (.step 22 (.close 18)))) (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.close 38)) (.step 18 (.step 4 (.close 45)))) (.step 18 (.close 24))) (.step 21 (.close 18))) (.step 18 (.step 21 (.close 7)))) (.step 18 (.step 7 (.step 18 (.step 23 (.close 24))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194516609912894035618430976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.step 18 (.step 7 (.step 13 (.step 18 (.close 39))))) (.step 18 (.step 9 (.close 59)))) (.split 25 0 (.split 26 0 (.step 18 (.close 21)) (.step 15 (.close 18))) (.step 18 (.close 21)))) (.step 7 (.split 36 0 (.step 18 (.step 13 (.step 18 (.close 25)))) (.step 54 (.close 4))))) (.step 7 (.split 17 0 (.split 22 0 (.step 18 (.step 13 (.step 18 (.close 39)))) (.step 23 (.close 24))) (.step 13 (.step 23 (.close 24)))))) (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.close 13)) (.step 15 (.close 13))) (.step 15 (.close 13))) (.step 15 (.close 16))) (.step 7 (.step 13 (.step 18 (.close 10))))) (.step 7 (.step 13 (.step 18 (.close 10)))))) (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.close 13)) (.step 15 (.close 13))) (.step 15 (.close 16))) (.step 15 (.close 16))) (.step 7 (.step 13 (.step 18 (.close 9))))) (.step 7 (.step 13 (.step 18 (.close 9))))) (.step 13 (.step 15 (.close 13))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1180591620718485045248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646069297235169759001689371306196046184448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 7 (.split 25 0 (.step 71 (.close 9)) (.step 28 (.close 7)))) (.split 25 0 (.split 26 0 (.step 70 (.step 7 (.close 10))) (.step 9 (.close 7))) (.step 9 (.close 7)))) (.split 25 0 (.split 26 0 (.split 34 0 (.step 22 (.close 9)) (.step 7 (.step 10 (.close 7)))) (.step 9 (.close 7))) (.step 9 (.close 7)))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 23 0 (.split 35 0 (.step 10 (.close 4)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 16 (.split 35 0 (.step 7 (.close 10)) (.step 9 (.close 7))))) (.step 9 (.close 7))) (.step 9 (.close 10)))) (.step 7 (.step 22 (.split 18 0 (.step 7 (.step 5 (.close 9))) (.step 22 (.close 7)))))) (.split 18 0 (.split 19 0 (.step 7 (.step 5 (.close 9))) (.step 21 (.close 7))) (.step 21 (.close 7)))) (.split 18 0 (.split 19 0 (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 17 0 (.split 36 0 (.step 10 (.close 4)) (.step 7 (.close 9))) (.step 5 (.close 7))) (.step 7 (.close 10))) (.step 7 (.close 16))) (.step 10 (.close 7))) (.step 10 (.close 28))) (.step 10 (.close 9))) (.step 10 (.step 7 (.close 9))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194517790504514753029734400⟩
def references : Fin 4 → Box := ![Part1.root, Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 7 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 13 0 (.reuse 1) (.run (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 72 0 (.step 52 (.step 4 (.close 15))) (.step 4 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 16))) (.step 13 (.step 15 (.close 13)))) (.step 15 (.close 13))) (.split 35 0 (.split 36 0 (.step 13 (.step 15 (.close 13))) (.step 22 (.step 13 (.close 15)))) (.step 15 (.close 13)))) (.step 15 (.step 7 (.close 15)))) (.step 16 (.step 28 (.step 7 (.close 15)))))))) (.reuse 2)) (.split 10 0 (.split 12 0 (.reuse 3) (.run (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 72 0 (.step 5 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 16 (.step 7 (.close 9)))) (.step 22 (.step 7 (.close 9)))) (.step 21 (.step 9 (.close 7)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 7 (.step 9 (.close 7))) (.step 16 (.step 7 (.close 9)))) (.step 22 (.step 7 (.close 9)))) (.step 9 (.close 7)))) (.split 13 0 (.step 9 (.close 29)) (.step 15 (.close 10)))) (.step 16 (.step 9 (.step 7 (.close 10))))))) (.run (.split 12 0 (.split 13 0 (.step 7 (.split 18 0 (.split 19 0 (.step 7 (.step 9 (.close 7))) (.step 16 (.step 22 (.close 7)))) (.step 16 (.split 25 0 (.step 21 (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.split 18 0 (.step 7 (.step 16 (.close 7))) (.step 16 (.close 7)))) (.step 7 (.step 16 (.close 7)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1152921505680588800, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646069297235169759000509932606983241728000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 58 (.close 9)) (.step 28 (.close 29))) (.split 25 0 (.split 36 0 (.step 9 (.close 7)) (.step 7 (.step 9 (.close 7)))) (.step 9 (.close 7)))) (.step 7 (.close 26))) (.split 25 0 (.split 26 0 (.split 38 0 (.step 54 (.step 9 (.close 4))) (.step 7 (.step 9 (.close 7)))) (.step 9 (.close 7))) (.step 9 (.close 7)))) (.split 25 0 (.split 26 0 (.split 19 0 (.split 38 0 (.split 42 0 (.step 9 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 21))) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 9 (.close 10)))) (.split 18 0 (.split 19 0 (.step 7 (.step 5 (.close 9))) (.step 22 (.close 7))) (.step 22 (.close 7)))) (.split 18 0 (.split 19 0 (.step 7 (.step 5 (.close 9))) (.step 21 (.close 7))) (.step 21 (.close 7)))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 72 0 (.step 46 (.step 4 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 10 (.close 4))) (.step 7 (.close 10))) (.step 21 (.step 7 (.close 9)))) (.split 35 0 (.split 36 0 (.step 7 (.close 10)) (.step 22 (.step 7 (.close 9)))) (.step 15 (.step 21 (.step 28 (.close 37)))))) (.step 10 (.step 7 (.close 9)))) (.step 10 (.close 28)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1181744542223091892224, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194517791657436257636581376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 12 0 (.split 72 0 (.step 5 (.close 9)) (.step 7 (.close 9))) (.split 13 0 (.split 56 0 (.step 4 (.close 9)) (.step 7 (.close 9))) (.step 9 (.close 4)))) (.split 10 0 (.split 16 0 (.split 13 0 (.step 4 (.close 9)) (.step 5 (.close 9))) (.step 4 (.close 5))) (.step 7 (.close 9)))) (.step 26 (.step 7 (.close 9)))) (.step 21 (.step 7 (.close 9)))) (.step 22 (.step 7 (.close 9)))) (.step 21 (.step 9 (.close 7)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 10 0 (.split 13 0 (.step 7 (.close 9)) (.step 10 (.close 4))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 26 (.step 7 (.close 9)))) (.step 10 (.close 7))) (.step 22 (.step 28 (.split 49 0 (.split 50 0 (.split 59 0 (.step 10 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 15 (.step 9 (.close 7))))) (.split 10 0 (.split 13 0 (.step 9 (.close 28)) (.step 10 (.close 4))) (.step 4 (.step 9 (.close 7))))) (.split 10 0 (.split 12 0 (.step 10 (.close 28)) (.step 9 (.close 5))) (.step 5 (.step 9 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1100585369600, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194517790504515852541362176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 0 (.split 10 0 (.split 12 0 (.split 13 0 (.split 25 0 (.split 26 0 (.split 34 0 (.split 17 0 (.split 22 0 (.split 16 0 (.step 18 (.close 22)) (.step 7 (.close 4))) (.step 7 (.close 4))) (.step 7 (.close 4))) (.split 35 0 (.step 7 (.close 18)) (.step 29 (.step 18 (.close 7))))) (.step 7 (.step 18 (.close 29)))) (.step 7 (.step 18 (.close 28)))) (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.close 7)) (.step 10 (.step 18 (.close 16)))) (.step 7 (.close 4))) (.step 10 (.step 18 (.step 22 (.close 18))))) (.step 10 (.step 18 (.split 25 0 (.step 21 (.close 18)) (.step 16 (.step 18 (.close 21))))))) (.step 18 (.close 7)))) (.split 13 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.close 7)) (.step 9 (.step 18 (.close 15)))) (.step 7 (.close 4))) (.step 9 (.split 25 0 (.step 18 (.step 15 (.close 18))) (.step 18 (.close 22))))) (.step 9 (.step 18 (.split 25 0 (.split 26 0 (.step 21 (.close 18)) (.step 18 (.close 21))) (.step 18 (.close 28)))))) (.step 18 (.close 7))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 13 (.close 15)) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 16))))) (.step 7 (.step 18 (.step 7 (.close 13))))) (.split 10 0 (.split 12 0 (.split 13 0 (.step 7 (.split 18 0 (.split 19 0 (.step 7 (.close 9)) (.step 9 (.close 7))) (.step 9 (.close 7)))) (.split 26 0 (.step 10 (.close 7)) (.step 7 (.close 10)))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.close 10)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648441660649001921640455192805564874203646070626464433194517791657437357148209152⟩
def references : Fin 4 → Box := ![Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 4 0 (.split 6 0 (.reuse 0) (.split 7 0 (.split 10 0 (.split 12 0 (.reuse 1) (.run (.split 13 0 (.split 18 0 (.split 19 0 (.split 25 0 (.split 26 0 (.split 34 0 (.split 36 0 (.split 22 0 (.split 16 0 (.step 9 (.close 4)) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 15))) (.step 9 (.close 29))) (.step 9 (.close 7))) (.step 9 (.close 10))) (.step 9 (.step 7 (.close 10)))) (.step 15 (.step 10 (.close 4)))))) (.run (.split 12 0 (.step 7 (.split 13 0 (.split 18 0 (.split 19 0 (.step 7 (.step 9 (.close 7))) (.step 15 (.split 25 0 (.step 7 (.close 9)) (.step 7 (.close 9))))) (.step 15 (.split 25 0 (.split 26 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 15 (.close 7)))) (.split 18 0 (.step 7 (.step 15 (.close 7))) (.step 15 (.close 7)))))) (.reuse 2))) (.split 6 0 (.reuse 3) (.run (.split 7 0 (.split 10 0 (.split 12 0 (.step 7 (.split 13 0 (.split 18 0 (.split 19 0 (.step 7 (.close 9)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 10 (.close 7)))) (.split 13 0 (.split 25 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.split 13 0 (.step 7 (.step 9 (.close 7))) (.step 5 (.close 10)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case196
