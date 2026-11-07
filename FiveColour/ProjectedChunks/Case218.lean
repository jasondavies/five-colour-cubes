module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case218
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941794206991798234622625843120460821168128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 36 0 (.step 29 (.split 38 0 (.step 55 (.step 53 (.close 13))) (.step 38 (.close 55)))) (.step 57 (.close 68))) (.split 42 0 (.split 35 0 (.split 63 0 (.step 38 (.step 5 (.close 54))) (.step 27 (.step 38 (.step 5 (.close 54))))) (.step 29 (.close 38))) (.step 38 (.step 5 (.step 9 (.close 43)))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 9 (.step 15 (.close 43)))) (.step 15 (.step 43 (.step 3 (.close 9))))) (.step 43 (.step 15 (.step 9 (.close 39))))) (.step 29 (.step 38 (.step 15 (.step 43 (.close 39))))))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.close 68))) (.step 38 (.close 19))) (.step 38 (.step 43 (.step 9 (.close 39))))) (.step 38 (.step 43 (.step 15 (.step 9 (.close 57))))))) (.split 34 0 (.split 30 0 (.split 35 0 (.step 43 (.step 11 (.close 62))) (.step 75 (.close 43))) (.split 35 0 (.split 36 0 (.step 42 (.close 68)) (.step 43 (.step 20 (.close 24)))) (.step 42 (.close 3)))) (.step 75 (.split 35 0 (.step 43 (.step 5 (.close 24))) (.step 43 (.close 3)))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205969698150575188156815938267791677718528⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 61))) (.split 36 0 (.step 42 (.close 68)) (.step 38 (.close 43)))) (.step 43 (.close 39))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 68)) (.step 43 (.step 5 (.close 24)))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.close 24))) (.step 33 (.close 39))) (.step 33 (.close 20))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.close 20)))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 43 (.close 74))))) (.step 24 (.step 33 (.split 34 0 (.step 61 (.step 33 (.close 20))) (.step 24 (.close 20))))))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.close 42)))) (.step 38 (.close 24))) (.step 38 (.step 43 (.close 3)))) (.split 39 0 (.step 38 (.close 19)) (.step 24 (.close 42)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.step 19 (.close 3))))) (.step 24 (.close 38))) (.step 24 (.step 17 (.step 38 (.step 3 (.close 25)))))) (.step 24 (.step 33 (.step 42 (.close 38)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.close 20))) (.step 24 (.close 38))) (.step 24 (.step 17 (.step 38 (.step 3 (.close 20)))))) (.step 24 (.step 33 (.step 42 (.close 38))))) (.step 24 (.step 19 (.step 20 (.close 24))))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038779335590781899962180968608235160983415291904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 52 (.step 27 (.step 5 (.close 54)))) (.step 42 (.step 9 (.step 15 (.close 61))))) (.split 35 0 (.split 43 0 (.step 57 (.step 58 (.step 15 (.close 77)))) (.step 15 (.step 9 (.step 5 (.close 11))))) (.step 38 (.step 15 (.close 43))))) (.split 35 0 (.split 36 0 (.step 52 (.close 5)) (.step 43 (.step 5 (.close 52)))) (.step 38 (.step 37 (.close 52))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.step 24 (.close 17))))) (.step 43 (.step 5 (.close 68)))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.close 52))) (.step 37 (.close 11))) (.step 38 (.close 9))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.step 17 (.close 24))))) (.step 24 (.step 17 (.close 43)))) (.step 24 (.step 4 (.step 17 (.step 38 (.close 24)))))) (.step 24 (.step 17 (.close 37)))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 68)) (.step 5 (.step 20 (.close 24)))) (.step 3 (.close 42))) (.step 5 (.step 17 (.close 24))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205971027378570973072688842074851958063104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.split 38 0 (.split 42 0 (.step 55 (.step 17 (.close 57))) (.step 15 (.step 43 (.close 53)))) (.step 15 (.step 38 (.step 5 (.close 3))))) (.step 38 (.step 53 (.close 68))))) (.step 62 (.step 43 (.step 15 (.step 4 (.close 24)))))) (.step 57 (.step 9 (.step 15 (.step 13 (.close 24)))))) (.split 22 0 (.split 30 0 (.step 29 (.step 38 (.step 15 (.step 53 (.close 57))))) (.step 38 (.close 9))) (.step 68 (.step 38 (.step 23 (.close 62)))))) (.split 35 0 (.split 22 0 (.step 15 (.step 43 (.close 15))) (.step 43 (.close 37))) (.step 29 (.step 15 (.close 37))))) (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 43 (.step 17 (.step 24 (.close 15)))) (.step 18 (.close 43))) (.step 68 (.step 38 (.close 74)))) (.step 15 (.step 18 (.close 43)))) (.step 24 (.step 4 (.step 17 (.close 24))))) (.step 24 (.step 4 (.step 29 (.step 15 (.close 43))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 17 0 (.split 35 0 (.step 9 (.step 17 (.close 24))) (.step 38 (.close 9))) (.step 17 (.close 24))) (.step 24 (.step 9 (.step 17 (.step 24 (.close 38)))))) (.step 18 (.close 68))) (.step 38 (.step 24 (.close 43)))) (.step 38 (.step 43 (.close 37)))) (.step 24 (.close 38)))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602286734919418671234115374552186880⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 68 (.close 74))) (.step 24 (.step 4 (.step 17 (.step 38 (.close 24)))))) (.step 24 (.step 17 (.close 37)))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 67 (.step 13 (.close 24)))) (.step 3 (.close 42))) (.step 5 (.step 17 (.close 24)))))) (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 74 (.close 43)))) (.step 13 (.step 20 (.step 11 (.close 33))))))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 68 (.close 67))) (.step 24 (.close 38))) (.step 24 (.step 17 (.close 37)))) (.step 24 (.step 42 (.close 33)))) (.step 24 (.split 30 0 (.step 17 (.step 19 (.close 24))) (.step 13 (.step 19 (.close 42)))))) (.split 22 0 (.step 24 (.split 30 0 (.step 17 (.step 19 (.close 20))) (.step 19 (.close 67)))) (.step 19 (.step 20 (.step 13 (.close 24))))))))) (.split 14 0 (.reuse 2) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 34 0 (.split 35 0 (.split 42 0 (.step 52 (.step 5 (.close 68))) (.step 15 (.close 5))) (.step 15 (.close 17))) (.step 15 (.step 29 (.close 66))))) (.step 24 (.step 15 (.step 17 (.step 4 (.close 24)))))) (.step 24 (.step 15 (.step 17 (.step 4 (.close 24)))))) (.split 17 0 (.step 24 (.step 15 (.step 17 (.step 4 (.close 24))))) (.step 13 (.close 17)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941794206993065885222854072521957524373504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 43 (.close 57))) (.step 43 (.step 11 (.step 19 (.close 52))))) (.split 36 0 (.split 39 0 (.step 29 (.step 52 (.step 3 (.close 19)))) (.step 38 (.close 24))) (.step 38 (.step 29 (.step 3 (.close 68)))))) (.step 15 (.split 35 0 (.step 43 (.close 15)) (.step 15 (.close 33))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.close 24))) (.step 42 (.close 33))) (.split 39 0 (.split 38 0 (.step 43 (.step 13 (.close 39))) (.step 18 (.close 33))) (.step 33 (.close 24)))) (.split 36 0 (.split 38 0 (.step 42 (.close 33)) (.step 3 (.close 18))) (.step 33 (.close 24)))) (.step 15 (.split 35 0 (.step 33 (.step 13 (.step 15 (.close 17)))) (.step 15 (.close 33)))))) (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.close 13))) (.step 43 (.step 20 (.close 24)))) (.step 75 (.step 42 (.step 43 (.close 3))))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.close 68)) (.step 5 (.close 42))) (.step 24 (.close 42))) (.step 33 (.close 43))) (.step 33 (.close 24)))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.close 15))) (.step 13 (.step 33 (.close 15)))) (.step 17 (.step 33 (.close 15)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205969698151842838757044167669288380923904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.close 19)) (.step 43 (.step 5 (.close 24)))) (.split 39 0 (.step 38 (.close 13)) (.step 3 (.close 42)))) (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.close 38))) (.step 33 (.close 38))) (.step 33 (.close 19)))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.close 15))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.close 38)))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.close 43)))) (.step 19 (.close 24))) (.step 17 (.close 14))))) (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 42 (.close 20)))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.close 24))) (.step 17 (.close 14)))) (.step 19 (.step 20 (.step 13 (.close 24)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599766273060006785103026559709810975047680⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.close 61)) (.step 43 (.step 5 (.close 24)))) (.split 39 0 (.step 43 (.close 3)) (.step 3 (.close 42)))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.close 68)) (.step 5 (.close 42))) (.step 24 (.close 42))) (.step 13 (.step 33 (.close 39)))) (.step 33 (.close 20)))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.close 15))) (.step 13 (.step 33 (.close 15)))) (.step 17 (.step 33 (.close 15))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 24 (.close 20)))) (.step 17 (.close 14))))))) (.reuse 1)) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.split 34 0 (.split 43 0 (.step 66 (.close 43)) (.step 15 (.close 11))) (.step 15 (.close 37))) (.split 35 0 (.split 49 0 (.step 13 (.close 15)) (.step 15 (.close 52))) (.step 3 (.step 15 (.close 13)))))) (.step 24 (.split 30 0 (.step 17 (.step 66 (.step 13 (.close 15)))) (.step 13 (.close 17))))) (.split 22 0 (.step 24 (.split 30 0 (.step 17 (.step 61 (.step 13 (.close 15)))) (.step 13 (.close 17)))) (.step 13 (.close 17)))) (.split 17 0 (.split 22 0 (.step 24 (.split 30 0 (.step 17 (.step 42 (.step 13 (.close 15)))) (.step 13 (.close 17)))) (.step 13 (.close 17))) (.step 13 (.close 17))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def references : Fin 2 → Box := ![Part4.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 22 0 (.step 15 (.split 36 0 (.step 52 (.step 9 (.step 3 (.close 17)))) (.step 15 (.close 17)))) (.step 24 (.close 13))) (.step 15 (.step 18 (.step 15 (.close 17))))) (.step 24 (.step 39 (.step 4 (.close 13))))) (.split 17 0 (.step 24 (.step 38 (.close 15))) (.step 13 (.close 17)))) (.split 16 0 (.step 15 (.close 13)) (.step 13 (.close 15)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case218
