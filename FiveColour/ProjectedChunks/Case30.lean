module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case30
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196335463521655586841957786504911440018864431493121431666867092157404200652664389845661957499105107686104440383301232523223676920462878814627510153484917940674582184881018547555020809699328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.step 71 (.split 69 1 (.split 72 1 (.split 12 0 (.split 16 0 (.step 7 (.step 9 (.step 40 (.step 7 (.close 53))))) (.step 7 (.close 4))) (.split 21 0 (.split 26 0 (.split 35 0 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.close 57))) (.step 7 (.step 9 (.close 21)))) (.step 7 (.step 15 (.step 18 (.close 29))))) (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 7 (.step 29 (.step 26 (.step 40 (.close 71)))))) (.step 71 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.close 7)) (.step 4 (.close 7))) (.step 7 (.close 4))) (.split 16 0 (.step 4 (.step 10 (.step 22 (.close 71)))) (.step 4 (.close 7)))) (.step 7 (.close 52)))))) (.step 70 (.step 71 (.split 69 1 (.step 7 (.close 70)) (.step 70 (.close 7)))))) (.split 68 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.split 17 0 (.split 36 0 (.step 65 (.close 71)) (.step 7 (.step 10 (.step 4 (.step 7 (.close 57)))))) (.step 7 (.close 54)))) (.step 7 (.close 65))) (.step 72 (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 64 (.close 71)))) (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 7 (.step 53 (.step 7 (.close 65))))) (.step 4 (.close 71))) (.step 63 (.close 71)))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742168706826074048029646094712429591419507633702611280353747000311757972567493802279239626988333839970241307824223340035469193974026904401143060747788434276352⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 54 1 (.split 59 1 (.split 61 1 (.reuse 0) (.run (.split 68 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 67 1 (.split 10 0 (.step 72 (.split 17 0 (.step 64 (.split 21 0 (.step 64 (.close 71)) (.step 4 (.close 7)))) (.step 7 (.close 54)))) (.step 7 (.close 64))) (.step 64 (.close 70))) (.step 7 (.step 30 (.close 64)))) (.step 64 (.split 10 0 (.split 16 0 (.step 4 (.close 64)) (.step 4 (.close 7))) (.step 7 (.close 52))))) (.step 4 (.step 64 (.close 71)))) (.step 63 (.close 64))))) (.run (.split 68 1 (.split 72 1 (.split 16 0 (.split 61 1 (.step 62 (.step 70 (.split 62 1 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 57))) (.step 7 (.close 62))) (.step 65 (.close 7))))) (.step 64 (.step 62 (.step 64 (.close 7))))) (.step 7 (.step 18 (.step 4 (.step 27 (.step 36 (.close 44))))))) (.step 18 (.close 26))) (.step 18 (.step 62 (.close 71)))))) (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 12 0 (.split 67 1 (.split 21 0 (.split 26 0 (.split 69 1 (.split 35 0 (.step 54 (.step 7 (.close 9))) (.step 7 (.close 57))) (.step 4 (.close 57))) (.step 18 (.close 57))) (.step 4 (.step 9 (.step 18 (.close 4))))) (.step 26 (.step 54 (.step 57 (.close 70))))) (.step 15 (.close 57))) (.step 26 (.step 29 (.close 57)))) (.step 4 (.step 29 (.close 71)))) (.step 4 (.step 21 (.step 10 (.step 57 (.close 65)))))) (.step 4 (.step 15 (.step 10 (.step 57 (.close 64)))))) (.step 57 (.close 62)))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434276803595271946858057795038993245151143890047831291497731209822335181667471539403261542233562010298803559802660766531613682854526976⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 54 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 54 (.step 7 (.close 54))) (.step 22 (.close 57))) (.step 7 (.close 54))) (.step 7 (.step 26 (.close 54)))) (.step 22 (.step 54 (.close 7)))) (.step 7 (.step 54 (.close 71)))) (.step 54 (.step 7 (.close 65)))) (.step 64 (.step 54 (.close 64))))))) (.run (.split 51 1 (.split 61 1 (.step 53 (.split 54 1 (.split 68 1 (.split 72 1 (.step 53 (.step 70 (.step 7 (.close 53)))) (.step 18 (.step 26 (.step 7 (.close 53))))) (.step 18 (.step 53 (.close 15)))) (.step 9 (.step 53 (.step 57 (.close 7)))))) (.step 52 (.step 53 (.step 64 (.step 53 (.step 70 (.step 71 (.step 9 (.step 7 (.close 53)))))))))) (.step 53 (.close 54))))) (.run (.step 52 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 54 1 (.split 72 1 (.split 69 1 (.split 12 0 (.split 16 0 (.step 52 (.step 7 (.close 9))) (.step 7 (.close 52))) (.step 52 (.close 18))) (.step 52 (.step 7 (.close 52)))) (.step 9 (.step 18 (.step 26 (.step 7 (.close 71)))))) (.step 57 (.close 7))) (.step 52 (.close 71))) (.step 52 (.close 7))) (.step 52 (.step 53 (.step 64 (.step 65 (.step 70 (.step 7 (.close 71)))))))) (.step 52 (.close 4))) (.step 52 (.close 54))))))
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

namespace Part3
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637108765072710910735548568821859825368135965499050443497691575219906088396150205624398285858767188093361455104⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 10 1 (.split 30 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 54 (.step 70 (.split 49 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.split 50 1 (.step 46 (.close 9)) (.step 9 (.close 46)))) (.step 7 (.close 27))) (.step 7 (.close 9))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 10 (.close 46))) (.step 10 (.step 30 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))) (.run (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 26 0 (.step 7 (.step 26 (.step 7 (.close 15)))) (.step 29 (.close 7))) (.step 7 (.step 26 (.close 31)))) (.step 7 (.step 26 (.close 71)))) (.step 7 (.step 26 (.close 71)))) (.step 7 (.step 15 (.close 71)))) (.step 7 (.close 62))) (.step 7 (.step 21 (.close 62)))) (.step 7 (.step 18 (.step 26 (.step 29 (.step 40 (.close 52))))))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 7 (.split 42 1 (.step 57 (.step 7 (.step 57 (.step 71 (.step 29 (.step 31 (.step 7 (.close 62)))))))) (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 40 (.step 57 (.step 26 (.step 29 (.close 31))))))) (.step 7 (.step 21 (.step 26 (.step 29 (.close 37)))))) (.step 7 (.step 26 (.step 29 (.step 37 (.close 52))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900807060179642755127455076762064039611778815312808745475319026294109206355877320298219048009728⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.reuse 0) (.run (.split 10 1 (.split 30 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 10 0 (.split 17 0 (.split 68 1 (.split 69 1 (.step 29 (.step 7 (.step 21 (.step 7 (.step 26 (.close 38)))))) (.step 4 (.step 21 (.step 22 (.step 29 (.close 38)))))) (.step 29 (.close 71))) (.step 18 (.step 7 (.close 4)))) (.step 18 (.step 7 (.close 38)))) (.step 7 (.step 21 (.step 29 (.close 70))))) (.step 21 (.close 71))) (.step 4 (.step 15 (.step 10 (.close 71))))) (.step 53 (.step 18 (.step 26 (.step 7 (.close 71)))))) (.step 21 (.step 29 (.step 38 (.step 57 (.close 4)))))) (.step 7 (.step 22 (.step 21 (.step 54 (.step 26 (.step 29 (.close 54)))))))) (.step 9 (.step 21 (.step 18 (.close 21))))) (.step 52 (.step 53 (.step 29 (.step 18 (.step 57 (.step 38 (.step 16 (.close 71))))))))) (.step 7 (.step 9 (.close 10)))) (.split 49 1 (.step 41 (.step 38 (.step 7 (.step 21 (.close 38))))) (.step 7 (.close 38)))) (.step 29 (.step 57 (.step 38 (.step 7 (.step 21 (.close 38))))))) (.step 7 (.close 18))) (.step 7 (.close 18)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200197408023521040185685109013464847708734576282818165289367301258197791490655125504⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.reuse 0) (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.step 7 (.close 26)))) (.step 29 (.close 7))) (.step 7 (.close 37))) (.step 7 (.step 4 (.step 15 (.close 39))))) (.step 4 (.step 7 (.step 15 (.step 28 (.close 39)))))) (.step 7 (.step 15 (.step 21 (.close 71))))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 62)))) (.step 7 (.step 15 (.step 21 (.close 62))))) (.step 15 (.step 7 (.step 29 (.close 52))))) (.step 37 (.split 49 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 54 1 (.step 7 (.close 37)) (.step 15 (.step 26 (.step 29 (.close 57))))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 15 (.step 37 (.close 52)))))) (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 40 (.step 15 (.step 29 (.step 31 (.close 26))))))) (.step 7 (.close 37))) (.step 15 (.step 37 (.close 52))))) (.step 15 (.step 29 (.step 37 (.step 38 (.step 7 (.step 21 (.close 37))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904899348241922649729044056425363910164480⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.split 10 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 29 (.step 71 (.step 7 (.split 67 1 (.step 29 (.step 7 (.close 15))) (.step 7 (.close 70)))))) (.step 10 (.step 71 (.close 15)))) (.step 4 (.step 10 (.step 15 (.close 71))))) (.step 27 (.step 62 (.close 71)))) (.step 29 (.close 57))) (.step 7 (.step 57 (.step 54 (.step 29 (.step 54 (.close 29))))))) (.step 27 (.step 29 (.step 57 (.step 53 (.close 29)))))) (.step 29 (.step 52 (.step 57 (.step 18 (.step 52 (.close 29))))))) (.step 7 (.step 9 (.close 10)))) (.step 28 (.close 29))) (.step 28 (.close 29))) (.step 29 (.close 71))) (.step 28 (.close 29))) (.step 18 (.close 7))) (.step 18 (.close 7))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 18 (.step 4 (.step 40 (.step 68 (.step 4 (.close 70)))))) (.step 4 (.step 18 (.close 57)))) (.step 7 (.close 54))) (.step 4 (.step 18 (.close 53)))) (.step 4 (.step 18 (.close 52)))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 24 (.close 26)))) (.step 7 (.close 39))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.step 24 (.step 4 (.close 37))))) (.step 4 (.step 18 (.close 29)))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.step 7 (.step 18 (.close 19))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 12 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 15 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 43 1 (.split 51 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 67 1 (.split 34 0 (.split 69 1 (.split 35 0 (.split 17 0 (.step 15 (.step 7 (.close 9))) (.step 4 (.close 7))) (.step 9 (.close 15))) (.step 4 (.step 9 (.step 15 (.close 7))))) (.step 7 (.close 15))) (.step 26 (.step 70 (.close 7)))) (.step 15 (.step 7 (.close 15)))) (.step 7 (.step 9 (.step 15 (.close 4))))) (.step 15 (.close 7))) (.step 15 (.close 71))) (.step 4 (.step 15 (.step 10 (.step 16 (.step 15 (.close 65))))))) (.step 4 (.step 15 (.close 64)))) (.step 15 (.step 54 (.step 22 (.step 54 (.step 15 (.close 54))))))) (.step 9 (.close 46))) (.step 15 (.close 62))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 15 (.step 7 (.close 15)))) (.step 15 (.step 7 (.close 31)))) (.step 15 (.close 38))) (.step 15 (.close 7))) (.step 15 (.close 29))))) (.step 5 (.step 15 (.close 18)))) (.step 4 (.step 15 (.close 7)))) (.step 5 (.step 15 (.close 18)))) (.step 5 (.step 4 (.step 7 (.step 15 (.close 18))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case30
