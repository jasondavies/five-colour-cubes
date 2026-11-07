module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case205
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592783902519083183027, 5789228615357111141503591527908565328988052238931866842109466783872516018158651860904340855333424994291657941685580562196867513399766593215024954541188249413884004349401981041481010002029536037373500234088386757515328619520, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877946047361966226669012756174301604460680445952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 24 0 (.split 30 0 (.split 38 0 (.split 39 0 (.step 29 (.step 57 (.step 43 (.close 39)))) (.step 38 (.step 9 (.close 43)))) (.step 38 (.step 5 (.close 3)))) (.split 34 0 (.split 36 0 (.step 53 (.step 3 (.close 24))) (.step 38 (.step 3 (.close 68)))) (.step 38 (.step 43 (.step 9 (.close 57)))))) (.split 34 0 (.split 30 0 (.step 29 (.step 27 (.close 3))) (.step 42 (.step 7 (.close 20)))) (.split 36 0 (.step 43 (.close 29)) (.step 29 (.close 7))))) (.split 24 0 (.step 29 (.step 7 (.step 27 (.close 7)))) (.split 30 0 (.split 34 0 (.step 5 (.close 27)) (.step 7 (.step 5 (.close 15)))) (.step 7 (.close 4))))) (.split 24 0 (.split 25 0 (.split 34 0 (.split 30 0 (.step 43 (.close 52)) (.step 42 (.step 43 (.close 67)))) (.step 43 (.close 3))) (.step 43 (.close 29))) (.split 30 0 (.step 43 (.close 27)) (.step 7 (.close 24))))) (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 43 (.close 74)) (.split 34 0 (.step 42 (.step 43 (.close 20))) (.step 38 (.close 43)))) (.step 43 (.close 29))) (.split 30 0 (.step 43 (.close 27)) (.step 7 (.close 24)))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 20 (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 20)))) (.step 24 (.step 33 (.close 20)))) (.step 7 (.close 4))) (.step 7 (.close 24))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877947441158541134832959102156693644983274569728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 5 (.step 9 (.close 57)))) (.step 5 (.close 55))) (.split 35 0 (.step 43 (.close 17)) (.step 29 (.step 38 (.close 37))))) (.split 34 0 (.step 42 (.step 43 (.close 67))) (.step 37 (.close 17)))) (.split 30 0 (.step 29 (.step 5 (.close 3))) (.step 37 (.step 4 (.close 7))))) (.split 30 0 (.split 25 0 (.split 34 0 (.split 39 0 (.step 29 (.close 27)) (.step 27 (.close 5))) (.split 36 0 (.step 52 (.close 5)) (.step 5 (.step 7 (.close 17))))) (.split 34 0 (.step 27 (.close 5)) (.step 5 (.close 15)))) (.split 25 0 (.step 42 (.step 43 (.close 27))) (.step 5 (.close 27))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 62))) (.step 24 (.step 4 (.step 15 (.close 62))))) (.step 17 (.close 37))) (.step 24 (.step 67 (.step 13 (.close 43))))) (.step 63 (.step 4 (.step 3 (.close 5))))) (.split 25 0 (.step 11 (.split 30 0 (.step 68 (.step 17 (.close 29))) (.step 7 (.close 27)))) (.step 7 (.close 27))))) (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 74 (.step 37 (.step 24 (.close 42)))) (.step 24 (.step 67 (.step 13 (.close 43))))) (.step 63 (.step 4 (.step 3 (.close 5))))) (.split 25 0 (.step 11 (.step 61 (.step 17 (.step 29 (.close 7))))) (.step 7 (.close 27)))) (.step 24 (.split 24 0 (.split 25 0 (.step 17 (.step 20 (.close 24))) (.step 7 (.close 18))) (.step 7 (.step 17 (.step 18 (.close 19)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444053036643934872976664639207112704⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 24 0 (.split 30 0 (.step 43 (.close 67)) (.step 38 (.close 19))) (.step 42 (.step 29 (.close 7)))) (.step 38 (.split 24 0 (.step 5 (.close 43)) (.step 7 (.close 4))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 19 (.close 24))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 33 (.close 24)))) (.step 7 (.close 4))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 19 (.close 20))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 33 (.close 20)))) (.step 7 (.close 4))) (.step 7 (.close 24))) (.step 24 (.step 19 (.step 7 (.step 19 (.step 20 (.close 9)))))))))) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 67 (.split 30 0 (.step 37 (.step 24 (.close 42))) (.step 42 (.close 3)))) (.step 23 (.step 38 (.step 24 (.close 7))))) (.split 35 0 (.split 43 0 (.step 67 (.split 49 0 (.step 7 (.close 15)) (.step 17 (.close 5)))) (.step 7 (.close 11))) (.step 24 (.close 29)))) (.step 24 (.split 24 0 (.step 19 (.step 7 (.step 11 (.step 13 (.step 17 (.close 25)))))) (.step 7 (.step 17 (.close 19)))))) (.split 22 0 (.step 24 (.split 24 0 (.step 19 (.step 7 (.step 13 (.step 19 (.close 20))))) (.step 7 (.step 17 (.close 19))))) (.step 19 (.step 20 (.step 7 (.close 24)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773281032428850745880471699487457280⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 15 (.step 57 (.step 43 (.close 38)))) (.step 38 (.step 5 (.close 37)))) (.step 38 (.step 15 (.step 3 (.close 57)))))) (.step 75 (.split 34 0 (.step 43 (.step 9 (.step 15 (.close 43)))) (.step 15 (.close 43))))) (.step 29 (.close 3))) (.split 25 0 (.step 9 (.step 29 (.close 7))) (.step 29 (.close 3)))) (.split 24 0 (.split 22 0 (.split 25 0 (.split 30 0 (.step 29 (.step 66 (.close 43))) (.step 18 (.step 24 (.close 39)))) (.step 9 (.step 4 (.close 29)))) (.step 24 (.close 4))) (.step 24 (.step 29 (.close 7))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 38 (.close 24))) (.step 18 (.step 24 (.close 13)))) (.step 38 (.step 24 (.close 15)))) (.step 24 (.close 38))) (.step 38 (.step 23 (.close 29)))) (.step 24 (.step 29 (.close 7))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 30 0 (.step 29 (.step 15 (.close 5))) (.step 38 (.close 13))) (.step 9 (.step 29 (.close 7))))) (.step 24 (.step 4 (.close 17)))) (.step 24 (.step 4 (.close 17)))) (.split 17 0 (.step 24 (.step 4 (.close 17))) (.step 13 (.close 17)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877946047361966227936663356402531005957383651328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 52 (.step 3 (.close 24))) (.step 43 (.step 29 (.step 18 (.close 13))))) (.step 15 (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.close 3))) (.step 33 (.step 13 (.close 57)))) (.step 38 (.close 13))) (.step 15 (.step 33 (.close 15))))) (.split 30 0 (.step 29 (.close 7)) (.step 7 (.close 3)))) (.split 25 0 (.split 30 0 (.split 34 0 (.step 43 (.step 27 (.close 7))) (.step 7 (.step 5 (.close 29)))) (.step 7 (.close 24))) (.step 7 (.close 4)))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.close 13)) (.step 42 (.step 4 (.close 43)))) (.step 15 (.step 17 (.close 15)))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.close 24))) (.step 33 (.close 13))) (.step 13 (.step 15 (.close 43)))))) (.step 7 (.close 3))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.close 13)) (.step 42 (.step 4 (.close 43)))) (.step 15 (.step 17 (.close 15)))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.close 24))) (.step 33 (.close 13))) (.step 13 (.step 15 (.close 43)))))) (.step 7 (.close 3))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 13 (.step 20 (.close 24))) (.step 19 (.step 13 (.step 20 (.close 4)))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444054304294535101206066135910318080⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.close 13)) (.step 38 (.close 13))) (.step 15 (.step 17 (.close 15)))) (.split 34 0 (.step 42 (.step 13 (.close 38))) (.step 13 (.close 38)))) (.step 7 (.close 3))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.step 42 (.step 13 (.step 38 (.step 24 (.close 19))))))))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 30 0 (.step 20 (.step 13 (.close 19))) (.step 13 (.step 20 (.close 42)))) (.step 19 (.close 24))) (.step 13 (.step 14 (.close 17))))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 30 0 (.step 66 (.step 43 (.close 11))) (.split 35 0 (.step 13 (.close 15)) (.step 15 (.close 13)))) (.step 5 (.step 15 (.close 3)))) (.split 30 0 (.step 68 (.step 15 (.close 7))) (.step 7 (.close 17))))) (.step 24 (.split 25 0 (.step 17 (.close 13)) (.step 3 (.close 7))))) (.split 22 0 (.step 24 (.split 25 0 (.step 17 (.close 13)) (.step 3 (.close 7)))) (.step 7 (.close 17)))) (.split 17 0 (.split 22 0 (.step 24 (.split 25 0 (.step 17 (.close 13)) (.step 3 (.close 7)))) (.step 7 (.close 17))) (.step 13 (.close 17))))))
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
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444053036643934874129586143813959680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 9 (.close 43)) (.step 38 (.step 5 (.close 9)))) (.step 38 (.step 7 (.close 9))))) (.step 75 (.split 34 0 (.step 43 (.step 9 (.close 3))) (.step 7 (.close 9))))) (.step 9 (.close 29))) (.split 25 0 (.step 9 (.step 29 (.close 7))) (.step 29 (.close 3)))) (.split 24 0 (.split 22 0 (.split 30 0 (.step 29 (.step 68 (.step 74 (.step 43 (.close 11))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 24 (.step 29 (.close 7))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 9 (.step 4 (.close 11)))) (.step 7 (.close 9))) (.step 7 (.step 15 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.close 29))) (.step 24 (.step 29 (.close 7))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 34 0 (.split 35 0 (.step 9 (.step 5 (.close 11))) (.step 38 (.step 9 (.close 3)))) (.split 30 0 (.step 29 (.step 43 (.step 5 (.close 9)))) (.step 7 (.close 9)))) (.step 9 (.step 29 (.close 7))))) (.step 24 (.step 4 (.close 11)))) (.step 24 (.step 4 (.close 11)))) (.split 30 0 (.step 24 (.step 4 (.close 11))) (.step 7 (.close 11))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def references : Fin 3 → Box := ![Part3.root, Part5.root, Part6.root]
def proof : Chunks.Proof 3 := (.split 6 0 (.split 10 0 (.reuse 0) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 35 0 (.step 43 (.close 13)) (.step 15 (.close 17))) (.step 9 (.step 4 (.close 7)))) (.step 9 (.step 29 (.close 7))))) (.step 24 (.close 13))) (.step 24 (.close 13))) (.split 17 0 (.step 24 (.close 13)) (.step 13 (.close 17)))) (.split 16 0 (.step 15 (.close 13)) (.step 13 (.close 15))))))) (.split 10 0 (.split 12 0 (.reuse 2) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 25 0 (.split 34 0 (.step 9 (.step 15 (.split 35 0 (.step 9 (.close 7)) (.step 9 (.close 3))))) (.step 15 (.close 4))) (.step 9 (.close 4))) (.step 9 (.close 29))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 9 (.split 35 0 (.step 24 (.close 9)) (.step 9 (.close 7)))) (.step 7 (.close 15))) (.step 7 (.close 9))) (.step 4 (.close 9))) (.step 4 (.step 9 (.close 11))))) (.split 24 0 (.split 30 0 (.step 15 (.step 5 (.close 7))) (.step 4 (.close 15))) (.step 29 (.close 9)))))) (.run (.split 14 0 (.split 12 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.step 29 (.split 38 0 (.step 9 (.step 4 (.step 9 (.close 7)))) (.step 4 (.close 7)))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 16 0 (.step 24 (.step 9 (.step 29 (.close 7)))) (.step 7 (.close 11)))) (.split 24 0 (.split 25 0 (.step 15 (.close 7)) (.step 7 (.close 9))) (.step 4 (.step 9 (.close 7))))) (.split 16 0 (.step 15 (.close 7)) (.step 7 (.close 11)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case205
