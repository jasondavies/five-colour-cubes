module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239476181206564864⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930440276761051891909598906447530463713519493061023221394449654500041625043738696340497667859955788528249253050871172440742036289011298962283587115845520670002208042291324945331961320205850771456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 7 (.close 28)) (.step 7 (.close 28))) (.step 7 (.step 47 (.step 3 (.close 5))))) (.step 7 (.step 3 (.step 18 (.step 5 (.close 29)))))) (.step 7 (.step 11 (.step 23 (.step 69 (.step 3 (.close 5))))))) (.step 29 (.step 7 (.step 69 (.step 3 (.close 5)))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 74))) (.step 47 (.close 74))) (.step 3 (.close 74))) (.step 11 (.step 3 (.close 74)))) (.step 29 (.step 69 (.close 74))))) (.step 7 (.close 3))) (.step 3 (.step 63 (.step 3 (.close 74))))) (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 21))) (.step 3 (.close 67))) (.step 47 (.close 67))) (.step 3 (.close 67))) (.step 11 (.close 67))) (.step 67 (.close 3))) (.step 3 (.close 67)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985451500009097113648969864882206129343097239478063145572485461032054246507696343774607980066138307919242355078914375680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.reuse 0) (.run (.step 3 (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 66))) (.step 47 (.close 66))) (.step 3 (.close 66))) (.step 11 (.step 3 (.close 66)))) (.step 66 (.close 3))) (.step 3 (.close 66))))))) (.run (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 28 (.close 7)) (.step 5 (.step 3 (.close 28)))) (.step 5 (.step 3 (.close 28)))) (.step 5 (.close 59))) (.step 28 (.step 75 (.step 3 (.close 5)))))) (.step 63 (.close 74))) (.step 18 (.close 48))) (.step 51 (.step 63 (.step 67 (.close 3))))) (.step 51 (.step 63 (.step 66 (.close 3)))))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 7 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 72 1 (.step 45 (.split 64 1 (.step 7 (.step 29 (.close 3))) (.step 29 (.close 67)))) (.step 29 (.step 45 (.close 3)))) (.step 7 (.step 29 (.step 45 (.close 37))))) (.step 7 (.step 28 (.step 45 (.close 5))))) (.step 5 (.step 7 (.step 29 (.close 77))))) (.step 3 (.step 29 (.close 45)))) (.step 29 (.step 66 (.close 3)))) (.step 5 (.step 28 (.step 45 (.step 59 (.step 51 (.step 60 (.step 3 (.close 59))))))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915749393989143232211810527671099302836839271375385801901242937224854674196195704832⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.split 42 1 (.split 51 1 (.split 56 1 (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 28 (.close 7)) (.step 5 (.step 3 (.close 28)))) (.step 5 (.step 3 (.close 28)))) (.step 5 (.close 41))) (.step 28 (.step 38 (.step 3 (.close 5)))))) (.step 67 (.step 5 (.step 28 (.step 59 (.step 3 (.close 5))))))) (.step 18 (.close 48))) (.step 63 (.close 67))) (.step 63 (.step 66 (.close 41))))) (.step 5 (.step 28 (.step 7 (.step 41 (.step 51 (.step 41 (.close 74)))))))) (.step 3 (.step 7 (.close 18)))) (.step 28 (.step 5 (.step 41 (.step 45 (.step 60 (.step 3 (.close 41)))))))))) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 71 1 (.step 39 (.step 7 (.step 29 (.close 3)))) (.step 29 (.close 74))) (.step 7 (.step 29 (.step 39 (.close 11))))) (.step 7 (.step 28 (.close 39)))) (.step 5 (.step 7 (.step 11 (.step 29 (.step 37 (.close 39))))))) (.step 3 (.close 39))) (.step 29 (.step 66 (.close 3)))) (.step 5 (.step 39 (.close 51)))) (.step 39 (.step 37 (.step 39 (.close 11))))) (.step 28 (.step 39 (.step 5 (.step 39 (.step 41 (.close 74))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270421462730796752586854571347924043719333695512689902015566333924048614299672772608⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 51 1 (.step 29 (.split 56 1 (.split 65 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.step 3 (.step 38 (.close 3)))) (.step 74 (.close 3))) (.step 67 (.close 3))) (.step 66 (.close 3))) (.step 3 (.close 38))) (.step 3 (.step 38 (.step 48 (.step 38 (.close 5))))))) (.step 3 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.close 3))))) (.step 29 (.close 38))) (.step 38 (.close 7))))) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 64 1 (.split 71 1 (.split 72 1 (.split 14 0 (.split 64 0 (.step 7 (.close 28)) (.step 29 (.close 7))) (.step 7 (.close 37))) (.step 29 (.close 37))) (.step 29 (.step 37 (.close 3)))) (.step 29 (.step 37 (.close 3)))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 28 (.close 37)))) (.step 5 (.step 7 (.step 11 (.step 29 (.close 37)))))) (.step 3 (.close 37))) (.step 29 (.close 66))) (.step 5 (.step 28 (.step 37 (.close 3))))) (.step 37 (.step 3 (.close 11)))) (.step 28 (.step 37 (.step 5 (.step 37 (.close 41)))))) (.step 37 (.close 74))) (.step 29 (.step 37 (.step 38 (.close 3)))))))) (.run (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 7 (.close 18))) (.step 3 (.step 7 (.close 38))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673895810653296350978514979767546304770703271102365302784⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 25 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.step 29 (.step 66 (.step 3 (.close 67)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7)))))) (.run (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 29 (.split 56 1 (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 16 0 (.step 5 (.step 18 (.split 17 0 (.step 28 (.close 3)) (.step 5 (.close 7))))) (.step 7 (.close 18))) (.step 18 (.close 15))) (.step 29 (.close 67))) (.step 29 (.close 66)))) (.step 28 (.close 5)))) (.step 3 (.step 7 (.close 18)))) (.step 7 (.close 10))) (.step 28 (.close 5))) (.step 28 (.close 5))) (.step 28 (.close 5))) (.step 28 (.close 5))) (.step 7 (.close 18))))) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 8 0 (.step 7 (.step 18 (.close 25))) (.step 11 (.close 7))) (.step 7 (.close 75))) (.step 3 (.step 11 (.step 18 (.close 19))))) (.step 18 (.step 67 (.close 3)))) (.step 11 (.step 66 (.step 3 (.close 5))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 11 (.step 29 (.step 38 (.step 7 (.step 19 (.close 20)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 19 (.close 69))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692474615154006138544499838960798418433221853184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 17 1 (.step 67 (.split 22 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 72 1 (.split 8 0 (.step 7 (.step 18 (.close 19))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 19)))) (.step 18 (.step 66 (.close 3)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.close 67))) (.step 3 (.step 29 (.step 19 (.close 38))))) (.step 3 (.step 11 (.step 23 (.step 29 (.close 19)))))) (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 25 (.step 18 (.step 3 (.close 19)))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 29)))) (.step 7 (.step 19 (.close 29)))) (.step 7 (.close 19))))) (.step 19 (.step 67 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 63 1 (.step 20 (.step 7 (.close 19))) (.step 18 (.step 19 (.close 3)))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 29)))) (.step 7 (.step 19 (.close 29)))) (.step 7 (.close 19))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673895810653297744775089887931492650753095311624959426560⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 25 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 4 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 11 (.step 7 (.step 3 (.step 17 (.step 23 (.step 3 (.close 5))))))) (.step 3 (.close 7))) (.step 29 (.step 11 (.step 17 (.step 3 (.close 5)))))) (.step 11 (.close 74))) (.step 17 (.close 67))) (.step 11 (.close 66))) (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.close 17))) (.step 11 (.close 67))) (.step 17 (.close 66)))) (.step 11 (.step 17 (.step 23 (.step 66 (.step 67 (.step 5 (.close 3)))))))) (.step 3 (.step 11 (.step 3 (.close 7))))) (.step 5 (.close 17))) (.step 23 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 11 (.close 7)))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 29 (.step 37 (.close 39))))))))) (.step 16 (.step 5 (.close 17)))) (.step 3 (.step 5 (.step 23 (.step 11 (.step 17 (.step 7 (.step 29 (.step 37 (.close 39)))))))))) (.step 5 (.step 29 (.step 38 (.step 11 (.step 17 (.step 66 (.step 3 (.step 38 (.step 50 (.step 17 (.close 37)))))))))))) (.step 3 (.step 7 (.step 29 (.step 5 (.step 17 (.step 37 (.step 17 (.close 37))))))))) (.step 3 (.step 7 (.close 17)))) (.step 3 (.step 29 (.step 17 (.close 3))))) (.step 29 (.step 5 (.close 17)))) (.step 11 (.step 17 (.step 5 (.step 7 (.step 17 (.close 3))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976096785171419860452519182336⟩
def references : Fin 3 → Box := ![Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.split 22 1 (.step 74 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 72 1 (.split 8 0 (.step 7 (.step 18 (.close 20))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 75)))) (.step 3 (.close 20))) (.step 11 (.step 18 (.step 51 (.close 66))))) (.step 7 (.close 74))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 11 (.step 29 (.step 7 (.step 19 (.close 20))))))) (.step 3 (.step 11 (.step 29 (.close 20)))))) (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 25 (.step 18 (.step 3 (.close 19)))) (.step 18 (.step 20 (.close 66)))) (.step 7 (.close 20))) (.step 7 (.close 20))) (.step 7 (.step 19 (.step 20 (.close 29))))) (.step 7 (.step 29 (.close 20)))) (.step 7 (.close 20))))))) (.reuse 1)) (.split 16 1 (.split 17 1 (.reuse 2) (.run (.step 11 (.step 17 (.step 7 (.step 20 (.step 5 (.step 17 (.close 3))))))))) (.run (.step 11 (.step 17 (.step 19 (.step 5 (.step 7 (.step 17 (.close 3)))))))))) (.run (.step 7 (.split 14 1 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 7 (.close 18))) (.step 3 (.step 7 (.close 38)))) (.step 3 (.close 29))) (.step 7 (.close 18))) (.step 3 (.close 17))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239476181205516288⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 8 1 (.reuse 0) (.run (.split 14 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 11 (.split 42 1 (.split 56 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.step 7 (.step 11 (.step 3 (.close 5)))) (.step 3 (.step 29 (.step 11 (.close 5))))) (.step 11 (.close 74))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 3 (.close 7))) (.step 5 (.close 8))) (.step 5 (.step 7 (.step 11 (.step 3 (.step 29 (.step 37 (.close 69))))))))) (.step 8 (.step 5 (.close 11)))) (.step 3 (.step 5 (.step 7 (.step 23 (.step 11 (.step 29 (.step 39 (.close 66))))))))) (.step 29 (.step 38 (.step 11 (.step 3 (.close 38)))))) (.step 3 (.step 7 (.step 29 (.step 5 (.step 38 (.step 23 (.step 11 (.step 37 (.close 66)))))))))) (.step 9 (.step 29 (.close 11)))) (.step 29 (.step 5 (.close 11)))) (.step 8 (.close 11))) (.step 8 (.close 11))) (.step 11 (.step 5 (.close 7)))))) (.run (.step 7 (.split 8 1 (.split 14 1 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 7 (.close 18))) (.step 3 (.step 7 (.close 38)))) (.step 3 (.close 29))) (.step 7 (.close 18))) (.step 3 (.step 7 (.close 17)))) (.step 3 (.close 11))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239476181206564864⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 29 (.split 22 1 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 11 (.step 66 (.close 5)))) (.step 3 (.step 11 (.close 18)))))) (.step 3 (.step 29 (.step 5 (.close 66))))) (.step 3 (.step 5 (.step 28 (.step 37 (.close 60)))))) (.step 3 (.step 5 (.close 39)))) (.step 38 (.close 5))) (.step 3 (.step 28 (.step 5 (.close 37))))) (.step 5 (.close 28))) (.step 3 (.step 5 (.close 18))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 5 (.close 17))) (.step 5 (.close 11))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case9
