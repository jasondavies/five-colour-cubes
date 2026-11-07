module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case41
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644173564507927540435590648756849381251613549547746442057311099855700504692816498699903096480214471914513143050275913728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 7 (.close 37)) (.step 7 (.split 16 0 (.step 3 (.close 37)) (.step 7 (.close 5))))) (.step 7 (.step 3 (.step 18 (.step 5 (.close 50)))))) (.step 7 (.step 11 (.step 69 (.split 2 0 (.step 7 (.step 23 (.step 69 (.step 3 (.close 5))))) (.step 3 (.step 5 (.close 14)))))))) (.step 29 (.step 69 (.step 75 (.split 2 0 (.step 3 (.close 37)) (.step 3 (.close 37))))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 34 0 (.step 3 (.close 38)) (.step 39 (.step 3 (.close 37)))) (.step 67 (.close 3))) (.step 3 (.close 74))) (.step 3 (.close 74))) (.step 11 (.step 69 (.close 74)))) (.step 74 (.close 3)))) (.step 7 (.close 3))) (.step 3 (.step 63 (.step 3 (.step 74 (.close 3)))))) (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 17 0 (.split 14 0 (.split 34 0 (.step 3 (.close 38)) (.step 66 (.step 3 (.close 38)))) (.step 3 (.close 67))) (.step 3 (.close 67))) (.step 3 (.close 67))) (.step 67 (.close 3))) (.step 67 (.close 3))) (.step 3 (.close 67))))) (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 74 0 (.split 34 0 (.step 3 (.close 38)) (.step 29 (.step 37 (.close 3)))) (.step 3 (.close 41))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 3 (.step 63 (.close 66)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985451500009097113648969864882206129343095384995383954180293130402997466740422131247509819416478654555553862616511152128⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 17 0 (.split 22 0 (.step 59 (.close 3)) (.step 7 (.close 41))) (.step 5 (.step 7 (.close 41))))) (.step 5 (.step 3 (.close 37)))) (.step 7 (.close 41))) (.step 5 (.close 59))) (.step 5 (.close 14))) (.step 75 (.step 59 (.close 3)))) (.step 63 (.close 74))) (.step 18 (.close 48))) (.step 50 (.step 51 (.step 63 (.close 67)))))) (.step 51 (.step 63 (.step 66 (.close 3))))))) (.run (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))))) (.run (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 9 (.step 3 (.close 11)))) (.step 3 (.step 7 (.close 18)))))) (.run (.step 7 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 63 1 (.split 64 1 (.split 71 1 (.step 45 (.step 3 (.close 5))) (.step 29 (.step 69 (.close 74)))) (.step 29 (.step 67 (.close 45)))) (.step 66 (.step 69 (.step 37 (.step 3 (.close 38)))))) (.step 7 (.step 45 (.close 66)))) (.step 7 (.step 45 (.step 60 (.step 37 (.close 74)))))) (.step 5 (.step 66 (.step 67 (.step 7 (.step 37 (.close 39))))))) (.step 69 (.step 45 (.close 3)))) (.step 3 (.step 48 (.step 66 (.step 45 (.step 39 (.step 67 (.close 69)))))))) (.step 28 (.step 60 (.split 63 1 (.step 59 (.step 74 (.step 45 (.close 3)))) (.step 48 (.step 49 (.step 59 (.step 45 (.close 66))))))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318958202479088358270709877171335232098032849823173032808119584862781413030760546304⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.reuse 0) (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 16 0 (.split 30 0 (.split 35 0 (.step 3 (.close 37)) (.step 38 (.step 3 (.close 37)))) (.step 7 (.close 38))) (.step 5 (.close 41)))) (.step 5 (.step 3 (.close 37)))) (.step 7 (.close 41))) (.step 5 (.close 41))) (.step 5 (.close 14))) (.step 29 (.step 75 (.step 41 (.close 3))))) (.step 63 (.step 74 (.close 3)))) (.step 18 (.close 48))) (.step 63 (.close 67)))) (.step 63 (.step 66 (.close 41)))) (.step 28 (.split 63 1 (.split 64 1 (.step 7 (.step 59 (.step 5 (.close 41)))) (.step 41 (.close 5))) (.step 5 (.step 18 (.step 49 (.step 51 (.step 41 (.close 66))))))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 28 (.step 41 (.step 45 (.step 60 (.split 63 1 (.step 41 (.step 60 (.step 41 (.step 7 (.close 15))))) (.step 37 (.step 41 (.step 48 (.close 66))))))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747539506464040819618197042042523069565058848287641251583283861166181733792481280⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.reuse 0) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 39 (.close 3)) (.step 7 (.close 39))) (.step 29 (.step 51 (.close 74)))) (.step 29 (.step 51 (.close 67)))) (.step 29 (.step 51 (.step 66 (.close 3))))) (.step 7 (.step 39 (.step 49 (.step 39 (.close 66)))))) (.step 5 (.step 66 (.step 67 (.step 7 (.step 37 (.close 39))))))) (.step 75 (.close 7))) (.step 3 (.step 39 (.close 66)))) (.step 51 (.step 39 (.close 3)))) (.split 71 1 (.step 45 (.step 37 (.step 39 (.step 3 (.step 39 (.close 66)))))) (.step 39 (.close 74)))) (.step 41 (.split 63 1 (.split 64 1 (.step 39 (.step 5 (.close 39))) (.step 5 (.step 39 (.close 67)))) (.step 5 (.step 37 (.step 39 (.step 41 (.close 66)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197799417690294085122161849115506252862557815795558393546734955600916552299260596785131086151680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 37 (.close 3)) (.step 7 (.close 37))) (.step 29 (.step 74 (.close 3)))) (.step 29 (.step 67 (.close 37)))) (.step 66 (.close 3))) (.step 7 (.close 66))) (.step 5 (.step 23 (.step 17 (.step 3 (.step 66 (.close 74))))))) (.step 75 (.close 7))) (.step 3 (.step 37 (.close 67)))) (.step 28 (.split 63 1 (.split 64 1 (.step 37 (.step 3 (.close 5))) (.step 5 (.step 37 (.close 67)))) (.step 37 (.close 66))))) (.split 63 1 (.step 45 (.step 66 (.step 45 (.close 67)))) (.step 37 (.close 66)))) (.step 28 (.step 41 (.split 63 1 (.split 64 1 (.step 37 (.step 3 (.close 5))) (.step 5 (.step 21 (.step 37 (.close 5))))) (.step 37 (.close 66)))))) (.split 63 1 (.step 39 (.step 3 (.step 37 (.close 67)))) (.step 37 (.close 66)))) (.step 37 (.step 38 (.close 7))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117561194662240718867263952059482985591741365906680560360121837269549056⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 38 (.close 3)) (.step 3 (.close 38))) (.step 7 (.close 38))) (.step 3 (.close 38))) (.step 3 (.step 69 (.step 3 (.close 38))))) (.step 74 (.close 3))) (.step 3 (.close 7))) (.step 3 (.close 38))) (.step 67 (.close 3))) (.step 66 (.close 3))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 48 (.step 50 (.step 74 (.step 41 (.step 59 (.close 38)))))))))))) (.step 3 (.step 40 (.step 9 (.step 38 (.close 3)))))) (.step 9 (.close 7))) (.step 29 (.step 38 (.close 7)))) (.step 29 (.step 38 (.close 3)))) (.step 29 (.step 38 (.close 39)))))) (.reuse 1)) (.run (.split 35 1 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 7 (.close 18))) (.step 38 (.step 3 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783747696424552768906899041496908442958029581169197056⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 35 0 (.split 38 0 (.step 7 (.step 25 (.close 3))) (.step 7 (.close 18))) (.step 7 (.close 19))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.close 75))) (.step 11 (.step 18 (.step 69 (.close 74))))) (.step 3 (.step 18 (.step 25 (.close 69))))) (.step 67 (.step 3 (.close 18)))) (.step 11 (.step 66 (.step 18 (.close 25))))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 23 (.step 38 (.step 66 (.step 67 (.step 7 (.step 19 (.close 69)))))))))))) (.run (.step 7 (.split 22 1 (.split 35 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 35 0 (.split 38 0 (.step 7 (.step 11 (.close 20))) (.step 7 (.close 18))) (.step 7 (.close 19))) (.step 7 (.close 20))) (.step 7 (.step 19 (.close 20)))) (.step 11 (.close 74))) (.step 3 (.close 20))) (.step 67 (.step 3 (.close 18)))) (.step 11 (.step 66 (.step 3 (.close 20))))) (.step 7 (.close 74))) (.step 3 (.step 23 (.step 38 (.step 66 (.step 67 (.step 7 (.step 19 (.close 69))))))))) (.split 35 1 (.split 38 1 (.split 63 1 (.split 64 1 (.step 20 (.step 7 (.step 20 (.close 19)))) (.step 19 (.step 20 (.close 67)))) (.step 66 (.step 20 (.close 3)))) (.step 7 (.close 20))) (.step 7 (.step 19 (.step 20 (.close 75)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415782251118749319720893566632174552951537942428839313408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 2 0 (.split 10 0 (.split 71 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 3 (.step 5 (.close 17))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 5)))) (.step 7 (.step 17 (.close 3)))) (.step 17 (.step 7 (.step 17 (.close 3))))) (.step 40 (.step 69 (.step 75 (.close 3))))) (.step 11 (.step 17 (.close 74)))) (.step 17 (.step 7 (.step 3 (.close 17))))) (.step 17 (.step 23 (.step 74 (.step 49 (.step 5 (.close 3))))))) (.step 3 (.close 7))) (.step 3 (.step 17 (.close 5)))) (.step 67 (.close 3))) (.step 66 (.close 3))) (.step 5 (.step 17 (.close 49)))) (.step 23 (.step 11 (.step 17 (.close 3))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 23 (.step 17 (.step 66 (.step 67 (.step 7 (.step 37 (.close 69)))))))))) (.step 16 (.step 49 (.step 5 (.close 17))))) (.step 40 (.step 51 (.step 5 (.step 66 (.step 67 (.step 74 (.step 17 (.close 77))))))))) (.step 5 (.step 38 (.step 66 (.step 67 (.step 74 (.step 77 (.step 3 (.split 2 0 (.step 38 (.close 17)) (.step 3 (.close 5))))))))))) (.step 38 (.step 40 (.step 49 (.step 17 (.step 66 (.step 7 (.step 37 (.step 17 (.step 37 (.close 67))))))))))) (.step 3 (.step 67 (.step 7 (.close 17))))) (.step 7 (.step 11 (.split 38 1 (.step 17 (.step 5 (.close 7))) (.step 5 (.close 17)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256399069184⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.split 17 1 (.split 22 1 (.step 67 (.split 35 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 38 0 (.step 7 (.step 11 (.split 36 0 (.step 19 (.close 3)) (.step 7 (.close 19))))) (.step 7 (.close 18))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 67 (.step 74 (.close 3)))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 66 (.step 3 (.close 19))))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 23 (.step 38 (.step 19 (.close 66))))))) (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 25 (.step 18 (.step 3 (.close 19)))) (.step 19 (.close 67))) (.step 66 (.step 19 (.close 3)))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 19 (.close 38)))) (.split 35 1 (.split 38 1 (.split 63 1 (.split 64 1 (.step 20 (.step 7 (.close 19))) (.step 19 (.close 67))) (.step 66 (.step 19 (.close 3)))) (.step 7 (.close 19))) (.step 19 (.close 38))))))) (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 7 (.step 11 (.step 20 (.step 74 (.step 17 (.step 5 (.close 7))))))))) (.run (.step 7 (.step 11 (.step 19 (.step 67 (.step 17 (.step 5 (.close 7)))))))))) (.run (.split 14 1 (.split 35 1 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 7 (.close 18))) (.step 3 (.step 66 (.step 7 (.close 38))))) (.step 17 (.step 3 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 23 (.step 5 (.split 42 1 (.split 63 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 67 (.step 5 (.close 74)))) (.step 3 (.step 18 (.close 49)))))) (.step 3 (.step 69 (.step 67 (.step 5 (.close 37)))))) (.step 66 (.close 5))) (.step 3 (.step 5 (.step 60 (.step 37 (.step 39 (.close 66))))))))) (.step 5 (.close 3))) (.step 3 (.step 5 (.step 39 (.step 5 (.close 41)))))) (.step 3 (.step 38 (.step 5 (.close 66))))) (.step 3 (.step 5 (.step 37 (.step 5 (.close 41)))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 5 (.step 18 (.close 19)))) (.step 5 (.close 17))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case41
