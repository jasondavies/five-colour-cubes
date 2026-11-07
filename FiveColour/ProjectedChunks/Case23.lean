module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case23
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734898008064⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593704327342179793651, 5789228615357111146520043253955950924962759905236944250816662429627930946143174768881773115736627492968050798482740711356931196351281104609431181736320982633118032348601960626826787145704805298534408245321323047477072364544, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645165905657932616471782169375884404183931266631908385858966624142249159354633612228051434473402457163817761377550236859536351171706880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 7 (.close 28)) (.step 3 (.step 7 (.close 37)))) (.step 7 (.split 14 0 (.step 3 (.close 41)) (.step 11 (.step 3 (.close 5)))))) (.step 7 (.step 3 (.step 18 (.split 8 0 (.step 3 (.step 5 (.close 28))) (.step 5 (.close 3))))))) (.split 10 0 (.step 11 (.step 7 (.step 3 (.step 23 (.step 69 (.step 3 (.close 5))))))) (.step 3 (.close 7)))) (.step 29 (.step 69 (.step 75 (.step 3 (.close 5)))))) (.step 74 (.step 3 (.close 74)))) (.step 7 (.close 3))) (.step 3 (.step 63 (.step 3 (.step 74 (.close 3)))))) (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.step 3 (.close 67)) (.step 29 (.close 75))) (.step 3 (.close 67)))))) (.step 66 (.step 3 (.step 66 (.step 3 (.close 66)))))) (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.step 28 (.split 16 0 (.step 51 (.step 3 (.close 5))) (.step 5 (.step 7 (.close 37))))) (.step 7 (.close 41))) (.step 5 (.step 3 (.close 41)))) (.step 5 (.close 59))) (.step 5 (.close 8))) (.step 75 (.step 59 (.close 3)))) (.step 63 (.close 74))) (.step 18 (.close 48))) (.step 50 (.step 51 (.step 63 (.close 67))))) (.step 51 (.step 63 (.step 66 (.close 3))))))) (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51)))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318960055152516155329836654307095371104558502142927683057145425109945154270009491456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 51 1 (.split 56 1 (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.step 28 (.split 16 0 (.split 14 0 (.step 3 (.close 37)) (.step 5 (.close 37))) (.step 5 (.close 41)))) (.step 7 (.close 41))) (.step 5 (.step 3 (.close 41)))) (.step 5 (.close 41))) (.step 5 (.close 8))) (.step 29 (.step 38 (.step 48 (.step 69 (.step 41 (.close 3))))))) (.step 63 (.step 74 (.close 3)))) (.step 18 (.close 48))) (.step 63 (.close 67))) (.step 63 (.step 66 (.close 38))))) (.step 5 (.step 28 (.split 63 1 (.step 7 (.step 41 (.step 51 (.step 41 (.close 74))))) (.step 18 (.step 49 (.step 51 (.step 41 (.close 66))))))))) (.step 3 (.step 7 (.close 18)))) (.step 28 (.step 41 (.step 5 (.step 45 (.split 63 1 (.step 41 (.step 60 (.step 3 (.close 41)))) (.step 37 (.step 41 (.step 48 (.close 66)))))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915749392179891837878744974177802662076090711168042291500609124108329922973041426432⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 9 (.step 3 (.close 11)))))) (.run (.step 7 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 45 (.step 7 (.step 29 (.step 3 (.close 38))))) (.step 7 (.step 29 (.close 45)))) (.step 7 (.step 29 (.step 45 (.close 37))))) (.step 7 (.step 29 (.step 45 (.close 5))))) (.step 29 (.step 66 (.close 3)))) (.step 5 (.step 11 (.step 29 (.step 66 (.step 7 (.step 37 (.close 39)))))))) (.step 29 (.step 69 (.step 45 (.close 3))))) (.step 3 (.step 29 (.step 45 (.step 15 (.step 39 (.step 21 (.close 69)))))))) (.step 5 (.step 28 (.step 45 (.split 63 1 (.step 59 (.step 51 (.step 60 (.step 3 (.close 59))))) (.step 48 (.step 51 (.close 66))))))))))) (.reuse 1)) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 8 0 (.split 14 0 (.step 39 (.step 29 (.step 39 (.close 3)))) (.step 7 (.step 29 (.close 39)))) (.step 7 (.step 29 (.step 39 (.close 11))))) (.step 29 (.step 51 (.close 66)))) (.step 5 (.step 11 (.step 29 (.step 66 (.step 7 (.step 37 (.close 39)))))))) (.step 29 (.step 75 (.close 3)))) (.step 3 (.step 29 (.close 39)))) (.step 51 (.step 39 (.close 3)))) (.split 71 1 (.step 45 (.step 37 (.step 39 (.step 3 (.step 39 (.close 11)))))) (.step 39 (.close 74)))) (.step 39 (.step 41 (.step 5 (.split 63 1 (.step 39 (.step 5 (.close 21))) (.step 37 (.step 39 (.close 66)))))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197799417690294086974835276912565379639693575934564919199054710251165578139507760526370335096832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 71 1 (.split 10 0 (.step 37 (.close 7)) (.step 7 (.close 37))) (.step 29 (.step 66 (.step 39 (.close 74))))) (.step 7 (.close 37))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 29 (.close 37)))) (.step 29 (.close 66))) (.step 5 (.step 11 (.step 17 (.step 7 (.step 29 (.step 37 (.close 66)))))))) (.step 29 (.step 75 (.close 3)))) (.step 3 (.step 29 (.close 37)))) (.step 5 (.step 37 (.step 48 (.step 5 (.close 37)))))) (.split 63 1 (.step 45 (.step 66 (.step 45 (.close 67)))) (.step 37 (.close 66)))) (.step 37 (.step 41 (.step 5 (.step 37 (.step 41 (.step 5 (.close 15)))))))) (.split 63 1 (.step 39 (.step 3 (.step 37 (.close 11)))) (.step 37 (.close 66)))) (.step 29 (.step 37 (.step 38 (.close 3)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973155312915794990387541965110787625101041863957152128867989686592733184⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 51 1 (.step 29 (.split 56 1 (.split 65 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 8 0 (.step 38 (.close 3)) (.step 3 (.close 38))) (.step 3 (.close 38))) (.step 3 (.step 11 (.step 38 (.close 3))))) (.step 74 (.close 3))) (.step 67 (.close 3))) (.step 66 (.close 3))) (.step 3 (.close 38))) (.step 3 (.step 38 (.step 48 (.step 38 (.close 5))))))) (.step 40 (.step 29 (.step 3 (.close 7)))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.close 3))))) (.step 3 (.close 38))) (.step 38 (.close 7))))) (.reuse 1)) (.run (.step 7 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 38)))))) (.run (.split 30 1 (.split 43 1 (.split 51 1 (.step 29 (.step 66 (.step 67 (.step 3 (.close 74))))) (.step 29 (.step 3 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.step 3 (.close 29))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304025709475857408416199539547380011465897430492381184⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 38 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.step 7 (.step 18 (.close 25))) (.step 11 (.close 7))) (.step 7 (.close 75))) (.step 18 (.step 69 (.close 74)))) (.step 3 (.step 11 (.step 18 (.close 25))))) (.step 11 (.step 67 (.step 3 (.close 5))))) (.step 11 (.step 66 (.step 3 (.close 18))))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 11 (.step 29 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20))))))))) (.step 29 (.step 3 (.step 11 (.step 66 (.step 19 (.close 69)))))))))) (.run (.step 7 (.split 22 1 (.step 74 (.split 26 1 (.split 35 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 8 0 (.step 7 (.step 18 (.close 20))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 75)))) (.step 3 (.close 20))) (.step 11 (.step 18 (.step 51 (.close 67))))) (.step 11 (.step 66 (.close 20)))) (.step 7 (.close 74))) (.step 3 (.step 11 (.step 29 (.step 38 (.step 7 (.step 19 (.close 20)))))))) (.step 29 (.step 3 (.step 11 (.step 20 (.close 66))))))) (.split 26 1 (.split 35 1 (.split 38 1 (.split 63 1 (.split 64 1 (.step 20 (.step 7 (.step 20 (.close 19)))) (.step 19 (.step 20 (.close 29)))) (.step 11 (.step 18 (.step 51 (.step 66 (.close 3)))))) (.step 7 (.close 20))) (.step 7 (.step 19 (.step 20 (.close 75))))) (.step 7 (.step 11 (.step 29 (.step 20 (.close 66))))))))))
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
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687302529131800624360402867130225024520045810278162497536⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 65 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.step 11 (.step 7 (.step 3 (.step 23 (.split 35 0 (.step 3 (.close 5)) (.step 29 (.step 3 (.close 5)))))))) (.step 3 (.close 7))) (.step 11 (.step 5 (.close 3)))) (.step 11 (.close 17))) (.step 29 (.step 11 (.step 69 (.step 3 (.close 5)))))) (.step 74 (.close 3))) (.step 11 (.step 17 (.close 67)))) (.step 66 (.close 3))) (.step 3 (.step 11 (.step 7 (.close 17))))) (.step 3 (.step 23 (.close 17)))) (.step 5 (.close 17))) (.step 23 (.step 11 (.step 3 (.close 17))))) (.step 3 (.step 11 (.close 7)))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 29 (.step 66 (.step 7 (.step 37 (.close 69)))))))))) (.step 16 (.step 5 (.close 17)))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 17 (.step 23 (.step 11 (.step 66 (.step 7 (.step 37 (.close 77)))))))))))) (.step 5 (.step 29 (.step 38 (.step 11 (.step 17 (.step 66 (.step 67 (.step 3 (.step 38 (.step 74 (.close 17)))))))))))) (.step 29 (.step 38 (.step 40 (.step 49 (.step 17 (.step 66 (.step 7 (.step 37 (.step 17 (.close 37))))))))))) (.step 3 (.step 7 (.step 11 (.step 7 (.close 17)))))) (.step 3 (.step 29 (.step 23 (.close 17))))) (.step 7 (.step 11 (.step 17 (.step 5 (.step 3 (.close 17))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174829158938370359105722253312⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.split 17 1 (.step 67 (.split 22 1 (.split 26 1 (.split 35 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 8 0 (.step 7 (.step 18 (.close 19))) (.step 11 (.close 7))) (.step 11 (.step 18 (.step 67 (.close 74))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 66 (.step 3 (.close 18))))) (.step 7 (.step 5 (.close 18)))) (.step 3 (.step 11 (.step 38 (.close 19))))) (.step 29 (.step 3 (.step 11 (.step 19 (.close 66)))))) (.step 19 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 25 (.step 3 (.close 19))) (.step 18 (.step 25 (.step 20 (.close 66))))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 19 (.close 38))) (.step 7 (.step 29 (.close 19))))))) (.step 19 (.step 67 (.split 26 1 (.split 35 1 (.split 38 1 (.split 63 1 (.step 20 (.step 7 (.close 19))) (.step 18 (.step 20 (.step 3 (.close 66))))) (.step 7 (.close 19))) (.step 19 (.close 38))) (.step 7 (.step 29 (.close 19)))))))))) (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 7 (.step 11 (.step 17 (.step 5 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 5 (.step 7 (.step 17 (.close 5)))))))))) (.run (.step 7 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 29 (.step 7 (.close 38))))) (.step 3 (.close 29))) (.step 3 (.close 17))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734896959488⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.reuse 0) (.run (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 11 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 11 (.step 3 (.close 5))) (.step 3 (.close 7))) (.step 29 (.step 3 (.step 11 (.close 5))))) (.step 11 (.close 74))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 3 (.close 11))) (.step 5 (.close 11))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 11 (.close 7)))) (.step 5 (.step 7 (.step 11 (.step 3 (.step 29 (.step 66 (.close 69))))))))) (.step 8 (.step 5 (.close 11)))) (.step 3 (.step 5 (.step 29 (.step 23 (.step 11 (.step 66 (.step 39 (.close 67))))))))) (.step 5 (.step 9 (.step 29 (.step 38 (.step 11 (.close 38))))))) (.step 5 (.step 29 (.step 38 (.step 66 (.step 67 (.step 7 (.step 37 (.step 5 (.close 11)))))))))) (.step 3 (.step 7 (.close 11)))) (.step 9 (.step 29 (.close 11)))) (.step 8 (.close 11))) (.step 8 (.close 11))) (.step 8 (.close 11))) (.step 11 (.step 5 (.close 7)))) (.step 3 (.step 7 (.close 11))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734898008064⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 23 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.step 29 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 11 (.step 67 (.step 5 (.close 28))))) (.step 3 (.step 11 (.close 18)))))) (.step 3 (.step 29 (.step 5 (.close 74))))) (.step 23 (.step 66 (.close 5)))) (.step 3 (.step 5 (.step 45 (.step 41 (.close 60)))))) (.step 3 (.step 5 (.step 28 (.close 39))))) (.step 38 (.close 5))) (.step 3 (.step 5 (.step 28 (.step 37 (.close 67))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 5 (.close 17))) (.step 5 (.close 11)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case23
