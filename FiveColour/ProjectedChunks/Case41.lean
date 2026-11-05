module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨2147483648, 11567172216946143397859013993925877836143429696690957734841830172388626264553774661463870461982142349876530018953991755048638417128470610741297576178948668392897731193656277674758524243286857886967305027018189953551200944128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 7 (.step 15 (.close 37))) (.step 7 (.split 16 0 (.step 3 (.step 5 (.close 37))) (.step 3 (.step 7 (.close 5)))))) (.step 7 (.close 37))) (.step 7 (.step 3 (.step 18 (.step 5 (.step 3 (.step 5 (.close 37)))))))) (.step 7 (.step 11 (.step 69 (.split 2 0 (.step 7 (.step 23 (.step 69 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 3 (.close 14))))))))) (.step 29 (.step 69 (.step 75 (.split 2 0 (.step 3 (.step 15 (.close 37))) (.step 3 (.step 5 (.close 37)))))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 65 0 (.split 34 0 (.step 3 (.step 21 (.close 38))) (.step 29 (.step 39 (.step 3 (.step 15 (.close 37)))))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 67 (.close 3)))) (.step 3 (.close 74))) (.step 3 (.close 74))) (.step 11 (.step 69 (.close 74)))) (.step 29 (.step 69 (.step 74 (.close 3)))))) (.step 3 (.step 7 (.close 3)))) (.step 3 (.step 63 (.step 3 (.step 74 (.close 3)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644173564507927540435590648756849381251613549547746442057311099855700504692816498699903096480214471914513143050275913728⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 17 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 34 0 (.step 3 (.step 21 (.close 38))) (.step 29 (.step 66 (.step 3 (.step 21 (.close 38)))))) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.close 67))) (.step 3 (.step 51 (.close 67)))) (.step 3 (.step 50 (.step 18 (.step 5 (.close 37)))))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.step 63 (.close 67)))))))) (.run (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 65 0 (.split 74 0 (.split 34 0 (.step 3 (.step 21 (.close 38))) (.step 29 (.step 37 (.close 3)))) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.close 66))) (.step 3 (.step 49 (.step 3 (.step 19 (.close 37)))))) (.step 3 (.step 49 (.step 43 (.close 66))))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 63 (.close 66))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737286641747790068547267634703068983761673689121194032714849164282093535467922156241548745609742920951099366940896919552⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 17 0 (.split 22 0 (.step 59 (.close 3)) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 5 (.step 3 (.step 7 (.step 37 (.close 38))))))) (.step 3 (.step 5 (.step 3 (.close 37))))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 3 (.step 5 (.step 3 (.step 37 (.close 38)))))) (.step 5 (.close 14))) (.step 5 (.step 29 (.step 75 (.step 59 (.close 3)))))) (.step 51 (.step 63 (.close 74)))) (.step 3 (.step 5 (.step 18 (.step 22 (.step 15 (.close 21))))))) (.step 50 (.step 51 (.step 63 (.close 67)))))) (.step 18 (.step 49 (.step 51 (.step 63 (.step 66 (.close 3))))))))) (.run (.step 3 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 3 (.split 51 1 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 3)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737289104373177343202218402143075242737536506604898436805265911050431300825532874817211959001383851258326917355146313728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 16 0 (.split 30 0 (.split 35 0 (.step 3 (.step 15 (.close 37))) (.step 38 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 5 (.step 3 (.step 7 (.step 37 (.close 38))))))) (.step 3 (.step 5 (.step 3 (.close 37))))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 3 (.step 5 (.step 3 (.step 37 (.close 38)))))) (.step 5 (.close 14))) (.step 5 (.step 29 (.step 38 (.step 75 (.step 41 (.close 3))))))) (.step 63 (.step 67 (.step 5 (.step 74 (.close 3)))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 38 (.step 15 (.step 22 (.step 15 (.close 26)))))))))) (.step 50 (.step 63 (.close 67))))) (.step 18 (.step 49 (.step 63 (.step 66 (.step 3 (.close 38))))))) (.step 28 (.split 63 1 (.split 64 1 (.step 7 (.step 59 (.step 5 (.step 3 (.step 18 (.step 38 (.close 41))))))) (.step 5 (.step 18 (.step 21 (.step 41 (.close 5)))))) (.step 5 (.step 18 (.step 49 (.step 41 (.step 51 (.step 41 (.step 22 (.step 41 (.step 5 (.step 59 (.close 66)))))))))))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 10 (.close 18))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747539506464040819618197042042523069565058848287641251583283861166181733792481280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 39 (.close 3)) (.step 7 (.step 37 (.close 38)))) (.step 29 (.step 51 (.step 39 (.close 3))))) (.step 29 (.step 51 (.close 67)))) (.step 29 (.step 51 (.step 66 (.close 3))))) (.step 7 (.step 3 (.close 39)))) (.step 3 (.step 7 (.step 39 (.step 49 (.step 39 (.step 5 (.step 50 (.step 60 (.close 66)))))))))) (.step 3 (.step 5 (.step 23 (.step 66 (.step 67 (.step 7 (.step 17 (.step 37 (.close 39)))))))))) (.step 29 (.step 74 (.step 75 (.step 3 (.close 7)))))) (.step 3 (.step 39 (.step 15 (.step 48 (.step 57 (.step 39 (.close 66)))))))) (.step 22 (.step 5 (.step 28 (.step 39 (.step 51 (.step 39 (.close 3)))))))) (.step 39 (.split 65 1 (.split 71 1 (.step 45 (.step 29 (.step 37 (.step 39 (.step 3 (.step 39 (.step 5 (.step 45 (.close 66))))))))) (.step 29 (.step 39 (.step 37 (.step 66 (.step 37 (.close 67))))))) (.step 3 (.close 39))))) (.step 28 (.step 39 (.step 41 (.split 63 1 (.split 64 1 (.step 39 (.step 3 (.step 5 (.step 3 (.close 21))))) (.step 5 (.step 21 (.step 38 (.step 39 (.step 5 (.step 37 (.close 39)))))))) (.step 5 (.step 37 (.step 38 (.step 39 (.step 41 (.step 3 (.step 21 (.step 3 (.step 39 (.close 66)))))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747539506464040819618197042042523069565058848287641251583283861166181733792481280⟩
def references : Fin 3 → Box := ![Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 63 1 (.split 64 1 (.split 71 1 (.step 45 (.step 3 (.close 5))) (.step 29 (.step 69 (.close 74)))) (.step 29 (.step 67 (.step 3 (.step 21 (.close 38)))))) (.step 29 (.step 66 (.step 69 (.step 37 (.step 3 (.step 21 (.close 38)))))))) (.step 7 (.step 3 (.step 45 (.step 37 (.step 39 (.step 41 (.step 49 (.close 66))))))))) (.step 3 (.step 7 (.step 45 (.step 49 (.step 45 (.step 50 (.step 60 (.step 37 (.step 39 (.close 41))))))))))) (.step 3 (.step 5 (.step 23 (.step 66 (.step 67 (.step 7 (.step 17 (.step 37 (.close 39)))))))))) (.step 29 (.step 69 (.step 45 (.close 3))))) (.step 3 (.step 48 (.step 66 (.step 45 (.step 39 (.step 15 (.step 67 (.step 15 (.step 45 (.close 69))))))))))) (.step 28 (.step 45 (.step 60 (.split 63 1 (.step 59 (.step 74 (.step 45 (.close 3)))) (.step 37 (.step 48 (.step 49 (.step 51 (.step 59 (.step 45 (.step 41 (.step 50 (.step 59 (.close 60)))))))))))))))))) (.split 42 1 (.reuse 1) (.run (.step 7 (.step 28 (.step 41 (.step 45 (.step 60 (.split 63 1 (.step 41 (.step 60 (.step 41 (.step 3 (.step 7 (.close 15)))))) (.step 37 (.step 38 (.step 41 (.step 48 (.step 45 (.step 39 (.step 41 (.close 60))))))))))))))))) (.reuse 2))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197799417690294085122161849115506252862557815795558393546734955600916552299260596785131086151680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 16 0 (.step 37 (.close 3)) (.step 7 (.close 37))) (.step 3 (.step 7 (.close 37)))) (.step 29 (.step 66 (.step 74 (.close 3))))) (.step 29 (.step 66 (.step 67 (.step 3 (.step 21 (.close 37))))))) (.step 29 (.step 66 (.close 3)))) (.step 7 (.step 3 (.close 37)))) (.step 3 (.step 7 (.step 37 (.step 5 (.step 50 (.step 60 (.close 66)))))))) (.step 3 (.step 5 (.step 23 (.step 17 (.step 3 (.step 37 (.step 66 (.step 37 (.step 39 (.close 45))))))))))) (.step 29 (.step 66 (.step 75 (.step 3 (.close 7)))))) (.step 3 (.step 15 (.step 37 (.close 67))))) (.step 28 (.step 37 (.split 63 1 (.split 64 1 (.step 37 (.step 3 (.close 5))) (.step 5 (.step 37 (.step 3 (.step 5 (.step 3 (.close 21))))))) (.step 5 (.step 15 (.step 37 (.close 66)))))))) (.step 37 (.split 63 1 (.step 45 (.step 29 (.step 39 (.step 66 (.step 45 (.step 3 (.close 17))))))) (.step 15 (.step 37 (.close 66)))))) (.step 28 (.step 37 (.step 41 (.split 63 1 (.split 64 1 (.step 37 (.step 3 (.close 5))) (.step 5 (.step 21 (.step 37 (.step 3 (.close 5)))))) (.step 5 (.step 15 (.step 37 (.close 66))))))))) (.step 37 (.split 63 1 (.step 39 (.step 3 (.step 37 (.step 5 (.step 17 (.step 39 (.close 66))))))) (.step 15 (.step 37 (.close 66)))))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117561194662240718867263952059482985591741365906680560360121837269549056⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.split 71 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 38 (.close 3)) (.step 3 (.close 38))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 3 (.close 38))) (.step 3 (.step 69 (.step 3 (.step 5 (.close 17)))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.close 38))) (.step 3 (.step 29 (.step 67 (.close 3))))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 48 (.step 50 (.step 74 (.step 41 (.step 59 (.step 3 (.close 5))))))))))))) (.step 3 (.step 40 (.step 9 (.step 38 (.close 3)))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.step 29 (.step 38 (.close 3)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.step 7 (.close 22))))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 38 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783747696424552768906899041496908442958029581169197056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 22 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 35 0 (.split 38 0 (.step 7 (.step 11 (.close 20))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 51 (.step 20 (.step 3 (.step 19 (.close 69)))))))) (.step 3 (.step 18 (.step 19 (.close 20))))) (.step 11 (.step 51 (.step 67 (.step 3 (.step 5 (.close 18))))))) (.step 11 (.step 51 (.step 66 (.step 3 (.step 5 (.step 18 (.close 20)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 11 (.step 23 (.step 38 (.step 66 (.step 67 (.step 7 (.step 19 (.step 20 (.close 69))))))))))) (.step 20 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 20 (.step 3 (.step 7 (.step 19 (.step 20 (.close 19)))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 3 (.close 67))))))) (.step 11 (.step 18 (.step 66 (.step 20 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.step 20 (.step 25 (.step 38 (.close 66))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293339556225470192594530735144529567208692095416033119022273432111281045990987629118602228938259578989303478828511713251968267845632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.step 67 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 35 0 (.split 38 0 (.step 7 (.step 11 (.split 36 0 (.step 19 (.close 3)) (.step 3 (.step 7 (.close 19)))))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 18 (.step 67 (.step 74 (.close 3)))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 66 (.step 3 (.step 5 (.step 18 (.close 19))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 11 (.step 23 (.step 38 (.step 19 (.close 66)))))))) (.step 19 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 25 (.step 3 (.step 18 (.step 3 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 67))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.close 38))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157926190099809817245181741159241049237101740032⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 35 0 (.split 38 0 (.step 7 (.step 11 (.step 25 (.close 3)))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.step 5 (.close 18))))) (.step 3 (.step 7 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 69 (.step 3 (.close 19)))))) (.step 3 (.step 18 (.step 19 (.step 20 (.step 19 (.step 25 (.close 69)))))))) (.step 11 (.step 67 (.step 3 (.step 5 (.close 18)))))) (.step 11 (.step 66 (.step 3 (.step 5 (.step 18 (.close 25))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 11 (.step 23 (.step 38 (.step 66 (.step 67 (.step 7 (.step 19 (.step 20 (.close 69)))))))))))))) (.reuse 1)) (.step 7 (.split 17 1 (.reuse 2) (.run (.step 19 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 20 (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 67))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.close 38))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747539506464040819618197042042523069566452644862549415529629843558222256386605056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 2 0 (.split 10 0 (.split 71 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 30 0 (.step 3 (.step 5 (.close 17))) (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 5)))) (.step 7 (.step 11 (.step 17 (.close 3))))) (.step 11 (.step 17 (.step 7 (.step 17 (.close 3)))))) (.step 29 (.step 40 (.step 69 (.step 3 (.step 75 (.close 3))))))) (.step 11 (.step 17 (.close 74)))) (.step 3 (.step 17 (.step 3 (.step 7 (.step 3 (.close 17))))))) (.step 11 (.step 17 (.step 23 (.step 74 (.step 3 (.step 49 (.step 5 (.close 3))))))))) (.step 3 (.close 7))) (.step 3 (.step 17 (.close 5)))) (.step 11 (.step 17 (.step 3 (.step 67 (.close 3)))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 5 (.step 17 (.step 14 (.close 49)))))) (.step 3 (.step 23 (.step 11 (.step 17 (.close 3)))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 23 (.step 17 (.step 66 (.step 67 (.step 7 (.step 37 (.step 39 (.close 69)))))))))))) (.step 3 (.step 5 (.step 16 (.step 49 (.step 5 (.close 17))))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 40 (.step 51 (.step 5 (.step 66 (.step 67 (.step 74 (.step 7 (.step 17 (.step 37 (.step 17 (.close 39)))))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256399069184⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 29 (.step 38 (.step 40 (.step 66 (.step 67 (.step 74 (.step 77 (.step 3 (.split 2 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 5))))))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 29 (.step 38 (.step 40 (.step 49 (.step 17 (.step 66 (.step 7 (.step 37 (.step 17 (.step 37 (.close 67)))))))))))))))) (.run (.step 3 (.step 7 (.step 67 (.step 7 (.step 3 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.split 35 1 (.split 38 1 (.step 17 (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 20 (.step 74 (.step 17 (.step 3 (.step 5 (.step 3 (.close 7)))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 19 (.step 67 (.step 17 (.step 3 (.step 5 (.step 3 (.close 7))))))))))))) (.run (.step 3 (.step 7 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 66 (.step 7 (.step 3 (.close 38)))))) (.step 3 (.step 17 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 23 (.step 5 (.split 42 1 (.split 63 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 11 (.step 23 (.step 5 (.step 67 (.step 5 (.step 66 (.step 5 (.close 14))))))))) (.step 3 (.step 14 (.step 18 (.close 49))))))) (.step 3 (.step 5 (.step 69 (.step 5 (.step 67 (.step 5 (.close 37)))))))) (.step 11 (.step 23 (.step 66 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 60 (.step 37 (.step 39 (.step 37 (.close 41)))))))))) (.step 5 (.close 3))) (.step 3 (.step 5 (.step 39 (.step 5 (.close 41)))))) (.step 3 (.step 5 (.step 38 (.step 5 (.step 41 (.close 66))))))) (.step 3 (.step 5 (.step 37 (.step 5 (.step 38 (.close 41))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.step 18 (.close 19))))) (.step 5 (.close 17))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case41
