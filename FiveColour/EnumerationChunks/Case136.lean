module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case136
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734898008064⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
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
def root : Box := ⟨2147483648, 11567172211559764234668580634528507661192102188877448412909279591789098762427634150999950241442573495260979389306697593941239856227283863192606711965130253155535840748848870805698162922155020425677247841608340837156239966208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 26 0 (.step 7 (.step 15 (.close 37))) (.step 29 (.step 3 (.close 7)))) (.step 7 (.split 16 0 (.step 3 (.step 29 (.step 5 (.close 37)))) (.step 3 (.step 7 (.step 14 (.step 3 (.close 19)))))))) (.split 14 0 (.step 7 (.split 16 0 (.step 3 (.step 29 (.step 5 (.close 37)))) (.step 3 (.step 7 (.step 8 (.step 3 (.close 11))))))) (.split 16 0 (.split 17 0 (.step 3 (.split 10 0 (.split 22 0 (.step 3 (.step 5 (.step 11 (.close 29)))) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 7 (.step 3 (.step 8 (.step 3 (.close 11)))))) (.step 11 (.close 3))))) (.split 8 0 (.step 7 (.step 3 (.step 43 (.split 14 0 (.step 3 (.step 28 (.step 5 (.close 37)))) (.step 5 (.step 3 (.step 5 (.close 28)))))))) (.step 3 (.step 47 (.step 11 (.step 3 (.close 5))))))) (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 3 (.step 69 (.step 7 (.step 3 (.step 5 (.close 11)))))) (.step 7 (.step 3 (.step 8 (.step 3 (.close 11)))))) (.step 11 (.step 3 (.step 7 (.step 18 (.step 3 (.close 19))))))) (.step 11 (.step 77 (.step 3 (.step 5 (.close 17)))))) (.step 3 (.step 11 (.step 3 (.close 7))))) (.step 11 (.step 3 (.step 23 (.step 69 (.step 5 (.close 3)))))))) (.step 29 (.split 74 1 (.split 2 0 (.split 8 0 (.step 75 (.step 3 (.step 15 (.close 37)))) (.step 3 (.step 69 (.step 75 (.close 3))))) (.step 3 (.step 69 (.step 5 (.close 37))))) (.step 40 (.close 69))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644173564507927540435590648756849381251615402221174239116437876991460643699342151019657746729240312161676884289524858880⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.reuse 0) (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 10 0 (.step 74 (.close 3)) (.step 3 (.step 29 (.step 37 (.close 38))))) (.step 3 (.close 74))) (.step 74 (.close 3))) (.step 74 (.step 3 (.close 5)))) (.step 11 (.step 69 (.close 74)))) (.step 29 (.step 69 (.step 74 (.close 3))))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 3 (.step 63 (.step 74 (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 15 (.close 29))))))))) (.run (.step 67 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 17 0 (.split 22 0 (.split 10 0 (.step 67 (.step 3 (.step 21 (.close 28)))) (.step 3 (.step 29 (.step 37 (.close 38))))) (.step 3 (.close 67))) (.step 3 (.step 51 (.close 67)))) (.step 67 (.close 3))) (.step 67 (.step 3 (.close 5)))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.step 63 (.close 67)))))))) (.run (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 10 0 (.split 16 0 (.split 30 0 (.step 66 (.close 3)) (.step 3 (.step 29 (.step 37 (.close 38))))) (.step 3 (.close 66))) (.step 3 (.step 29 (.step 37 (.close 38))))) (.step 3 (.close 66))) (.step 66 (.close 3))) (.step 66 (.step 3 (.step 5 (.close 3))))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 63 (.close 66))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737286641747790068547267634703068983761675541794621829773975941417853674474447808561303395858768761198263108180145864704⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.split 14 0 (.step 28 (.split 17 0 (.split 22 0 (.step 59 (.close 3)) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 5 (.step 3 (.step 7 (.step 37 (.close 38))))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 37)))))) (.step 3 (.step 7 (.step 28 (.step 37 (.close 38)))))) (.step 3 (.step 18 (.step 51 (.step 47 (.step 5 (.step 18 (.step 5 (.close 37))))))))) (.step 5 (.step 3 (.step 28 (.step 37 (.close 38)))))) (.step 5 (.step 8 (.close 14)))) (.step 5 (.step 29 (.step 75 (.step 59 (.step 3 (.close 5))))))) (.step 51 (.step 63 (.close 74)))) (.step 3 (.step 5 (.step 18 (.step 22 (.step 15 (.step 26 (.step 15 (.close 21))))))))) (.step 50 (.step 51 (.step 63 (.step 67 (.close 3))))))) (.step 18 (.step 49 (.step 51 (.step 63 (.step 66 (.step 3 (.close 28)))))))))) (.run (.step 3 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 3 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 3)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985451500009097113648969864882206129343097237668811751239419907538757605746947783567264469665504494802717603855760097280⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.reuse 0) (.run (.step 7 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 45 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 29 (.step 37 (.step 5 (.close 38))))))) (.step 3 (.step 7 (.step 29 (.step 45 (.step 5 (.step 11 (.close 37)))))))) (.step 3 (.step 7 (.step 28 (.step 45 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.close 39))))))))) (.step 29 (.step 69 (.step 74 (.close 3))))) (.step 3 (.step 29 (.step 45 (.close 69))))) (.step 29 (.step 67 (.step 69 (.step 67 (.step 3 (.close 21))))))) (.step 29 (.step 66 (.step 69 (.step 66 (.close 3)))))) (.step 28 (.step 45 (.step 60 (.split 63 1 (.split 64 1 (.step 59 (.step 74 (.step 45 (.close 3)))) (.step 41 (.step 48 (.step 50 (.step 51 (.step 5 (.step 59 (.close 5)))))))) (.step 37 (.step 48 (.step 49 (.step 51 (.step 60 (.step 59 (.step 3 (.step 41 (.step 3 (.step 50 (.step 59 (.close 66))))))))))))))))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617114490639080225807811346041912304525751659656106471084604403339615060714703808345707726354203397363646184675229654523643308827537499520113592682315493901600478353169580032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.split 14 0 (.step 28 (.split 16 0 (.split 30 0 (.split 35 0 (.step 3 (.step 15 (.close 37))) (.step 38 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 5 (.step 3 (.step 7 (.step 37 (.close 38))))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 37)))))) (.step 3 (.step 7 (.step 28 (.step 37 (.close 38)))))) (.step 3 (.step 18 (.step 67 (.step 3 (.step 5 (.step 28 (.close 37)))))))) (.step 5 (.step 3 (.step 28 (.step 37 (.close 38)))))) (.step 5 (.step 8 (.close 14)))) (.step 5 (.step 29 (.step 38 (.step 75 (.split 2 0 (.step 48 (.step 41 (.step 3 (.close 5)))) (.step 3 (.step 5 (.step 37 (.close 39)))))))))) (.step 63 (.step 67 (.step 74 (.step 3 (.close 28)))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 28 (.step 38 (.step 15 (.step 22 (.step 15 (.close 26))))))))))) (.step 50 (.step 63 (.close 67))))) (.step 18 (.step 49 (.step 63 (.step 66 (.step 3 (.step 28 (.step 3 (.close 38))))))))) (.step 28 (.split 63 1 (.split 64 1 (.step 7 (.split 65 1 (.step 5 (.step 59 (.step 41 (.step 59 (.close 5))))) (.step 10 (.step 18 (.step 21 (.step 22 (.step 15 (.close 26)))))))) (.step 5 (.step 18 (.step 21 (.step 41 (.close 5)))))) (.step 5 (.step 18 (.step 49 (.step 51 (.step 63 (.step 41 (.step 59 (.step 5 (.close 66)))))))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293342263910718354990169001164060476514587604172414573788277780310014122472368623988278146588842240184620248741910866797321318825984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 39 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 29 (.step 37 (.step 5 (.close 38))))))) (.step 3 (.step 7 (.step 29 (.step 39 (.step 5 (.close 11))))))) (.step 3 (.step 7 (.step 28 (.step 39 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.close 39))))))))) (.step 29 (.step 51 (.close 74)))) (.step 3 (.step 29 (.close 39)))) (.step 29 (.step 51 (.step 67 (.step 3 (.close 39)))))) (.step 29 (.step 51 (.step 66 (.step 3 (.close 26)))))) (.step 22 (.step 5 (.step 28 (.step 39 (.step 51 (.step 39 (.step 3 (.close 5))))))))) (.step 39 (.split 65 1 (.split 74 1 (.split 71 1 (.split 63 1 (.step 39 (.step 29 (.split 2 0 (.split 10 0 (.split 14 0 (.step 39 (.close 3)) (.step 3 (.step 37 (.close 39)))) (.step 3 (.step 7 (.close 39)))) (.step 3 (.step 39 (.close 5)))))) (.step 29 (.step 37 (.step 39 (.step 51 (.step 45 (.step 3 (.step 39 (.close 66))))))))) (.step 29 (.step 39 (.step 11 (.step 37 (.step 66 (.close 67))))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 45 (.step 37 (.step 66 (.step 37 (.close 67))))))))))) (.step 3 (.step 29 (.close 39)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915749392179891837878744974177802662076090711168042291500609124108329922973041426432⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 36 1 (.split 38 1 (.reuse 0) (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 1) (.run (.step 3 (.step 7 (.close 18))))) (.run (.step 3 (.step 7 (.step 10 (.close 18)))))) (.run (.step 7 (.step 28 (.step 41 (.step 45 (.step 60 (.split 63 1 (.split 64 1 (.split 65 1 (.split 2 0 (.split 71 1 (.step 41 (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 38 (.step 39 (.step 48 (.step 59 (.step 5 (.close 37))))))) (.step 3 (.step 5 (.step 38 (.step 37 (.step 39 (.step 37 (.close 41)))))))) (.step 3 (.step 21 (.step 26 (.step 15 (.step 22 (.step 15 (.close 38)))))))) (.step 21 (.step 38 (.step 41 (.close 5))))) (.step 37 (.step 38 (.step 48 (.step 49 (.step 60 (.step 41 (.step 3 (.step 39 (.step 3 (.step 41 (.close 66)))))))))))))))))))) (.step 7 (.split 38 1 (.reuse 2) (.run (.step 28 (.step 39 (.step 41 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 39 (.step 3 (.close 5)))) (.step 3 (.step 21 (.step 22 (.step 15 (.step 38 (.step 15 (.close 26)))))))) (.step 5 (.step 21 (.step 38 (.step 41 (.close 5)))))) (.step 5 (.step 37 (.step 38 (.step 48 (.step 49 (.step 51 (.close 66)))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835224385310455621613479736644694266832634443734142458926399664930098090918379985417194126883033098727981056⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.split 71 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.split 14 0 (.step 38 (.close 3)) (.step 3 (.close 38))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 3 (.step 38 (.step 3 (.close 11))))) (.step 3 (.close 38))) (.step 40 (.step 69 (.step 3 (.step 11 (.step 3 (.step 5 (.close 17)))))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 29 (.close 38)))) (.step 29 (.step 3 (.step 67 (.close 3))))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 48 (.step 50 (.step 74 (.split 63 1 (.step 41 (.step 3 (.close 5))) (.step 37 (.step 38 (.step 3 (.close 5)))))))))))))) (.step 3 (.step 40 (.step 9 (.step 29 (.step 38 (.close 3))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.step 29 (.step 38 (.close 3)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.step 7 (.close 22)))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293342263910718354990166652623717447423537518902375226731818848905586859649732566232206603480780917447356945988293359521889894006784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 72 1 (.split 14 0 (.split 10 0 (.split 16 0 (.step 37 (.step 3 (.close 7))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 29 (.close 37)))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 29 (.step 37 (.close 3)))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 28 (.close 37))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 17 (.close 37)))))))) (.step 29 (.step 66 (.step 74 (.close 3))))) (.step 3 (.step 15 (.step 29 (.close 37))))) (.step 29 (.step 66 (.step 67 (.step 37 (.step 3 (.close 21))))))) (.step 29 (.step 66 (.close 3)))) (.step 28 (.step 37 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 37 (.step 3 (.close 5)))) (.step 3 (.step 15 (.step 22 (.close 21))))) (.step 5 (.step 41 (.step 48 (.step 49 (.step 50 (.step 51 (.step 5 (.step 59 (.close 5)))))))))) (.step 5 (.step 15 (.step 37 (.step 5 (.close 66))))))))) (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.split 14 0 (.step 45 (.step 29 (.step 39 (.step 66 (.step 45 (.close 3)))))) (.step 3 (.step 7 (.step 29 (.step 37 (.close 11)))))) (.step 15 (.step 29 (.step 37 (.close 66))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.step 39 (.step 45 (.close 66))))))))))) (.step 3 (.step 15 (.step 29 (.close 37))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270421460921545358253789017854627402958585135305346391614932520807523863076518494208⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 28 (.step 37 (.step 41 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 37 (.step 3 (.close 5)))) (.step 3 (.step 15 (.step 21 (.step 22 (.step 26 (.close 37))))))) (.step 5 (.step 21 (.step 38 (.step 41 (.close 5)))))) (.step 5 (.step 15 (.step 37 (.step 5 (.close 66))))))))))) (.run (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.step 39 (.step 29 (.step 74 (.step 37 (.close 3))))) (.step 15 (.step 29 (.step 37 (.close 66))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.step 39 (.close 66)))))))))) (.step 3 (.step 15 (.step 29 (.close 37)))))))) (.run (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 38 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687302529131799230563827958966278678537653769755568373760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 8 (.step 5 (.close 14)))))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 69 (.step 3 (.step 23 (.close 74)))))) (.step 3 (.step 11 (.step 18 (.step 19 (.step 20 (.step 19 (.step 25 (.close 69))))))))) (.step 11 (.step 67 (.step 3 (.step 5 (.close 18)))))) (.step 11 (.step 66 (.step 3 (.step 5 (.step 18 (.close 25))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 66 (.step 67 (.step 69 (.step 40 (.step 29 (.step 11 (.step 38 (.step 3 (.step 19 (.close 20)))))))))))) (.step 3 (.step 4 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 67 (.step 20 (.step 19 (.close 69))))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293339556225470192594530735144529567208692095416033122727620287703714302878562235904564766789474046695068791642428964447767606853632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 8 (.step 5 (.close 14)))))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 51 (.close 74)))) (.step 3 (.step 11 (.step 18 (.step 19 (.close 20)))))) (.step 11 (.step 51 (.step 67 (.step 3 (.step 5 (.close 18))))))) (.step 11 (.step 51 (.step 66 (.step 3 (.step 5 (.step 18 (.close 20)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 7 (.step 11 (.step 19 (.step 25 (.close 29)))))))))) (.step 3 (.step 4 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 20 (.step 67 (.step 20 (.close 74)))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304025709475857408416199539547380011465897430492381184⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 17 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 38 1 (.split 43 1 (.split 51 1 (.step 29 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.step 74 (.step 3 (.step 11 (.close 19))))) (.step 3 (.close 7))) (.step 3 (.close 29))) (.step 29 (.step 3 (.step 11 (.step 23 (.step 19 (.close 67))))))) (.step 29 (.step 3 (.step 23 (.step 11 (.close 66))))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 5 (.step 28 (.close 29))))) (.step 3 (.step 7 (.step 29 (.step 3 (.close 7))))))))) (.reuse 1)) (.step 7 (.split 22 1 (.reuse 2) (.run (.step 25 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 36 0 (.step 25 (.close 3)) (.step 7 (.step 11 (.close 19)))) (.step 3 (.step 7 (.step 11 (.step 20 (.close 19)))))) (.step 11 (.step 18 (.step 20 (.step 19 (.close 29)))))) (.step 3 (.step 11 (.step 18 (.step 19 (.close 20)))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 3 (.step 25 (.step 29 (.close 67))))))))) (.step 11 (.step 18 (.step 66 (.step 74 (.step 25 (.close 3))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 19 (.step 29 (.step 20 (.step 25 (.step 38 (.close 66))))))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 29 (.step 20 (.step 19 (.step 66 (.step 20 (.close 67))))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293339556225470192594530735144529567208692095416033122727620287703714302878562234409448591799960361372699207773671435339748615389184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 67 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 8 (.step 5 (.close 14)))))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.step 25 (.close 29)))))))) (.step 11 (.step 67 (.step 18 (.step 74 (.close 3)))))) (.step 3 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 66 (.step 3 (.step 5 (.step 18 (.close 19))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 38 (.step 11 (.step 23 (.step 29 (.step 38 (.step 19 (.close 66))))))))) (.step 3 (.step 4 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 19 (.step 66 (.step 19 (.step 20 (.step 67 (.close 69)))))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293339556225470192594530735144529567208692095416033122727620287705399299545259149396615280242899088289801529300080221119817591029760⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.step 19 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 35 0 (.step 25 (.close 3)) (.step 3 (.step 7 (.step 11 (.close 19))))) (.step 3 (.step 7 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 20 (.step 67 (.step 3 (.step 19 (.step 25 (.close 29))))))))) (.step 3 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 29 (.close 67)))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38)))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.step 19 (.close 67))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318960055152516155329836654307095371104559895939502591221091771092337194792603615232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 8 0 (.step 3 (.split 22 0 (.step 3 (.step 5 (.step 17 (.close 29)))) (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 5)))) (.step 11 (.step 3 (.step 7 (.step 14 (.step 3 (.close 17))))))) (.step 11 (.step 67 (.step 3 (.step 7 (.close 17)))))) (.step 3 (.step 11 (.step 3 (.close 7))))) (.step 29 (.step 40 (.step 69 (.step 3 (.step 11 (.step 75 (.close 3)))))))) (.step 11 (.step 3 (.step 23 (.split 72 1 (.step 49 (.step 5 (.close 3))) (.step 3 (.step 5 (.close 17)))))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 11 (.step 17 (.step 74 (.close 3))))) (.step 3 (.step 23 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 11 (.step 17 (.close 5))))) (.step 11 (.step 17 (.step 3 (.step 67 (.close 3)))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 14 (.close 49))))))) (.step 3 (.step 23 (.step 11 (.step 17 (.close 3)))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 66 (.step 67 (.step 69 (.step 23 (.step 11 (.step 17 (.step 7 (.step 29 (.step 17 (.step 37 (.close 39))))))))))))))) (.step 3 (.step 5 (.step 16 (.step 49 (.step 5 (.step 11 (.close 17)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687302529131800624360402867130225024520045810278162497536⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 7 (.step 51 (.step 66 (.step 67 (.step 74 (.step 5 (.step 7 (.step 29 (.step 17 (.step 37 (.step 11 (.step 17 (.close 39))))))))))))))))) (.run (.step 3 (.step 5 (.step 66 (.step 67 (.step 74 (.step 75 (.split 36 1 (.split 42 1 (.split 74 1 (.step 29 (.step 40 (.split 8 0 (.step 3 (.split 2 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 5)))) (.step 11 (.close 5))))) (.step 11 (.step 17 (.close 5)))) (.step 3 (.step 5 (.step 29 (.step 11 (.step 17 (.step 37 (.close 38)))))))) (.step 3 (.step 5 (.step 29 (.step 37 (.step 11 (.step 17 (.close 38)))))))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 49 (.step 66 (.step 67 (.step 74 (.step 7 (.step 5 (.step 17 (.step 29 (.step 37 (.step 11 (.close 17)))))))))))))))) (.run (.step 3 (.step 7 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.step 11 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 29 (.step 66 (.step 67 (.step 74 (.split 2 0 (.split 8 0 (.step 29 (.step 3 (.close 17))) (.step 11 (.close 5))) (.step 3 (.step 5 (.step 11 (.close 17))))))))))))) (.run (.step 7 (.step 11 (.step 17 (.split 26 1 (.split 35 1 (.split 38 1 (.step 17 (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.close 17))) (.step 3 (.close 17))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894025907178558710140957609019047936⟩
def references : Fin 3 → Box := ![Part12.root, Part14.root, Part16.root]
def proof : Chunks.Proof 3 := (.split 14 1 (.split 16 1 (.reuse 0) (.step 7 (.split 17 1 (.reuse 1) (.run (.step 19 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 35 0 (.step 20 (.close 3)) (.step 3 (.step 7 (.step 11 (.close 19))))) (.step 3 (.step 7 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 20 (.step 19 (.close 29)))))) (.step 3 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 29 (.close 67)))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38)))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.close 67))))))))))))))) (.split 16 1 (.split 17 1 (.reuse 2) (.run (.step 7 (.step 11 (.step 17 (.step 25 (.step 74 (.step 17 (.step 5 (.step 3 (.step 7 (.close 17)))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 19 (.step 67 (.step 17 (.step 5 (.step 3 (.step 7 (.close 17)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part14.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2417851639229260496896000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915749392179891837878744974177802662076090711168042291500610333034149537602216132608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 11 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 2 0 (.split 72 1 (.split 16 0 (.split 10 0 (.split 17 0 (.split 30 0 (.split 26 0 (.step 11 (.step 3 (.close 5))) (.step 9 (.step 29 (.close 3)))) (.step 3 (.step 11 (.close 3)))) (.step 11 (.close 3))) (.step 3 (.step 11 (.close 3)))) (.step 11 (.close 3))) (.step 9 (.step 29 (.step 69 (.step 3 (.step 11 (.close 5))))))) (.step 11 (.step 3 (.close 5)))) (.step 11 (.step 9 (.step 29 (.step 5 (.step 37 (.step 39 (.step 66 (.close 69))))))))) (.step 3 (.close 7))) (.step 3 (.close 11))) (.step 11 (.step 23 (.step 29 (.close 67))))) (.step 11 (.step 23 (.step 47 (.close 66))))) (.step 3 (.step 5 (.step 8 (.close 11)))))) (.step 3 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 29 (.step 23 (.step 11 (.step 3 (.step 66 (.step 67 (.step 37 (.step 39 (.step 37 (.close 69))))))))))))))) (.step 3 (.step 5 (.step 8 (.step 58 (.step 5 (.step 8 (.close 11)))))))) (.step 3 (.step 5 (.step 7 (.step 51 (.step 66 (.step 67 (.step 74 (.step 5 (.step 7 (.step 11 (.step 29 (.step 11 (.step 45 (.step 11 (.close 37)))))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734896959488⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 14 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 29 (.close 38))))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 17 (.step 3 (.close 7))))))))) (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 11 (.step 9 (.step 29 (.step 38 (.step 66 (.step 67 (.step 74 (.split 14 0 (.step 3 (.split 63 0 (.step 38 (.close 3)) (.step 11 (.step 5 (.close 37))))) (.step 11 (.close 5)))))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 29 (.step 38 (.step 37 (.step 5 (.step 11 (.close 37))))))))))))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.close 7))))))) (.run (.step 3 (.step 5 (.step 11 (.step 9 (.step 29 (.close 11)))))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 5 (.close 7))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423313594973156997912461687304027170978888535894027174830367864189973734898008064⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 23 (.step 5 (.split 42 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 5 (.step 3 (.step 11 (.step 23 (.step 75 (.step 5 (.step 66 (.step 5 (.close 14))))))))) (.step 11 (.step 23 (.step 74 (.step 3 (.close 5)))))) (.step 11 (.step 23 (.step 67 (.step 3 (.step 5 (.close 28))))))) (.step 11 (.step 23 (.step 66 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 28 (.step 60 (.step 37 (.step 39 (.step 37 (.close 41))))))))))) (.step 5 (.close 3))) (.step 3 (.step 5 (.step 28 (.step 39 (.step 5 (.close 41))))))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 5 (.step 11 (.step 41 (.close 66))))))))) (.step 3 (.step 5 (.step 28 (.step 37 (.step 5 (.step 38 (.close 41)))))))) (.step 3 (.step 5 (.step 28 (.step 11 (.close 29)))))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 3 (.step 5 (.step 8 (.step 18 (.close 19)))))) (.step 5 (.step 11 (.close 17)))) (.step 5 (.step 8 (.close 11)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part20.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case136

namespace FiveColour.Packed.EnumerationChunks.Projected.Case136
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 23 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 23 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 23 0).upper i := by decide +kernel
lemma budget_model : (⟨11593704327342179793651, 5789228615357111146520043253955950924962759905236944250816662429627930946143174768881773115736627492968050798482740711356931196351281104609431181736320982633118032348601960626826787145704805298534408245321323047477072364544, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 23), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11593704327342179793651, 5789228615357111146520043253955950924962759905236944250816662429627930946143174768881773115736627492968050798482740711356931196351281104609431181736320982633118032348601960626826787145704805298534408245321323047477072364544, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 23) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 23 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 23 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 23) (Archive.root 23) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 23 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 23 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case136

namespace FiveColour.Packed.EnumerationChunks.Case136
def root : Box := Archive.root 23
def families : Fin 78 → List Cut := Enumeration.families 23
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case136.original_covered points
end FiveColour.Packed.EnumerationChunks.Case136
