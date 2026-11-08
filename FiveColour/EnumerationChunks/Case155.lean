module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case155
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
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
def root : Box := ⟨2147483648, 11567172211559764234668580634528507661192102188877448412909279591789098762427634150999950241442573495260979389306697593941239856227283863192606710112456825358476713971713110666691637269835265775428222001361177095916991021056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 3 (.step 15 (.close 37))) (.step 29 (.step 38 (.step 3 (.step 15 (.close 37)))))) (.step 3 (.step 7 (.step 37 (.close 38))))) (.step 7 (.step 37 (.close 38)))) (.step 7 (.step 67 (.close 3)))) (.step 7 (.split 16 0 (.split 17 0 (.step 3 (.step 37 (.close 5))) (.step 3 (.step 7 (.close 5)))) (.step 7 (.step 18 (.step 3 (.close 19))))))) (.step 7 (.step 37 (.close 38)))) (.step 7 (.split 14 0 (.split 16 0 (.step 3 (.step 43 (.step 3 (.step 41 (.close 5))))) (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 3 (.step 18 (.step 49 (.step 5 (.close 3)))))))) (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 30 0 (.step 3 (.step 5 (.step 17 (.close 37)))) (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 5)))) (.step 11 (.step 74 (.step 3 (.close 7))))) (.step 11 (.step 67 (.step 7 (.step 14 (.step 3 (.close 19))))))) (.step 3 (.step 7 (.close 17)))) (.step 11 (.step 23 (.step 69 (.step 60 (.split 16 0 (.step 5 (.close 3)) (.step 3 (.step 5 (.close 14)))))))))) (.split 74 1 (.split 2 0 (.split 10 0 (.step 29 (.split 14 0 (.step 75 (.step 69 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 69 (.step 75 (.close 3)))))) (.step 3 (.step 7 (.step 41 (.close 37))))) (.step 3 (.step 69 (.step 37 (.step 5 (.close 38)))))) (.step 29 (.step 40 (.close 69))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930440276761051891909598906447530463713519493061023221394449654500041625043738696340497667859955788528249253050871170586259357097619106631654530336078246457475109881641665291968272827743447547904⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.reuse 0) (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 30 0 (.step 74 (.close 3)) (.step 3 (.step 38 (.close 37)))) (.step 3 (.step 39 (.step 37 (.close 38))))) (.step 3 (.step 51 (.close 74)))) (.step 3 (.step 67 (.step 3 (.close 37))))) (.step 74 (.close 3))) (.step 74 (.step 3 (.close 5)))) (.step 11 (.step 69 (.step 74 (.close 3))))) (.step 29 (.step 69 (.step 74 (.close 3))))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 3 (.step 63 (.step 74 (.split 72 1 (.split 74 1 (.split 14 0 (.step 43 (.step 41 (.close 15))) (.step 3 (.step 18 (.close 19)))) (.step 3 (.step 18 (.step 19 (.close 20))))) (.step 3 (.step 48 (.step 15 (.close 39)))))))))) (.run (.step 67 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 30 0 (.split 34 0 (.step 67 (.close 3)) (.step 29 (.step 66 (.step 67 (.close 3))))) (.step 3 (.step 38 (.close 37)))) (.step 3 (.step 41 (.close 37)))) (.step 3 (.step 51 (.close 67)))) (.step 3 (.close 67))) (.step 67 (.close 3))) (.step 67 (.step 3 (.close 5)))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.step 3 (.step 21 (.close 41)))))) (.step 3 (.step 63 (.close 67))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087300938137600, 11567172216946143397859013993930444732269467538584617114490639080225807811346041912304525751659656106471084601940714227786059753040905701467378338727206513983525686130619545404463401128624695729041648723347209186699671240704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.step 7 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 43 0 (.step 48 (.step 37 (.close 39))) (.step 3 (.step 15 (.close 21)))) (.step 28 (.step 48 (.step 38 (.step 41 (.step 3 (.step 15 (.close 37)))))))) (.step 3 (.step 7 (.step 38 (.close 37))))) (.step 3 (.step 7 (.step 41 (.close 37))))) (.step 5 (.step 3 (.step 7 (.step 39 (.step 37 (.close 38))))))) (.step 5 (.step 7 (.step 18 (.step 38 (.step 37 (.close 39))))))) (.step 3 (.step 18 (.step 49 (.step 5 (.close 38)))))) (.step 3 (.step 7 (.step 41 (.close 37))))) (.step 5 (.step 3 (.step 41 (.close 37))))) (.step 5 (.step 14 (.close 18)))) (.step 5 (.step 29 (.step 75 (.step 59 (.step 3 (.step 15 (.close 37)))))))) (.step 51 (.step 63 (.close 74))))) (.step 3 (.step 18 (.step 22 (.step 15 (.step 26 (.step 15 (.close 21)))))))) (.step 18 (.step 50 (.step 51 (.step 63 (.step 67 (.close 3))))))) (.step 18 (.step 49 (.step 51 (.step 63 (.step 66 (.step 3 (.close 38)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737286641747790068547267634703068983761673689121194032714849164282093535467922156241548745609742920951099366940896919552⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.reuse 0) (.run (.step 67 (.split 65 1 (.split 67 1 (.step 66 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 3 (.step 21 (.close 38))) (.step 29 (.step 51 (.step 3 (.step 21 (.close 38)))))) (.step 29 (.close 66))) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 37 (.step 38 (.close 39))))) (.step 3 (.step 51 (.close 66)))) (.step 3 (.step 66 (.close 3)))) (.step 66 (.close 3))) (.step 66 (.step 3 (.step 5 (.close 3))))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.step 3 (.step 22 (.close 38))))))) (.step 3 (.close 66))) (.step 3 (.step 63 (.step 3 (.close 66)))))))) (.reuse 1)) (.run (.step 3 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 3 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 11 (.step 3 (.step 9 (.close 18))))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 3)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742737593739892338422769234585537292878935986526833035245421936363522755065976604435965316473705864170286950205518967638725890146304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 45 (.step 7 (.step 29 (.step 45 (.close 3))))) (.step 3 (.step 7 (.step 37 (.step 5 (.step 41 (.step 5 (.close 39)))))))) (.step 3 (.step 7 (.step 45 (.close 37))))) (.step 3 (.step 5 (.step 7 (.step 37 (.close 69)))))) (.step 29 (.step 69 (.step 74 (.split 2 0 (.split 10 0 (.step 69 (.step 74 (.close 3))) (.step 3 (.step 39 (.step 41 (.close 37))))) (.step 3 (.step 45 (.step 5 (.close 37))))))))) (.step 3 (.step 45 (.step 39 (.step 48 (.step 15 (.close 69))))))) (.step 29 (.step 67 (.step 69 (.split 65 1 (.split 2 0 (.split 10 0 (.step 69 (.step 67 (.close 3))) (.step 3 (.close 45))) (.step 3 (.step 45 (.step 5 (.close 37))))) (.step 3 (.step 45 (.step 15 (.step 39 (.step 21 (.step 26 (.close 67))))))))))))) (.step 3 (.step 29 (.step 66 (.step 69 (.split 65 1 (.split 2 0 (.split 10 0 (.step 69 (.split 14 0 (.split 30 0 (.step 66 (.close 3)) (.step 3 (.step 37 (.close 38)))) (.step 3 (.close 37)))) (.step 3 (.step 37 (.step 41 (.close 39))))) (.step 3 (.step 37 (.close 45)))) (.step 3 (.step 15 (.step 45 (.step 39 (.step 21 (.step 26 (.close 66))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644176027133314815090541416196855640227476367031450846147727846624038270050427217275566309871855402221740693464525307904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.step 7 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 43 0 (.step 48 (.step 37 (.close 39))) (.step 3 (.step 15 (.close 21)))) (.step 28 (.step 38 (.close 3)))) (.step 3 (.step 7 (.close 38)))) (.step 3 (.step 7 (.step 38 (.step 37 (.close 39)))))) (.step 5 (.step 3 (.step 7 (.step 38 (.step 37 (.close 39))))))) (.step 5 (.step 7 (.step 18 (.step 38 (.step 37 (.close 39))))))) (.step 3 (.step 18 (.step 49 (.step 5 (.close 38)))))) (.step 3 (.step 7 (.step 38 (.step 37 (.close 39)))))) (.step 5 (.step 3 (.step 38 (.step 37 (.close 39)))))) (.step 5 (.step 14 (.close 18)))) (.step 5 (.step 29 (.step 38 (.step 75 (.split 2 0 (.split 10 0 (.step 48 (.step 41 (.step 3 (.close 37)))) (.step 3 (.step 41 (.close 37)))) (.step 3 (.step 5 (.close 41))))))))) (.step 63 (.step 67 (.step 74 (.step 3 (.close 38))))))) (.step 3 (.step 18 (.step 21 (.step 38 (.close 48)))))) (.step 18 (.step 50 (.step 63 (.close 67))))) (.step 18 (.step 49 (.step 63 (.step 66 (.step 3 (.step 38 (.step 3 (.step 39 (.close 41)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318958202479088358270709877171335232098032849823173032808119584862781413030760546304⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 28 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 59 (.step 43 (.step 5 (.step 38 (.close 41))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 38 (.close 41))))))) (.step 5 (.step 38 (.step 41 (.close 5))))) (.step 5 (.step 22 (.step 51 (.step 59 (.close 5)))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 18 (.step 21 (.step 22 (.step 15 (.step 26 (.step 15 (.close 38))))))))) (.step 5 (.step 18 (.step 21 (.step 41 (.step 5 (.step 49 (.close 67)))))))) (.step 5 (.step 18 (.step 49 (.step 51 (.step 63 (.step 41 (.step 59 (.close 66)))))))))))) (.run (.step 3 (.step 7 (.close 18))))) (.run (.step 3 (.step 7 (.step 10 (.step 3 (.close 18))))))) (.run (.step 7 (.step 28 (.step 41 (.step 45 (.step 60 (.split 63 1 (.split 64 1 (.split 65 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 41 (.step 7 (.step 39 (.step 3 (.step 15 (.close 37)))))) (.step 3 (.step 5 (.step 37 (.step 38 (.step 39 (.close 41))))))) (.step 3 (.step 7 (.step 38 (.step 41 (.step 37 (.close 39))))))) (.step 3 (.step 5 (.step 38 (.close 41))))) (.step 3 (.step 21 (.step 26 (.step 41 (.step 15 (.close 39))))))) (.step 21 (.step 38 (.step 41 (.step 5 (.step 37 (.close 60))))))) (.step 37 (.step 38 (.step 48 (.step 49 (.step 60 (.step 41 (.step 39 (.step 3 (.step 41 (.close 66))))))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737286641750138611130041467930958464358463026148569715263757484152800826439454365266663354053206619949484135643928854528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 65 0 (.split 72 1 (.split 10 0 (.step 39 (.close 3)) (.step 7 (.close 39))) (.step 29 (.step 39 (.close 3)))) (.step 3 (.step 7 (.close 39)))) (.step 3 (.step 7 (.step 37 (.step 5 (.close 39)))))) (.step 3 (.step 7 (.step 39 (.close 5))))) (.step 3 (.step 5 (.step 7 (.step 37 (.close 69)))))) (.step 29 (.step 74 (.close 3)))) (.step 3 (.close 39))) (.step 29 (.step 67 (.step 74 (.step 75 (.split 65 1 (.split 2 0 (.split 10 0 (.step 51 (.close 67)) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 39 (.close 5)))) (.step 3 (.close 39))))))))) (.step 3 (.step 29 (.step 66 (.step 74 (.step 75 (.split 65 1 (.split 2 0 (.split 10 0 (.step 51 (.step 37 (.step 3 (.step 21 (.close 38))))) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 37 (.step 5 (.step 38 (.close 39)))))) (.step 3 (.step 15 (.step 21 (.step 26 (.close 39)))))))))))) (.step 7 (.step 22 (.step 28 (.step 39 (.step 51 (.step 39 (.step 3 (.close 5))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747539506464040819618197042042523069565058848287641251583283861166181733792481280⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 39 (.split 65 1 (.split 74 1 (.split 71 1 (.split 63 1 (.step 39 (.step 29 (.split 2 0 (.split 10 0 (.split 14 0 (.step 39 (.close 3)) (.step 3 (.step 37 (.close 39)))) (.step 3 (.step 7 (.close 39)))) (.step 3 (.step 39 (.close 5)))))) (.step 29 (.step 37 (.step 39 (.step 51 (.step 45 (.step 39 (.close 66)))))))) (.step 29 (.step 39 (.step 37 (.step 66 (.step 37 (.close 67))))))) (.step 3 (.step 5 (.step 7 (.step 45 (.step 66 (.step 37 (.step 67 (.step 37 (.close 74)))))))))) (.step 3 (.step 39 (.close 66)))))))) (.run (.step 7 (.step 28 (.step 39 (.step 41 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.step 39 (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 5 (.step 38 (.step 39 (.close 5))))) (.step 3 (.step 21 (.step 22 (.step 38 (.step 15 (.close 39))))))) (.step 5 (.step 21 (.step 38 (.step 41 (.step 5 (.step 37 (.close 67)))))))) (.step 5 (.step 37 (.step 38 (.step 48 (.step 49 (.step 51 (.close 66))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835224385310455621613479736642841593404837384607365323166260658404445771163729736391353879719291859479035904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.step 29 (.split 14 0 (.split 16 0 (.split 34 0 (.split 36 0 (.step 3 (.step 21 (.close 38))) (.step 38 (.close 3))) (.step 38 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 7 (.close 38)))) (.step 3 (.step 38 (.step 3 (.close 19)))))) (.step 3 (.step 7 (.close 38)))) (.step 3 (.close 38))) (.step 29 (.step 40 (.step 69 (.step 3 (.split 2 0 (.step 38 (.step 3 (.close 19))) (.step 3 (.close 5)))))))) (.step 29 (.close 38))) (.step 29 (.step 38 (.step 74 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 7 (.step 3 (.close 38))))))) (.step 3 (.close 38))) (.step 29 (.step 38 (.step 67 (.step 3 (.step 21 (.close 38))))))) (.step 29 (.step 38 (.step 66 (.step 3 (.step 22 (.close 38))))))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 48 (.step 38 (.step 50 (.step 74 (.split 63 1 (.step 41 (.split 2 0 (.step 48 (.step 59 (.step 3 (.close 5)))) (.step 3 (.step 5 (.close 37))))) (.step 37 (.step 38 (.step 3 (.close 5)))))))))))))) (.step 3 (.step 40 (.step 9 (.step 38 (.step 51 (.step 3 (.close 7)))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 7 (.close 22)))))) (.step 3 (.step 5 (.step 29 (.step 38 (.close 3)))))) (.step 7 (.step 29 (.step 38 (.step 7 (.close 39)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644173564507927542675335390934653591809055830116190720178956597090350039592805599663694967660375417295390636321883029504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 65 0 (.split 72 1 (.split 22 0 (.split 17 0 (.split 10 0 (.step 37 (.close 3)) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 15 (.step 21 (.close 37)))))) (.step 3 (.step 7 (.close 37)))) (.step 3 (.step 7 (.close 37)))) (.step 3 (.step 5 (.step 7 (.step 37 (.step 17 (.step 39 (.step 45 (.close 66))))))))) (.step 29 (.step 66 (.step 74 (.step 75 (.split 2 0 (.split 14 0 (.split 30 0 (.step 74 (.close 3)) (.step 3 (.close 37))) (.step 3 (.close 37))) (.step 3 (.close 37)))))))) (.step 3 (.step 15 (.step 37 (.close 74))))) (.step 29 (.step 66 (.step 67 (.step 75 (.split 65 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 51 0 (.step 37 (.close 3)) (.step 3 (.step 21 (.step 26 (.close 37))))) (.step 3 (.close 37))) (.step 3 (.close 37))) (.step 3 (.close 37))) (.step 3 (.close 37))) (.step 3 (.close 37))))))))) (.step 3 (.step 29 (.step 66 (.close 3))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484390543665374500016598876400483047532636392355374405984766998021950786964903988280530243658906302367662080⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 7 (.step 28 (.step 37 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 2 0 (.split 14 0 (.step 59 (.step 5 (.close 37))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 5 (.close 37)))) (.step 5 (.step 22 (.step 37 (.step 3 (.close 5)))))) (.step 3 (.step 22 (.step 15 (.step 21 (.close 26)))))) (.step 5 (.step 41 (.step 48 (.step 49 (.step 50 (.step 51 (.step 59 (.step 37 (.step 3 (.step 45 (.step 59 (.close 66))))))))))))) (.step 5 (.step 15 (.step 37 (.close 66)))))))))) (.run (.step 3 (.close 7)))) (.run (.step 3 (.close 7)))) (.run (.step 7 (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.split 14 0 (.step 45 (.step 29 (.step 39 (.step 66 (.step 45 (.close 3)))))) (.step 3 (.step 7 (.step 37 (.close 67))))) (.step 15 (.step 37 (.close 66)))) (.step 3 (.step 5 (.step 7 (.step 45 (.step 17 (.step 66 (.close 67)))))))) (.step 3 (.step 15 (.step 37 (.close 67))))))))) (.run (.step 7 (.step 28 (.step 37 (.step 41 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 2 0 (.split 14 0 (.step 41 (.step 5 (.step 7 (.step 15 (.close 37))))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 5 (.close 37)))) (.step 5 (.step 37 (.step 3 (.close 5))))) (.step 3 (.step 21 (.close 37)))) (.step 5 (.step 21 (.step 38 (.step 41 (.step 5 (.step 37 (.close 66)))))))) (.step 5 (.step 15 (.step 37 (.close 66)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117561194662240718867263952059482985591741365906680560360121837269549056⟩
def references : Fin 6 → Box := ![Part3.root, Part4.root, Part6.root, Part8.root, Part9.root, Part11.root]
def proof : Chunks.Proof 6 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 1) (.run (.step 7 (.step 28 (.step 45 (.step 60 (.split 63 1 (.split 64 1 (.step 59 (.split 65 1 (.step 45 (.step 39 (.step 48 (.step 45 (.step 3 (.step 5 (.close 37))))))) (.step 3 (.step 22 (.step 15 (.close 21)))))) (.step 41 (.step 48 (.step 50 (.step 51 (.step 60 (.step 5 (.step 59 (.close 37))))))))) (.step 37 (.step 48 (.step 49 (.step 51 (.step 60 (.step 59 (.step 45 (.step 41 (.step 50 (.step 59 (.close 66)))))))))))))))))) (.run (.step 3 (.close 7)))) (.run (.step 3 (.close 7))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.split 35 1 (.split 36 1 (.reuse 5) (.run (.step 7 (.step 37 (.split 63 1 (.split 65 1 (.split 74 1 (.step 39 (.step 29 (.step 74 (.step 37 (.close 3))))) (.step 3 (.step 5 (.step 7 (.step 37 (.step 17 (.step 39 (.step 66 (.close 67))))))))) (.step 3 (.step 37 (.close 39)))) (.step 15 (.step 37 (.close 66)))))))) (.run (.step 7 (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 3 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67)))) (.step 3 (.step 50 (.close 66)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415782251118747925924318658468228206969145901906245189632⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 35 0 (.split 38 0 (.split 56 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.step 14 (.close 18))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.close 18)))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 69))))) (.step 11 (.step 69 (.step 74 (.step 18 (.split 10 0 (.step 69 (.close 74)) (.step 3 (.step 17 (.close 19))))))))) (.step 3 (.step 18 (.step 25 (.step 20 (.step 19 (.close 69))))))) (.step 11 (.step 67 (.step 3 (.step 5 (.step 18 (.close 25)))))))) (.step 3 (.step 11 (.step 66 (.step 18 (.step 69 (.split 65 1 (.split 10 0 (.step 69 (.step 66 (.close 3))) (.step 3 (.step 17 (.close 19)))) (.step 3 (.step 25 (.step 19 (.step 20 (.close 66)))))))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 69 (.step 40 (.step 38 (.step 74 (.step 7 (.step 19 (.close 20)))))))))))) (.step 3 (.close 7))) (.step 3 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117561194662240718868760529736109830179981939175382034172249512193556480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 35 0 (.split 38 0 (.split 56 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.step 14 (.close 18))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.close 18)))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 69))))) (.step 11 (.step 74 (.close 3)))) (.step 3 (.step 18 (.close 20)))) (.step 11 (.step 67 (.step 3 (.step 5 (.step 18 (.close 20)))))))) (.step 3 (.step 11 (.step 66 (.step 18 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.step 51 (.step 66 (.close 3))) (.step 3 (.close 17))) (.step 3 (.step 19 (.close 20))))))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 19 (.step 25 (.close 38)))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117561194662240718867265413561120316494659569591513276643141493202092032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 35 0 (.split 38 0 (.split 56 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.step 14 (.close 18))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.close 18)))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.step 20 (.step 25 (.step 38 (.close 67)))))))) (.step 11 (.step 67 (.step 18 (.step 74 (.close 3)))))) (.step 3 (.step 18 (.step 19 (.close 74))))) (.step 11 (.close 67)))) (.step 3 (.step 11 (.step 66 (.step 18 (.step 67 (.step 66 (.step 3 (.step 19 (.close 3)))))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 38 (.step 11 (.step 23 (.step 66 (.step 67 (.step 7 (.step 19 (.step 38 (.step 19 (.close 74))))))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157926190099809817245181741159241049237101740032⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 19 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 35 0 (.step 25 (.close 3)) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 18 (.step 20 (.step 67 (.step 25 (.step 3 (.close 38)))))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 67))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 4 (.step 7 (.step 19 (.step 38 (.close 66))))))))))) (.run (.step 7 (.step 19 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 35 0 (.step 20 (.close 3)) (.step 3 (.step 7 (.close 19)))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 18 (.step 20 (.step 19 (.step 38 (.close 67))))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 67))))) (.step 11 (.step 18 (.step 66 (.step 19 (.close 3)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 4 (.step 7 (.step 19 (.step 38 (.close 66)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985451500009097113648969864882206129343095384995383954180293130402997466740423525044084727580425000537945903139105275904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 30 0 (.step 3 (.step 5 (.step 17 (.close 37)))) (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 5)))) (.step 11 (.step 74 (.step 3 (.close 7))))) (.step 11 (.step 67 (.step 7 (.step 14 (.step 3 (.close 17))))))) (.step 3 (.step 7 (.close 17)))) (.step 11 (.step 23 (.split 16 0 (.step 49 (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 14 (.step 5 (.close 17)))))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 77 (.step 29 (.step 40 (.step 69 (.step 3 (.split 34 0 (.split 2 0 (.split 16 0 (.step 75 (.close 3)) (.step 3 (.close 17))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 37)))))))))) (.step 11 (.step 17 (.step 74 (.close 3))))) (.step 3 (.step 23 (.step 11 (.step 7 (.step 3 (.close 17))))))) (.step 3 (.step 17 (.step 23 (.close 17))))) (.step 11 (.step 17 (.step 67 (.close 3))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 5 (.step 16 (.step 5 (.step 17 (.step 14 (.close 49)))))))) (.step 3 (.step 23 (.step 11 (.step 17 (.step 51 (.step 3 (.close 7)))))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 66 (.step 67 (.step 69 (.step 23 (.step 17 (.step 74 (.step 7 (.step 37 (.close 39))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783747696425946565481807205443254425350070103763320832⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 16 (.step 49 (.step 58 (.step 5 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 51 (.step 66 (.step 67 (.step 74 (.step 7 (.step 5 (.step 37 (.step 17 (.step 39 (.close 45))))))))))))))) (.run (.step 3 (.step 5 (.step 66 (.step 67 (.step 74 (.step 75 (.split 36 1 (.split 42 1 (.split 74 1 (.step 29 (.step 40 (.split 16 0 (.split 10 0 (.split 17 0 (.split 2 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))))) (.step 11 (.step 17 (.close 5)))) (.step 3 (.step 5 (.step 37 (.close 38))))) (.step 3 (.step 5 (.step 37 (.close 38))))))))))))) (.run (.step 3 (.step 7 (.step 49 (.step 66 (.step 67 (.step 74 (.step 7 (.step 5 (.step 38 (.step 37 (.step 5 (.step 69 (.step 17 (.step 37 (.close 17))))))))))))))))) (.run (.step 3 (.step 7 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 17))) (.step 3 (.close 17)))))))) (.run (.step 7 (.step 11 (.split 35 1 (.split 38 1 (.step 17 (.split 56 1 (.step 17 (.step 3 (.step 7 (.close 5)))) (.step 3 (.step 5 (.step 14 (.close 17)))))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.close 17))))))) (.run (.step 7 (.step 11 (.step 74 (.step 17 (.step 25 (.split 35 1 (.split 38 1 (.step 17 (.step 3 (.step 7 (.close 5)))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.close 17))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384725409128087141633089759695863808⟩
def references : Fin 4 → Box := ![Part13.root, Part14.root, Part16.root, Part18.root]
def proof : Chunks.Proof 4 := (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.split 22 1 (.reuse 1) (.run (.step 7 (.split 35 1 (.step 20 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 36 0 (.step 25 (.close 3)) (.step 7 (.step 19 (.close 20)))) (.step 3 (.step 7 (.step 20 (.close 19))))) (.step 11 (.step 18 (.step 20 (.step 19 (.close 74)))))) (.step 3 (.step 18 (.close 20)))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 3 (.step 25 (.close 67)))))))) (.step 11 (.step 18 (.step 66 (.step 74 (.step 25 (.close 3))))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 19 (.step 25 (.step 66 (.step 20 (.step 25 (.step 38 (.close 74))))))))))))))) (.reuse 2)) (.split 16 1 (.reuse 3) (.run (.step 7 (.step 11 (.step 19 (.step 67 (.step 17 (.split 35 1 (.split 56 1 (.step 17 (.step 3 (.step 7 (.close 5)))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.close 17)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part16.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2149580800, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.step 63 (.split 63 1 (.split 64 1 (.split 71 1 (.step 5 (.step 3 (.step 23 (.step 77 (.split 72 1 (.step 5 (.step 49 (.step 3 (.step 5 (.close 37))))) (.step 3 (.step 5 (.step 37 (.close 39))))))))) (.step 11 (.step 23 (.step 74 (.step 3 (.close 5)))))) (.step 11 (.step 23 (.step 67 (.step 3 (.step 5 (.close 41))))))) (.step 11 (.step 23 (.step 66 (.step 5 (.close 14))))))) (.step 5 (.step 18 (.step 5 (.close 66))))) (.step 3 (.step 5 (.step 60 (.step 45 (.step 37 (.step 39 (.step 41 (.close 66))))))))) (.step 5 (.step 18 (.step 41 (.close 66))))) (.step 3 (.step 5 (.step 39 (.step 5 (.step 39 (.step 41 (.step 39 (.close 66))))))))) (.step 3 (.step 5 (.step 38 (.step 5 (.step 41 (.step 66 (.step 5 (.close 67))))))))) (.step 3 (.step 5 (.step 37 (.step 5 (.step 38 (.step 37 (.step 41 (.step 37 (.step 66 (.close 67))))))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.step 18 (.close 20))))) (.step 3 (.step 5 (.step 18 (.close 19))))) (.step 5 (.close 17)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419608248117562879658907415783749157927583896384726676778687369862491256400117760⟩
def references : Fin 2 → Box := ![Part19.root, Part20.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66)))) (.step 3 (.step 49 (.close 66)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 38))) (.step 3 (.close 38))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 17 (.step 3 (.close 7))))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part21.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case155

namespace FiveColour.Packed.EnumerationChunks.Projected.Case155
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 42 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 42 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 42 0).upper i := by decide +kernel
lemma budget_model : (⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 42), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 42) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 42 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 42 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 42) (Archive.root 42) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 42 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 42 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case155

namespace FiveColour.Packed.EnumerationChunks.Case155
def root : Box := Archive.root 42
def families : Fin 78 → List Cut := Enumeration.families 42
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case155.original_covered points
end FiveColour.Packed.EnumerationChunks.Case155
