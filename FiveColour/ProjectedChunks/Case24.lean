module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case24
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402377030679424704311071747478046313602911991503685419008⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593704327342213348339, 5789228615357111146520048038021683988773733487122101869605338720869906162805958987122173504434281850008071622175991935381017825153590590481063666660227604324706233660950604329370748855691173985301545264301300140783538537472, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930440276761051891909598906447530463713519493061023221394449654500041625043738696340497667859955788528249253050871170588068608491952172185147826976838995017682453392042299105084797577867090198528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 7 (.step 15 (.close 28))) (.step 7 (.step 43 (.step 3 (.step 5 (.close 28)))))) (.step 7 (.step 3 (.step 5 (.step 3 (.close 28)))))) (.step 7 (.step 11 (.step 3 (.step 23 (.step 69 (.step 5 (.close 3)))))))) (.step 29 (.step 69 (.step 75 (.step 3 (.close 5)))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 65 0 (.split 34 0 (.step 3 (.step 21 (.close 28))) (.step 29 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 43 (.step 3 (.step 28 (.close 37)))))) (.step 3 (.close 74))) (.step 3 (.step 18 (.step 5 (.step 28 (.close 37)))))) (.step 11 (.step 69 (.close 74)))) (.step 29 (.step 69 (.close 74))))) (.step 3 (.step 7 (.close 3)))) (.step 3 (.step 63 (.step 3 (.step 66 (.step 3 (.close 19))))))) (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 65 0 (.split 34 0 (.step 3 (.step 21 (.close 28))) (.step 29 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 41 (.close 3)))) (.step 3 (.close 67))) (.step 3 (.step 18 (.step 5 (.step 28 (.close 37)))))) (.step 11 (.close 67))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.step 63 (.step 3 (.step 66 (.step 3 (.close 19)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168678327626737286641747790068547267634703068983761673690930445427047914717775390176228670716448892256010376734067624117064539570176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.reuse 0) (.run (.step 3 (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 65 0 (.split 34 0 (.step 3 (.step 21 (.close 28))) (.step 29 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 43 (.step 3 (.step 28 (.close 37)))))) (.step 3 (.step 37 (.close 5)))) (.step 3 (.step 18 (.step 5 (.step 28 (.close 37)))))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 63 (.step 3 (.close 66))))))))) (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 10 0 (.step 28 (.split 16 0 (.step 51 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 3 (.step 7 (.close 37))))))) (.step 3 (.step 7 (.step 28 (.close 37))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 37)))))) (.step 28 (.step 75 (.step 59 (.close 3)))))) (.step 51 (.step 63 (.close 74)))) (.step 3 (.step 5 (.step 18 (.step 22 (.step 15 (.close 21))))))) (.step 50 (.step 51 (.step 63 (.close 67)))))) (.step 18 (.step 49 (.step 51 (.step 63 (.step 66 (.close 3))))))))) (.run (.step 3 (.split 56 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 3 (.split 51 1 (.split 56 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 10)))) (.step 3 (.step 7 (.close 3)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318958204288339752603775430664631872858781410030516543208753397979306163154403196928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 10 0 (.step 28 (.split 16 0 (.split 14 0 (.step 3 (.step 15 (.close 37))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 5 (.step 3 (.step 7 (.close 37))))))) (.step 3 (.step 7 (.step 28 (.close 37))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 37)))))) (.step 28 (.step 38 (.step 48 (.step 41 (.close 3))))))) (.step 63 (.step 67 (.step 5 (.step 28 (.step 59 (.step 5 (.step 38 (.step 3 (.close 5)))))))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 28 (.step 15 (.step 22 (.step 15 (.close 26)))))))))) (.step 50 (.step 63 (.close 67))))) (.step 18 (.step 49 (.step 63 (.step 66 (.step 3 (.close 28))))))) (.step 28 (.step 5 (.step 41 (.step 51 (.step 18 (.step 41 (.step 22 (.step 5 (.step 37 (.close 41))))))))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 10)))) (.step 7 (.step 28 (.step 41 (.step 5 (.step 41 (.step 45 (.step 60 (.step 41 (.step 3 (.close 15))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915747541315715435152683750535339163830313619055631151652217096977690931857435131904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 2 0 (.split 14 0 (.step 39 (.step 29 (.step 39 (.close 3)))) (.step 3 (.step 7 (.step 29 (.step 37 (.step 5 (.close 38))))))) (.step 3 (.step 7 (.step 28 (.close 39))))) (.step 29 (.step 51 (.close 66)))) (.step 3 (.step 5 (.step 11 (.step 23 (.step 66 (.step 7 (.step 17 (.step 37 (.close 39)))))))))) (.step 29 (.step 69 (.step 74 (.step 75 (.close 3)))))) (.step 3 (.step 29 (.close 39)))) (.step 22 (.step 5 (.step 28 (.step 39 (.step 5 (.step 22 (.step 5 (.step 37 (.close 39)))))))))) (.step 39 (.step 3 (.step 29 (.step 37 (.step 39 (.close 66))))))) (.step 28 (.step 39 (.step 41 (.step 5 (.step 39 (.step 41 (.step 3 (.step 5 (.step 3 (.close 21)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835224385310455621613479736642843402656231717672918816462901419153005978507240137025166996244041983121686528⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 2 0 (.split 14 0 (.step 45 (.step 7 (.step 29 (.step 3 (.step 21 (.close 38)))))) (.step 3 (.step 7 (.step 29 (.step 37 (.step 5 (.close 38))))))) (.step 3 (.step 7 (.step 28 (.close 45))))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 5 (.step 11 (.step 23 (.step 66 (.step 7 (.step 17 (.step 37 (.close 39)))))))))) (.step 29 (.step 69 (.step 45 (.close 3))))) (.step 3 (.step 29 (.step 45 (.step 15 (.step 39 (.step 21 (.step 26 (.step 66 (.close 67)))))))))) (.step 28 (.step 5 (.step 45 (.step 59 (.step 51 (.step 60 (.step 59 (.step 3 (.close 15))))))))))))) (.reuse 1)) (.reuse 2)) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 51 1 (.step 29 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.step 38 (.step 3 (.close 5))) (.step 3 (.step 38 (.close 3)))) (.step 74 (.close 3))) (.step 3 (.close 7))) (.step 3 (.step 15 (.close 38)))) (.step 3 (.step 67 (.close 3)))) (.step 3 (.step 66 (.close 3)))) (.step 3 (.step 5 (.step 38 (.step 48 (.step 38 (.step 3 (.close 5))))))))) (.step 3 (.close 7)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.close 3))))) (.step 3 (.step 5 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419610057368955527727794212163904712808043192935251766540493676884871960912199680⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 63 1 (.split 2 0 (.split 14 0 (.split 71 1 (.split 64 1 (.split 10 0 (.step 37 (.step 3 (.close 7))) (.step 7 (.step 28 (.close 37)))) (.step 29 (.step 37 (.close 3)))) (.step 29 (.step 66 (.step 3 (.step 39 (.step 3 (.step 21 (.close 37)))))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 28 (.close 37))))) (.step 29 (.step 37 (.close 66)))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 7 (.step 37 (.close 66)))))))) (.step 29 (.step 66 (.step 69 (.step 37 (.close 3)))))) (.step 3 (.step 15 (.step 29 (.step 21 (.close 37)))))) (.step 28 (.step 5 (.step 37 (.close 3))))) (.step 37 (.step 3 (.close 66)))) (.step 28 (.step 37 (.step 5 (.step 37 (.step 3 (.step 5 (.step 3 (.close 21))))))))) (.step 37 (.step 3 (.close 66)))) (.step 29 (.step 37 (.step 38 (.close 3)))))))) (.run (.step 3 (.step 7 (.split 35 1 (.split 38 1 (.split 56 1 (.step 3 (.close 7)) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 38)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402375532640245046339005679269495833202195402153530490880⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.step 29 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 74 1 (.split 71 1 (.step 7 (.step 5 (.close 3))) (.step 29 (.close 5))) (.step 5 (.close 14))) (.step 3 (.step 5 (.step 18 (.step 15 (.close 21)))))) (.step 29 (.step 5 (.step 18 (.close 5)))))) (.step 18 (.step 29 (.step 18 (.step 5 (.step 18 (.close 21)))))))) (.step 28 (.close 5))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 10)))) (.step 7 (.step 28 (.close 5)))) (.step 10 (.step 28 (.close 5)))) (.step 7 (.step 28 (.close 5)))) (.step 7 (.step 28 (.close 5)))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 7 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 11 (.step 18 (.step 69 (.step 3 (.close 19)))))) (.step 3 (.step 18 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 67 (.close 3))))) (.step 11 (.step 66 (.step 3 (.step 5 (.close 14)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 11 (.step 23 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20))))))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402377030679423310514496838046449367392290549484387041280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 17 1 (.step 67 (.split 22 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 71 1 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 11 (.step 18 (.step 67 (.step 3 (.close 19)))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 11 (.step 23 (.step 38 (.close 19)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 19 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 25 (.step 3 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.close 38))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5))))))))) (.step 19 (.step 67 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 19 (.step 20 (.step 3 (.step 7 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 3))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.close 38))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402377030679423310514496838046449367392290549484387041280⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.split 22 1 (.step 74 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 7 (.step 18 (.step 3 (.step 19 (.close 3))))) (.step 11 (.step 18 (.step 51 (.step 19 (.step 3 (.close 20))))))) (.step 11 (.step 18 (.step 51 (.close 66))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 14 (.close 18))))))) (.step 3 (.step 11 (.step 23 (.step 38 (.step 7 (.step 19 (.close 20)))))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 20 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 25 (.step 3 (.step 18 (.step 3 (.close 19))))) (.step 11 (.step 18 (.step 20 (.step 3 (.step 19 (.step 20 (.close 66)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 7 (.step 19 (.step 20 (.close 38)))))) (.step 3 (.step 5 (.step 7 (.step 18 (.close 5))))))))))) (.reuse 1))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835224385310455621613479736642843402656231717672918816462901419154399775082148300971512978636082505715810304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 65 1 (.split 67 1 (.split 2 0 (.split 10 0 (.step 67 (.split 63 1 (.split 71 1 (.split 72 1 (.step 7 (.step 11 (.step 17 (.step 3 (.step 23 (.split 16 0 (.step 3 (.close 5)) (.step 3 (.close 5)))))))) (.step 3 (.step 29 (.step 17 (.step 69 (.step 3 (.close 5))))))) (.step 11 (.step 17 (.step 3 (.step 23 (.close 74)))))) (.step 11 (.step 17 (.close 66))))) (.step 17 (.step 3 (.step 66 (.step 7 (.step 3 (.close 17))))))) (.step 11 (.step 17 (.step 23 (.step 66 (.step 67 (.step 49 (.step 3 (.step 5 (.close 3)))))))))) (.step 3 (.step 11 (.step 7 (.step 3 (.close 17)))))) (.step 3 (.step 17 (.step 23 (.close 17))))) (.step 3 (.step 5 (.step 14 (.close 17))))) (.step 3 (.step 23 (.step 11 (.step 3 (.close 17)))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 17 (.step 23 (.step 66 (.step 7 (.step 37 (.step 39 (.close 67)))))))))))) (.step 3 (.step 5 (.step 16 (.step 49 (.step 5 (.close 17))))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 5 (.step 17 (.step 23 (.step 66 (.step 7 (.step 37 (.step 39 (.close 67))))))))))))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 17 (.step 23 (.step 66 (.step 67 (.step 3 (.step 38 (.step 74 (.step 3 (.close 5)))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402377030679424704311071747478046313602911991503684370432⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 7 (.step 29 (.step 38 (.step 40 (.step 49 (.step 17 (.step 37 (.step 17 (.close 37))))))))))))) (.run (.step 3 (.step 7 (.step 3 (.close 17)))))) (.run (.step 3 (.step 5 (.step 16 (.step 29 (.step 5 (.step 14 (.close 17))))))))) (.run (.step 7 (.step 11 (.split 25 1 (.step 17 (.step 7 (.step 17 (.step 3 (.step 5 (.close 14)))))) (.step 3 (.step 5 (.step 14 (.close 17))))))))) (.run (.step 7 (.step 11 (.step 20 (.step 74 (.step 17 (.step 7 (.step 17 (.step 3 (.step 5 (.close 14)))))))))))) (.run (.step 7 (.step 11 (.step 19 (.step 67 (.step 17 (.step 7 (.step 17 (.step 3 (.step 5 (.close 14))))))))))))) (.run (.step 3 (.step 7 (.split 14 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 3 (.close 7)) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 38))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 17)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270419611866620351545790014402377030679424704311071747478046313602911991503685419008⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 38 1 (.step 5 (.step 3 (.step 23 (.step 5 (.step 67 (.step 3 (.step 5 (.close 37)))))))) (.step 5 (.close 3))) (.step 5 (.step 11 (.step 23 (.step 66 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 45 (.step 41 (.close 60)))))) (.step 3 (.step 5 (.step 28 (.step 5 (.close 39)))))) (.step 3 (.step 5 (.step 29 (.step 38 (.close 5)))))) (.step 3 (.step 5 (.step 28 (.step 37 (.step 5 (.close 38))))))) (.step 5 (.step 3 (.close 28)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 5 (.close 17))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case24
