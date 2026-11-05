module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case27
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539134298696058450022093553664⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨18740915245514456087283, 5789228615357111146520043253955950924962759905236944250816662429627930946143177890630323431728858874565283113377443026906005086448749057136295994626906708871240422740574967198931403751522663329691581331687037538719964857344, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567385983191639432196471305727407451091194415651837569843567242944100769407992952914006949000210854476979021228779850080573086583006165456748239587315580665856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.step 7 (.split 2 0 (.split 8 0 (.step 7 (.step 31 (.step 3 (.close 7)))) (.step 7 (.step 11 (.close 5)))) (.split 43 0 (.split 51 0 (.step 3 (.step 31 (.close 5))) (.step 3 (.close 4))) (.step 3 (.close 4))))) (.split 2 0 (.step 7 (.step 11 (.step 7 (.step 31 (.step 17 (.step 3 (.close 5))))))) (.step 11 (.step 3 (.step 23 (.close 5)))))) (.step 7 (.step 3 (.step 7 (.close 11))))) (.split 67 1 (.split 74 1 (.split 2 0 (.step 7 (.split 8 0 (.split 14 0 (.step 7 (.step 9 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 23 (.close 17)))) (.step 9 (.close 11)))) (.step 9 (.step 31 (.close 3)))) (.step 23 (.step 27 (.step 23 (.step 11 (.step 7 (.step 17 (.close 18)))))))) (.step 44 (.step 62 (.close 7))))) (.split 59 1 (.split 67 1 (.step 61 (.step 7 (.step 27 (.step 7 (.step 31 (.close 8)))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 44 (.step 31 (.close 61)))))) (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.step 7 (.step 5 (.step 58 (.step 7 (.close 5)))))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 5 (.close 7)))))))) (.step 58 (.step 3 (.step 18 (.step 27 (.step 18 (.step 11 (.close 17)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325437709934763984976463317753067945134267705425704352055488528740100887631080829645871030694124989276119249056359776256⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 38 0 (.step 54 (.step 7 (.close 3))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 54 (.step 3 (.close 7)))) (.step 3 (.step 54 (.step 7 (.step 11 (.step 27 (.close 44))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))) (.run (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 58 1 (.split 74 1 (.step 7 (.split 8 0 (.split 14 0 (.step 7 (.step 9 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 23 (.close 17)))) (.step 9 (.close 11)))) (.step 23 (.step 27 (.step 23 (.step 11 (.step 7 (.step 17 (.close 18)))))))) (.step 27 (.step 61 (.step 3 (.close 7))))) (.step 53 (.close 7))) (.step 53 (.step 3 (.close 4)))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21))))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 5 (.step 27 (.step 58 (.step 61 (.step 62 (.step 23 (.step 9 (.step 31 (.step 3 (.close 5))))))))))) (.step 53 (.step 7 (.close 3))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124637754454866599742667208477479669281747166464941147623927673303286082742289138718013218330990636454927333114025038975074304⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 58 1 (.split 74 1 (.step 7 (.split 8 0 (.split 14 0 (.step 7 (.step 9 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 23 (.close 17)))) (.step 9 (.close 11)))) (.step 23 (.step 27 (.step 23 (.step 11 (.step 7 (.step 17 (.close 18)))))))) (.step 27 (.step 34 (.step 31 (.close 61))))) (.step 52 (.close 7))) (.step 52 (.step 3 (.close 4)))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21))))))))))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 5 (.step 27 (.step 58 (.step 61 (.step 62 (.step 23 (.step 9 (.step 31 (.step 3 (.close 5))))))))))) (.step 52 (.step 7 (.close 3)))) (.step 52 (.step 4 (.step 7 (.close 5))))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 46 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 46 (.split 55 1 (.step 54 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 27 (.step 7 (.close 46))))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587391331344527548635684740417839958361117533164347150556155299522165568621435004333067930763641126974483316878716436480⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 7 (.step 5 (.step 31 (.close 45)))))))) (.run (.step 5 (.step 31 (.step 43 (.step 61 (.split 43 1 (.step 5 (.split 49 1 (.split 50 1 (.split 51 1 (.step 5 (.step 7 (.step 9 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 5 (.step 7 (.step 9 (.step 7 (.step 23 (.step 7 (.close 44)))))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 31 (.step 44 (.close 52))))))))) (.step 3 (.step 7 (.close 9)))))))))) (.run (.step 42 (.step 31 (.step 61 (.split 40 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.step 42 (.step 7 (.step 27 (.step 31 (.close 11))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 42 (.step 3 (.close 7))))) (.step 3 (.step 27 (.step 42 (.step 3 (.close 5)))))) (.step 3 (.step 42 (.step 54 (.step 27 (.step 7 (.step 11 (.step 34 (.close 42))))))))) (.step 27 (.step 42 (.close 53)))) (.step 27 (.step 34 (.step 42 (.close 52))))) (.step 3 (.step 11 (.step 9 (.close 27))))) (.step 5 (.step 27 (.step 31 (.close 42))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263365873409341085735697933769687675427237195480366161210624950577931933845752598745756280095635995997765632⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 43 (.step 58 (.split 39 1 (.split 42 1 (.step 42 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.step 7 (.step 5 (.step 42 (.step 5 (.close 7)))))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 5 (.close 7)))))) (.step 5 (.step 43 (.step 7 (.step 58 (.step 3 (.close 7))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 31 (.step 42 (.step 7 (.step 9 (.close 21))))))) (.step 5 (.step 31 (.step 42 (.step 16 (.step 9 (.step 52 (.close 7)))))))) (.step 3 (.step 7 (.close 9))))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 16 (.close 22))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.step 8 (.close 18)))))))))))) (.run (.step 7 (.step 31 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 31 (.step 58 (.split 49 1 (.step 5 (.step 31 (.step 5 (.step 16 (.close 21))))) (.step 9 (.step 22 (.step 23 (.step 5 (.step 31 (.step 16 (.close 21)))))))))))) (.step 5 (.step 31 (.close 36)))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 22 (.step 16 (.step 21 (.step 16 (.close 39))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330582609369522246042763919360⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.close 8)))) (.step 7 (.step 11 (.step 17 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.step 19 (.close 17))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 44 (.step 48 (.step 11 (.step 17 (.step 23 (.step 25 (.step 31 (.step 19 (.step 44 (.step 42 (.close 52))))))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.step 7 (.close 5)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828111988598038931588921903851310843334373717687926784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.close 8)))) (.step 7 (.step 11 (.step 17 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.step 19 (.close 17))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 48 (.step 11 (.step 17 (.step 23 (.step 52 (.step 7 (.close 19))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.step 7 (.close 5)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 25 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.step 20 (.step 4 (.step 7 (.close 18)))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 20 (.step 19 (.step 20 (.step 25 (.close 52)))))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 20 (.step 7 (.close 42)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450099676262491840107536143559617393373620469760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.close 8)))) (.step 7 (.step 11 (.step 17 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.close 17))))))) (.step 4 (.step 42 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 44 (.close 52)))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.close 42)))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 52)))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))) (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 52)))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980350648051554646572046290503333979047116705306052319228403264102907815559954432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 38 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 34 0 (.step 11 (.step 7 (.step 17 (.close 5)))) (.step 17 (.step 7 (.step 5 (.step 9 (.close 17)))))) (.step 11 (.step 17 (.step 3 (.step 23 (.close 5)))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 23 (.step 44 (.step 23 (.step 11 (.close 17))))))) (.step 3 (.step 5 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 3 (.step 5 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.close 61))))))) (.step 5 (.step 18 (.step 11 (.step 17 (.step 5 (.step 23 (.close 17)))))))) (.step 3 (.step 7 (.step 27 (.step 18 (.step 3 (.step 11 (.step 17 (.step 34 (.close 44)))))))))) (.step 31 (.step 27 (.step 48 (.step 61 (.split 51 1 (.step 77 (.step 55 (.step 23 (.step 55 (.step 11 (.step 7 (.step 17 (.step 7 (.step 17 (.step 34 (.close 44))))))))))) (.step 3 (.step 7 (.step 17 (.step 34 (.step 11 (.close 44)))))))))))) (.step 17 (.step 31 (.step 27 (.step 34 (.step 31 (.step 34 (.step 3 (.close 44))))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.close 27))))))) (.step 5 (.step 7 (.step 11 (.step 17 (.close 23)))))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 23 (.close 17)))))))) (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.close 3))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066748271482489542009433896214593536⟩
def references : Fin 5 → Box := ![Part4.root, Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 5 := (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 31 (.step 37 (.step 9 (.step 23 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37))))))))))) (.step 5 (.step 31 (.close 34)))) (.step 5 (.step 7 (.step 5 (.step 16 (.step 21 (.close 37))))))) (.step 31 (.split 49 1 (.step 45 (.step 7 (.step 5 (.step 31 (.step 37 (.step 5 (.close 9))))))) (.step 7 (.step 16 (.step 9 (.step 17 (.step 31 (.close 37))))))))))))) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.step 7 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19)))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 4) (.run (.step 5 (.step 7 (.step 23 (.step 11 (.step 7 (.step 17 (.close 31))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 7 (.step 5 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.close 7)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 7 (.step 18 (.close 7)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 7 (.step 18 (.close 19)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2417851639229260496896000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263365873409341085735697933769687675427237195480366161210624950577931933845752598746965205915250625173520384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 11 (.split 55 1 (.split 58 1 (.split 2 1 (.split 38 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 2 0 (.step 7 (.step 11 (.step 5 (.close 7)))) (.step 8 (.step 5 (.close 3)))) (.step 3 (.step 7 (.close 11)))) (.step 9 (.step 27 (.step 23 (.step 9 (.step 11 (.close 3))))))) (.step 3 (.step 5 (.step 3 (.close 9))))) (.step 3 (.step 5 (.step 3 (.close 9))))) (.step 3 (.step 5 (.step 3 (.close 9))))) (.step 11 (.step 5 (.step 3 (.step 7 (.close 44)))))) (.step 3 (.step 5 (.step 18 (.step 11 (.step 5 (.close 9)))))))) (.step 3 (.step 7 (.step 11 (.step 3 (.step 11 (.close 44))))))) (.step 9 (.step 11 (.step 23 (.step 27 (.step 31 (.step 48 (.step 55 (.step 61 (.split 51 1 (.step 23 (.step 9 (.step 11 (.step 7 (.close 44))))) (.step 3 (.step 7 (.step 11 (.close 44)))))))))))))) (.step 9 (.step 11 (.step 23 (.step 27 (.step 31 (.step 48 (.step 55 (.step 61 (.split 50 1 (.split 51 1 (.step 23 (.step 9 (.step 11 (.step 7 (.close 44))))) (.step 3 (.step 7 (.step 11 (.step 34 (.close 44)))))) (.step 9 (.step 34 (.close 52))))))))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.close 27))))))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 31 (.step 11 (.close 42))))) (.step 5 (.step 7 (.step 9 (.step 11 (.step 7 (.step 9 (.close 11)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539134298696058450022093553664⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 2 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 38 1 (.split 39 1 (.step 7 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19)))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7))) (.step 3 (.step 17 (.step 3 (.step 7 (.step 11 (.close 17)))))))))))) (.run (.step 3 (.step 5 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.step 5 (.step 3 (.step 5 (.step 23 (.step 21 (.step 42 (.step 3 (.step 9 (.step 17 (.close 21)))))))))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 5 (.step 11 (.step 17 (.step 23 (.close 17)))))))))) (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 1) (.run (.step 5 (.step 7 (.step 9 (.step 31 (.step 7 (.step 5 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11)))))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 5 (.close 7))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case27
