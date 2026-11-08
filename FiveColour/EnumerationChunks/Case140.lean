module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case140
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539134298696058450022093553664⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨18740915245514456087283, 5789228615357111146520043253955950924962759905236944250816662429627930946143177890630323431728858874565283113377443026906005086448749057136295994626906708871240422740574967198931403751522663329691581331687037538719964857344, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041327803083408248821065973113499751072541486551933211826000204806937246280638885736841612676857054114931776890062681900579070861809449093613395627876076468447475847027738197393145856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 74 1 (.split 2 0 (.step 7 (.split 8 0 (.split 14 0 (.step 7 (.step 31 (.step 9 (.step 5 (.close 7))))) (.step 7 (.step 31 (.step 17 (.step 3 (.close 5)))))) (.split 16 0 (.split 17 0 (.step 7 (.step 27 (.step 7 (.step 5 (.close 9))))) (.step 7 (.close 8))) (.step 7 (.step 11 (.close 3)))))) (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 5 (.step 7 (.close 5))) (.step 7 (.step 3 (.close 5)))) (.step 3 (.step 31 (.close 5)))) (.step 3 (.close 7))) (.split 10 0 (.split 30 0 (.split 43 0 (.split 14 0 (.step 3 (.step 31 (.close 5))) (.step 8 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.split 2 0 (.split 10 0 (.split 8 0 (.step 7 (.split 14 0 (.step 7 (.step 31 (.close 18))) (.step 11 (.step 7 (.step 17 (.step 31 (.step 18 (.step 7 (.close 5))))))))) (.step 11 (.close 3))) (.step 7 (.close 11))) (.step 11 (.step 23 (.step 5 (.close 3)))))) (.split 74 1 (.split 8 0 (.split 14 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 17)))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996181697849386896196714841039050974949388621395211881485546001430878483625598014686544627594783950641610033639266988040911494917869020425652700929681112074845085454303232⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.split 67 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.close 3)) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 17 (.close 18))))))) (.step 7 (.close 3))) (.step 9 (.step 31 (.step 9 (.step 11 (.close 3)))))) (.split 8 0 (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5)))) (.step 9 (.close 3)))) (.step 27 (.step 23 (.step 44 (.step 7 (.step 8 (.close 5))))))) (.step 44 (.step 62 (.close 7)))))) (.run (.split 59 1 (.split 67 1 (.split 10 0 (.step 61 (.step 27 (.step 31 (.step 44 (.step 5 (.step 3 (.close 7))))))) (.step 31 (.step 27 (.step 7 (.step 11 (.step 7 (.close 17))))))) (.step 3 (.step 61 (.split 8 0 (.step 70 (.close 7)) (.step 7 (.step 11 (.step 27 (.step 34 (.close 44))))))))) (.step 27 (.step 44 (.step 61 (.step 5 (.close 7)))))))) (.run (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.split 8 0 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.step 7 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 7)))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 5 (.step 3 (.step 8 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.close 16)))))))))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325437709934763984976463317753067945134267705425704352055488528740100887631080829645871030694124989276119249056359776256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.step 53 (.close 3)) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 17)))) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 17 (.close 18))))))) (.step 7 (.close 3))) (.step 9 (.step 31 (.step 9 (.step 11 (.close 3)))))) (.step 27 (.step 23 (.step 55 (.step 23 (.step 11 (.step 31 (.step 44 (.close 7))))))))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.close 16))))))))) (.step 48 (.step 58 (.close 3)))) (.step 5 (.step 58 (.split 74 1 (.split 8 0 (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5)))) (.step 9 (.close 3))) (.step 11 (.close 23)))))) (.step 53 (.split 74 1 (.split 2 0 (.split 8 0 (.split 56 1 (.step 53 (.close 7)) (.step 3 (.step 4 (.step 7 (.step 9 (.close 21)))))) (.step 3 (.step 7 (.step 11 (.step 27 (.step 34 (.close 44))))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 44)))))))) (.step 53 (.step 62 (.step 7 (.close 5))))) (.step 53 (.step 61 (.step 7 (.step 3 (.close 5)))))) (.step 53 (.step 54 (.step 57 (.step 53 (.step 7 (.close 3))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567161174868858867513347584291470413161041331859301996185383359567389335146818588361269775278591758116034487790379282440000604292941476575656851961302589463788589652372959515212059479554120403321807170486317399881473327104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.step 5 (.close 17)))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.close 17)))))) (.step 7 (.close 3))) (.step 9 (.step 31 (.step 9 (.step 11 (.close 3)))))) (.step 27 (.step 23 (.step 55 (.step 23 (.step 11 (.step 17 (.step 7 (.close 19))))))))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.close 16))))))))) (.step 48 (.step 58 (.close 3)))) (.step 5 (.step 58 (.split 74 1 (.split 8 0 (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5)))) (.step 9 (.close 3))) (.step 11 (.step 17 (.step 3 (.step 7 (.close 5))))))))) (.step 52 (.split 74 1 (.split 2 0 (.split 8 0 (.split 56 1 (.step 52 (.close 7)) (.step 3 (.step 4 (.step 7 (.step 9 (.close 21)))))) (.step 3 (.step 7 (.step 11 (.step 27 (.step 34 (.close 44))))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 44)))))))) (.step 52 (.step 62 (.step 7 (.close 5))))) (.step 52 (.step 61 (.step 7 (.step 3 (.close 5)))))) (.step 52 (.step 54 (.step 57 (.step 52 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648365977144347058681978277116666098743607114191412539063716371710453210000916480⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.reuse 0) (.run (.step 58 (.step 18 (.step 27 (.step 48 (.close 3))))))) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 70 (.step 3 (.close 7)))) (.step 54 (.step 62 (.close 7)))) (.step 3 (.step 61 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.step 31 (.step 3 (.close 54)))))))) (.reuse 1)) (.split 50 1 (.reuse 2) (.run (.step 52 (.split 74 1 (.split 2 0 (.split 8 0 (.split 30 0 (.step 52 (.step 9 (.step 55 (.step 5 (.close 52))))) (.step 31 (.step 7 (.close 52)))) (.step 9 (.step 27 (.close 52)))) (.step 5 (.step 9 (.step 52 (.close 3))))) (.step 27 (.step 31 (.step 34 (.step 52 (.step 3 (.close 7)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124640336704744686651256864396651672293621496170733976847440503962642623389911155559207847976343916592758769017197011722567680⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 70 (.step 3 (.close 7)))) (.step 9 (.step 27 (.close 7)))) (.step 3 (.step 11 (.step 27 (.close 7))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 9 (.close 46))))))) (.step 46 (.split 55 1 (.split 56 1 (.split 58 1 (.split 74 1 (.step 46 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 9 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.step 7 (.close 52)))))))) (.run (.step 5 (.step 43 (.step 31 (.split 43 1 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 51 1 (.step 5 (.split 67 1 (.step 5 (.step 7 (.close 11))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 7 (.close 44))))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 31 (.step 44 (.close 53)))))))) (.step 5 (.step 9 (.step 23 (.step 31 (.step 44 (.close 52)))))))) (.step 3 (.step 7 (.close 9)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980350648051554646572046290503333979045722908731144155282057281710867292965830656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 43 (.step 58 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 42 (.split 59 1 (.split 67 1 (.split 74 1 (.split 8 0 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.step 7 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 7)))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 5 (.step 3 (.step 8 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 31 (.step 42 (.step 7 (.step 9 (.step 7 (.close 16)))))))))) (.step 5 (.step 43 (.step 58 (.step 7 (.split 67 1 (.split 2 0 (.split 8 0 (.step 7 (.step 28 (.step 5 (.step 7 (.close 16))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.step 7 (.step 9 (.close 21)))))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 31 (.step 42 (.step 21 (.step 7 (.step 9 (.step 21 (.close 26))))))))) (.step 5 (.step 31 (.step 42 (.step 16 (.step 58 (.step 9 (.close 26)))))))) (.step 3 (.step 7 (.step 9 (.close 10))))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 16 (.step 22 (.step 16 (.close 41))))))))) (.step 3 (.step 5 (.step 21 (.close 42))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980350648051554646572046290503333979045722908731144155282057281710867292965830656⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.split 39 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 45 (.step 23 (.step 31 (.step 21 (.step 16 (.step 22 (.step 16 (.close 45)))))))))))) (.step 23 (.step 31 (.step 44 (.step 31 (.step 7 (.step 16 (.step 45 (.step 21 (.step 22 (.step 45 (.close 52)))))))))))))))) (.run (.split 40 1 (.split 42 1 (.step 42 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 8 0 (.step 31 (.step 27 (.close 42))) (.step 42 (.step 3 (.close 7)))) (.step 42 (.close 3))) (.step 11 (.step 42 (.step 3 (.close 7))))) (.step 3 (.step 42 (.split 8 0 (.step 70 (.close 7)) (.step 7 (.step 11 (.step 27 (.step 34 (.close 42))))))))) (.step 27 (.step 42 (.step 7 (.step 3 (.close 5)))))) (.step 27 (.step 42 (.step 3 (.close 5))))) (.step 3 (.step 42 (.step 3 (.step 61 (.step 62 (.step 70 (.step 7 (.close 11))))))))) (.step 27 (.step 42 (.step 53 (.close 3))))) (.step 27 (.step 42 (.step 34 (.close 52))))) (.step 3 (.step 11 (.step 3 (.step 27 (.close 7)))))))) (.step 5 (.step 7 (.step 31 (.close 42))))) (.step 5 (.step 27 (.step 31 (.close 42))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083263539908491211968243871515317125863395860159850567032897637623778906701660973129267604881408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 37 (.step 9 (.step 23 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37)))))))))))) (.step 15 (.step 16 (.step 17 (.step 31 (.step 34 (.step 31 (.step 7 (.close 16))))))))) (.step 7 (.step 31 (.step 37 (.step 45 (.step 9 (.step 16 (.step 17 (.step 31 (.close 52)))))))))) (.step 5 (.step 31 (.close 34)))) (.step 16 (.step 31 (.step 38 (.step 45 (.step 5 (.step 7 (.step 5 (.step 37 (.close 21)))))))))) (.step 31 (.split 49 1 (.split 50 1 (.step 45 (.split 55 1 (.split 59 1 (.split 74 1 (.step 37 (.step 7 (.step 5 (.step 31 (.close 16))))) (.step 5 (.step 7 (.step 31 (.step 5 (.close 37)))))) (.step 7 (.step 5 (.step 22 (.step 23 (.step 31 (.step 16 (.step 21 (.close 22))))))))) (.step 5 (.step 7 (.close 37))))) (.step 7 (.step 22 (.step 23 (.step 31 (.close 37)))))) (.step 7 (.step 16 (.step 9 (.step 17 (.step 31 (.step 37 (.close 52)))))))))))))
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
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330582609369522246042763919360⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.split 38 0 (.split 39 0 (.step 25 (.close 7)) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18))))))) (.step 7 (.step 8 (.step 11 (.close 14))))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.step 19 (.close 17))))))) (.step 11 (.step 18 (.step 44 (.step 7 (.step 17 (.step 19 (.close 17)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 44 (.step 48 (.step 11 (.step 23 (.step 25 (.step 31 (.step 19 (.step 44 (.step 19 (.step 17 (.step 42 (.close 53)))))))))))))) (.step 4 (.step 44 (.step 48 (.step 55 (.step 27 (.step 52 (.step 7 (.step 11 (.step 17 (.close 19))))))))))) (.step 7 (.step 5 (.step 11 (.step 19 (.close 20)))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 19 (.step 7 (.step 17 (.step 7 (.close 20)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330582609369522246042763919360⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 58 (.step 31 (.step 5 (.step 16 (.close 21))))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 31 (.step 7 (.step 16 (.step 21 (.step 22 (.step 21 (.close 52)))))))))))) (.step 7 (.step 31 (.step 45 (.step 9 (.step 23 (.step 31 (.step 38 (.step 16 (.step 45 (.close 52))))))))))) (.step 5 (.step 31 (.close 36)))) (.step 31 (.step 38 (.split 49 1 (.step 45 (.step 5 (.step 7 (.step 5 (.step 22 (.step 16 (.close 21))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.close 39)))))))))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 42)))))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7)))))))) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147119229707115137779673558956759444558487127859797624668181824676036608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.split 38 0 (.step 20 (.split 74 1 (.step 7 (.step 11 (.step 3 (.step 7 (.close 17))))) (.step 11 (.step 7 (.step 18 (.step 7 (.close 17))))))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18))))))) (.step 7 (.step 8 (.step 11 (.close 14))))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.step 19 (.close 17))))))) (.step 11 (.step 18 (.step 20 (.step 7 (.step 19 (.close 44))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 48 (.step 11 (.step 23 (.step 53 (.step 7 (.step 19 (.step 17 (.close 20)))))))))) (.step 4 (.step 48 (.step 61 (.step 7 (.step 11 (.step 17 (.step 19 (.step 42 (.step 44 (.close 52))))))))))) (.step 7 (.step 5 (.step 11 (.step 19 (.close 20)))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 19 (.step 7 (.step 17 (.step 7 (.close 20)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147119229707115137778178442781769930873164758275928867139073805684572160⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 10 0 (.split 17 0 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 3 (.close 7)))) (.step 19 (.split 8 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 8 (.step 7 (.close 11)))))) (.step 7 (.step 8 (.step 11 (.close 14))))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.close 19)))))) (.step 11 (.step 18 (.step 42 (.step 7 (.step 17 (.step 19 (.close 17)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 42 (.step 7 (.step 11 (.step 18 (.step 19 (.step 44 (.step 17 (.step 19 (.close 53))))))))))) (.step 4 (.step 42 (.step 48 (.step 53 (.step 7 (.step 11 (.step 17 (.step 19 (.step 44 (.close 52))))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.close 3))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450099676262491840107536143559617393373620469760⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.close 53))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 42 (.step 25 (.close 52)))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5)))))))))) (.run (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.close 53))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 42 (.step 20 (.close 52)))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450099676262491840107536143559617393373621518336⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part13.root]
def proof : Chunks.Proof 3 := (.split 2 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.step 25 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 25 (.step 7 (.step 5 (.step 3 (.close 18))))) (.step 11 (.step 18 (.step 20 (.close 19))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.step 20 (.step 17 (.step 25 (.close 53))))))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 52 (.step 19 (.close 20))))))))) (.step 7 (.step 5 (.step 11 (.step 19 (.close 20)))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 7 (.step 17 (.step 25 (.close 42))))))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))))))))) (.reuse 2)) (.run (.step 3 (.step 5 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.step 5 (.split 39 1 (.step 3 (.step 5 (.step 23 (.step 61 (.step 3 (.step 9 (.step 17 (.step 21 (.step 17 (.close 23)))))))))) (.step 5 (.step 21 (.close 42))))) (.step 3 (.step 5 (.close 39)))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 18 (.close 19)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726287955918105216566624601901706107976334118234853872875812949604281502102008814458038143032455719680345786664676753408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 2 1 (.split 38 1 (.split 56 1 (.split 67 1 (.split 10 0 (.split 74 1 (.split 2 0 (.split 8 0 (.step 7 (.split 16 0 (.split 17 0 (.step 7 (.step 27 (.step 7 (.step 5 (.close 17))))) (.step 7 (.close 17))) (.step 7 (.step 17 (.close 3))))) (.step 11 (.close 3))) (.step 11 (.step 23 (.close 5)))) (.step 11 (.step 17 (.close 3)))) (.step 17 (.step 31 (.step 7 (.step 5 (.close 8)))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 3 (.step 5 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 3 (.step 5 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 3 (.step 5 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 23 (.step 31 (.step 27 (.step 44 (.step 23 (.step 77 (.step 55 (.step 23 (.step 11 (.close 17))))))))))) (.step 11 (.step 17 (.step 42 (.step 61 (.step 5 (.close 7))))))) (.step 5 (.step 18 (.step 27 (.step 18 (.step 48 (.step 11 (.step 17 (.step 5 (.step 31 (.step 34 (.step 5 (.close 21))))))))))))) (.step 3 (.step 31 (.step 61 (.step 3 (.step 7 (.step 17 (.step 27 (.step 17 (.step 34 (.step 11 (.close 44)))))))))))))
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
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410922805883575589494528955351914286565359091712⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 23 (.step 31 (.step 27 (.step 48 (.step 61 (.split 51 1 (.split 59 1 (.split 67 1 (.step 23 (.split 74 1 (.step 55 (.step 23 (.step 11 (.close 17)))) (.step 11 (.step 17 (.close 3))))) (.step 3 (.step 7 (.step 11 (.step 17 (.step 34 (.close 44))))))) (.step 44 (.step 23 (.step 52 (.step 23 (.step 11 (.step 7 (.close 17)))))))) (.step 3 (.step 7 (.step 52 (.close 53)))))))))))) (.run (.step 17 (.step 23 (.step 31 (.step 27 (.step 34 (.step 48 (.step 52 (.step 23 (.step 34 (.step 7 (.step 11 (.step 3 (.step 7 (.close 17)))))))))))))))) (.run (.step 3 (.step 8 (.step 11 (.step 3 (.step 7 (.step 11 (.close 27))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 11 (.step 7 (.close 17)))))))) (.run (.step 5 (.step 7 (.step 11 (.step 7 (.step 17 (.step 23 (.step 7 (.close 17)))))))))) (.run (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.step 5 (.close 7))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 36 (.step 7 (.step 5 (.step 31 (.step 5 (.close 37)))))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 34 (.step 7 (.step 31 (.step 5 (.close 37))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 7 (.step 11 (.step 7 (.close 17)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.split 38 1 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17)))))) (.step 3 (.step 5 (.close 17))))))))))
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
def root : Box := ⟨2417851639229260496896000, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325440172560151259631414085193074204110130522909408756145905275508438652988691548221534244085767128509166414099784925184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 2 1 (.split 38 1 (.step 11 (.split 56 1 (.split 67 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.split 34 0 (.split 36 0 (.step 11 (.step 3 (.close 7))) (.step 23 (.close 3))) (.step 23 (.step 3 (.step 5 (.close 7)))))) (.step 7 (.close 11))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 9))))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 9)))))) (.step 3 (.step 5 (.step 3 (.close 11))))) (.step 11 (.step 9 (.step 23 (.step 27 (.step 31 (.step 44 (.step 23 (.step 55 (.step 23 (.close 11))))))))))) (.step 11 (.step 31 (.step 42 (.close 61))))) (.step 5 (.step 11 (.step 18 (.step 31 (.step 48 (.step 11 (.step 5 (.close 9))))))))) (.step 3 (.step 11 (.step 3 (.step 7 (.step 27 (.step 18 (.step 3 (.step 61 (.step 11 (.step 34 (.close 44)))))))))))) (.step 11 (.step 9 (.step 23 (.step 27 (.step 31 (.step 48 (.step 61 (.split 51 1 (.split 59 1 (.split 67 1 (.step 23 (.step 55 (.step 23 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 44))))) (.step 9 (.step 44 (.step 11 (.step 3 (.close 19)))))) (.step 3 (.step 7 (.close 53)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2417851639229260496896000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539134298696058450022093553664⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 11 (.step 9 (.step 23 (.step 27 (.step 31 (.step 48 (.step 61 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.step 23 (.step 55 (.step 23 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 44))))) (.step 9 (.step 34 (.step 44 (.step 11 (.step 3 (.close 19))))))) (.step 3 (.step 7 (.step 34 (.close 52))))) (.step 9 (.step 34 (.close 52))))))))))))) (.run (.step 3 (.step 8 (.step 11 (.step 3 (.step 7 (.step 11 (.close 27))))))))) (.run (.step 5 (.step 7 (.step 9 (.step 11 (.step 7 (.step 9 (.close 11))))))))) (.run (.step 5 (.step 7 (.step 9 (.step 11 (.step 7 (.step 9 (.close 11))))))))) (.run (.step 11 (.step 31 (.step 42 (.close 5)))))) (.run (.step 5 (.step 7 (.step 9 (.step 31 (.step 36 (.step 7 (.step 5 (.step 31 (.step 5 (.close 39)))))))))))) (.run (.step 5 (.step 7 (.step 9 (.step 31 (.step 34 (.step 7 (.step 31 (.step 5 (.close 37))))))))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11)))))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 5 (.close 7))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539134298696058450022093553664⟩
def references : Fin 3 → Box := ![Part14.root, Part16.root, Part18.root]
def proof : Chunks.Proof 3 := (.split 8 1 (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 25 (.step 74 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17)))))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 67 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17))))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 52)))))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7))) (.step 3 (.step 17 (.step 3 (.step 7 (.step 11 (.close 17))))))))))))) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part16.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part19.excludes
end FiveColour.Packed.EnumerationChunks.Case140
