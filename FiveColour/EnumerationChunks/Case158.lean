module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case158
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763744141312⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨2147483648, 5783580587434429433756673792145735206580520665929650998092691679783694669210104598128705822647278416162793696896986131684056577041632788472233773227165069981345265954126914056725050535029533374769565940422209610382945812480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 0 (.split 14 0 (.split 16 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 31 (.split 38 0 (.step 7 (.close 3)) (.step 3 (.step 4 (.close 7))))) (.step 7 (.close 3))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 17)))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.split 16 0 (.split 17 0 (.step 7 (.step 31 (.step 3 (.step 7 (.close 11))))) (.step 7 (.step 17 (.step 3 (.close 5))))) (.step 7 (.step 18 (.step 7 (.close 17))))))) (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 5 (.split 22 0 (.step 5 (.split 30 0 (.step 5 (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.close 4)))) (.step 7 (.step 3 (.close 5)))) (.step 7 (.step 27 (.step 3 (.step 18 (.close 3)))))) (.split 30 0 (.split 43 0 (.split 51 0 (.step 31 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 7 (.step 3 (.close 5))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041327803083408248821065973113499751072541486551933211826000204806937246280638885736841612676857054114931776890062681900579070861809449093613395627876076468446266921208123568218439680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 74 1 (.reuse 0) (.run (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.split 30 0 (.split 34 0 (.step 23 (.step 27 (.step 3 (.close 17)))) (.step 23 (.close 5))) (.step 7 (.step 11 (.close 17))))) (.step 7 (.step 11 (.step 17 (.step 7 (.close 5)))))) (.step 11 (.split 34 0 (.split 36 0 (.step 61 (.step 7 (.close 17))) (.step 3 (.step 7 (.close 17)))) (.step 3 (.step 7 (.close 17)))))) (.step 11 (.split 34 0 (.split 30 0 (.split 36 0 (.step 42 (.step 7 (.step 18 (.step 7 (.close 17))))) (.step 7 (.step 17 (.step 7 (.close 18))))) (.step 7 (.step 17 (.step 7 (.close 18))))) (.step 7 (.close 17))))) (.step 7 (.step 11 (.close 17)))) (.step 11 (.step 23 (.split 10 0 (.step 5 (.step 7 (.close 18))) (.step 3 (.step 5 (.close 7))))))))) (.run (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 55 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.step 27 (.close 34)))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 44))))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331855344705984165752020386804136972103022143956886080785356816048272308775031154953331140772041520980886458311325749006006794574171175425219736152281657863930066893478452505083904⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.reuse 0) (.run (.split 67 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 10 0 (.step 62 (.step 7 (.step 3 (.step 5 (.close 7))))) (.step 7 (.step 31 (.step 7 (.step 3 (.close 27)))))) (.step 7 (.step 27 (.step 3 (.step 4 (.step 3 (.close 7))))))) (.step 7 (.step 27 (.step 7 (.step 3 (.step 7 (.close 18))))))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 18 (.step 31 (.step 18 (.close 19))))))))) (.step 31 (.step 27 (.step 55 (.step 44 (.step 7 (.close 17))))))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 22 0 (.step 5 (.step 31 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 7 (.close 3))))) (.step 31 (.step 3 (.step 9 (.close 23))))) (.step 3 (.step 7 (.step 3 (.close 15)))))) (.split 2 0 (.step 55 (.step 27 (.step 44 (.close 7)))) (.step 11 (.step 23 (.close 3))))) (.step 44 (.step 62 (.step 7 (.close 3)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301992407735424565354844473286458062706058471700174795441057169795130632859463205865834458500869606291874068565264236224196011724333239095633020139494220753559186806884270080⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 58 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.split 34 0 (.step 61 (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 7 (.step 17 (.step 23 (.close 31)))))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27)))) (.step 7 (.step 27 (.step 7 (.step 3 (.step 7 (.close 18))))))) (.step 7 (.step 27 (.step 7 (.step 42 (.step 3 (.step 7 (.close 18)))))))) (.split 16 0 (.step 31 (.step 27 (.step 34 (.step 31 (.step 58 (.step 7 (.close 18))))))) (.step 11 (.step 42 (.step 7 (.step 18 (.step 7 (.close 17)))))))) (.split 10 0 (.step 61 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 7 (.close 15))))))) (.step 11 (.step 61 (.step 7 (.close 5))))) (.step 3 (.step 61 (.split 10 0 (.split 14 0 (.step 70 (.close 7)) (.step 7 (.step 27 (.step 34 (.close 44))))) (.step 7 (.step 27 (.close 44))))))) (.step 44 (.step 61 (.step 7 (.step 5 (.close 7))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471300751149468785396202835943736744396702085800021476867234464906581098657480704⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 43 (.split 16 0 (.split 17 0 (.step 43 (.step 58 (.step 7 (.step 55 (.step 22 (.step 5 (.close 7))))))) (.step 3 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 5 (.close 7)))))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 5)))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 22 (.step 7 (.step 16 (.step 7 (.close 21))))))))))))) (.step 3 (.step 5 (.step 31 (.close 18))))))) (.run (.step 58 (.split 58 1 (.step 18 (.step 58 (.step 48 (.step 3 (.close 62))))) (.step 27 (.step 58 (.step 48 (.step 3 (.close 35))))))))) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 55 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.step 27 (.close 34)))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 44)))))) (.step 70 (.step 3 (.step 7 (.close 3))))) (.step 54 (.step 62 (.step 7 (.close 3))))) (.step 3 (.step 61 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.step 31 (.step 3 (.close 54))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11567161174868858867508448700980813070724093477401681768644298834190491637063229733832077482858699146786791677654113802719117878506243101229106750357060890490585628675387673822544485147054661208765077558520255781900498501632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 10 0 (.split 34 0 (.split 36 0 (.step 53 (.step 3 (.close 5))) (.step 7 (.step 9 (.step 7 (.step 5 (.close 23)))))) (.step 7 (.step 9 (.step 7 (.step 31 (.close 16)))))) (.step 7 (.step 31 (.step 7 (.step 3 (.close 27)))))) (.step 7 (.step 27 (.step 3 (.step 4 (.step 3 (.close 7))))))) (.step 7 (.step 27 (.step 7 (.step 3 (.step 7 (.close 18))))))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 18 (.step 31 (.step 18 (.close 19))))))))) (.step 31 (.step 27 (.step 55 (.step 52 (.step 7 (.close 19))))))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 22 0 (.step 5 (.step 31 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 7 (.close 3))))) (.step 31 (.step 3 (.step 9 (.close 23))))) (.step 3 (.step 7 (.step 3 (.close 15)))))) (.split 2 0 (.step 55 (.step 27 (.split 14 0 (.step 31 (.step 44 (.close 7))) (.step 23 (.step 17 (.step 31 (.step 44 (.close 7)))))))) (.step 11 (.step 23 (.close 3))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325437709934763984976463317753067945134267705425704352055488528740100887631080829645871030694123780350299634427185070080⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 50 1 (.reuse 0) (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.reuse 1) (.run (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 40 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.step 27 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 7 (.step 27 (.close 44)))) (.step 7 (.step 27 (.close 36)))) (.step 3 (.step 7 (.step 27 (.step 34 (.close 44)))))) (.step 7 (.step 27 (.close 44)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 27 (.step 44 (.step 17 (.close 53))))))))) (.run (.step 53 (.step 62 (.step 7 (.close 5)))))) (.run (.step 53 (.step 61 (.step 7 (.step 5 (.close 7))))))) (.run (.step 5 (.step 31 (.step 48 (.step 57 (.step 21 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 26)))))))))))))) (.run (.step 48 (.step 53 (.step 58 (.step 3 (.step 27 (.close 35)))))))) (.run (.step 53 (.step 54 (.step 57 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 40 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.step 27 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 7 (.step 27 (.close 44)))) (.step 7 (.step 27 (.close 36)))) (.step 3 (.step 7 (.step 27 (.step 34 (.close 44)))))) (.step 7 (.step 27 (.close 44)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 27 (.step 44 (.step 17 (.close 53)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567161174868858867513347584291470413161041331855344705984165752020386804140168773537667532931015540920124250569395339529243883789620548768177361547009751320752199456331589949643087997204472663502802657162484682606146224128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.step 3 (.close 5))) (.step 7 (.step 9 (.step 7 (.step 31 (.close 16)))))) (.step 7 (.step 31 (.step 7 (.step 3 (.close 27)))))) (.step 7 (.step 27 (.step 3 (.step 4 (.step 3 (.close 7))))))) (.step 7 (.step 27 (.step 7 (.step 3 (.step 7 (.close 18))))))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 18 (.step 31 (.step 18 (.close 19))))))))) (.step 31 (.step 27 (.step 55 (.step 17 (.step 7 (.close 34))))))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 22 0 (.step 5 (.step 31 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 7 (.close 3))))) (.step 31 (.step 3 (.step 9 (.close 23))))) (.step 3 (.step 7 (.step 3 (.close 15)))))) (.split 2 0 (.step 55 (.step 27 (.split 14 0 (.step 31 (.step 44 (.close 7))) (.step 17 (.close 3))))) (.step 11 (.step 17 (.step 23 (.close 3)))))) (.split 74 1 (.split 2 0 (.split 30 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 43 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 27 (.close 7)))) (.step 7 (.step 9 (.close 44)))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 7 (.step 9 (.close 36)))) (.step 7 (.step 27 (.close 42)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 27 (.step 34 (.step 44 (.close 52)))))))) (.step 52 (.step 62 (.step 7 (.close 5))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648365977144347058681978277116666098743607114191412539062507445890838580826210304⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.reuse 0) (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.reuse 1) (.run (.step 52 (.step 61 (.step 7 (.step 5 (.close 7))))))) (.run (.step 5 (.step 31 (.step 48 (.step 57 (.step 52 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21)))))))))))))) (.run (.step 48 (.step 52 (.step 58 (.step 3 (.step 27 (.close 35)))))))) (.run (.step 52 (.step 54 (.step 57 (.split 74 1 (.split 2 0 (.split 30 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 43 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 27 (.close 7)))) (.step 7 (.step 9 (.close 44)))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 7 (.step 9 (.close 36)))) (.step 7 (.step 27 (.close 42)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 27 (.step 34 (.step 44 (.close 52)))))))))))) (.run (.step 52 (.split 56 1 (.split 74 1 (.split 2 0 (.split 30 0 (.split 36 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 31 (.step 52 (.close 4))))) (.step 52 (.step 4 (.close 7)))) (.step 9 (.step 52 (.close 3)))) (.step 27 (.step 34 (.step 52 (.step 3 (.close 7)))))) (.step 5 (.step 9 (.step 21 (.step 31 (.step 48 (.step 5 (.step 7 (.step 16 (.step 7 (.step 22 (.step 7 (.close 26)))))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832323002619724861049712310179709848418892747886637021813849138747252203646220411217988224292064443189452011748906085414600704⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 55 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 11)))) (.step 70 (.step 3 (.step 7 (.close 3))))) (.step 9 (.step 27 (.step 7 (.close 46))))) (.step 3 (.step 11 (.step 27 (.close 7))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 9 (.close 46))))))) (.step 46 (.split 55 1 (.split 56 1 (.split 58 1 (.split 74 1 (.step 54 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 9 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))))) (.step 9 (.step 27 (.step 9 (.step 46 (.step 7 (.close 53))))))) (.step 9 (.step 27 (.step 9 (.step 46 (.step 7 (.close 52))))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 45 (.step 5 (.close 17))))))) (.step 23 (.step 31 (.step 44 (.step 31 (.step 7 (.step 38 (.step 45 (.step 16 (.step 22 (.close 53))))))))))) (.step 23 (.step 31 (.step 44 (.step 58 (.step 55 (.step 9 (.close 52)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832323005141453257618958979765568414828084031411740335123637725495942981517946604593809703422577483502086612760530276794236928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 56 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.split 34 0 (.step 42 (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 7 (.step 17 (.step 23 (.close 31)))))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27)))) (.step 7 (.step 27 (.step 7 (.step 3 (.step 7 (.close 18))))))) (.step 7 (.step 27 (.step 7 (.close 42))))) (.step 42 (.step 3 (.close 7)))) (.step 5 (.step 3 (.step 18 (.close 21))))) (.step 5 (.step 42 (.close 3)))) (.step 11 (.step 61 (.step 42 (.step 5 (.close 7)))))) (.step 3 (.step 42 (.split 10 0 (.split 14 0 (.step 70 (.close 7)) (.step 7 (.step 27 (.step 34 (.close 42))))) (.step 7 (.step 27 (.close 42))))))) (.step 42 (.step 44 (.step 61 (.step 42 (.step 27 (.step 7 (.step 5 (.close 7))))))))) (.step 42 (.step 3 (.close 5)))) (.step 5 (.step 42 (.step 3 (.close 5))))) (.step 3 (.step 42 (.step 3 (.step 61 (.step 62 (.step 70 (.split 14 0 (.step 7 (.step 9 (.close 27))) (.step 7 (.step 11 (.step 27 (.close 34)))))))))))) (.step 21 (.step 42 (.step 27 (.step 53 (.step 3 (.close 5))))))) (.step 42 (.step 52 (.step 61 (.step 42 (.step 27 (.step 31 (.close 3)))))))) (.step 3 (.step 11 (.step 3 (.step 27 (.close 7)))))) (.step 5 (.step 7 (.step 31 (.step 42 (.close 44)))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124637754457329225129941863428247109288006142327758631328331763720032851080054496328731793994204028094648714521960824049762304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 43 (.split 16 0 (.split 17 0 (.step 43 (.step 58 (.step 7 (.step 55 (.step 58 (.close 3)))))) (.step 3 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 5 (.close 7)))))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 5)))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 31 (.step 42 (.step 7 (.step 9 (.step 21 (.step 7 (.close 16)))))))))) (.step 3 (.step 5 (.step 31 (.close 18))))) (.step 5 (.step 58 (.split 16 0 (.split 17 0 (.split 22 0 (.split 67 1 (.split 2 0 (.split 14 0 (.split 40 0 (.split 43 0 (.split 51 0 (.step 58 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 21)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7))))))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 31 (.step 42 (.step 48 (.step 5 (.step 21 (.step 58 (.step 9 (.close 26)))))))))) (.step 5 (.step 31 (.step 42 (.step 48 (.step 58 (.step 9 (.step 42 (.step 26 (.close 52)))))))))) (.step 3 (.step 7 (.step 9 (.close 10)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980350648051554646572046290503333979045722908731144155280848355891252663791124480⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 38 1 (.split 39 1 (.split 40 1 (.reuse 0) (.run (.step 31 (.step 58 (.split 43 1 (.split 49 1 (.step 43 (.split 50 1 (.split 51 1 (.split 58 1 (.step 31 (.split 59 1 (.split 67 1 (.step 5 (.split 74 1 (.split 14 0 (.step 43 (.step 7 (.close 9))) (.step 5 (.close 7))) (.step 5 (.step 7 (.step 17 (.step 7 (.close 19))))))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 31 (.close 44)))))))) (.step 5 (.step 27 (.step 31 (.close 61))))) (.step 3 (.step 7 (.step 9 (.step 44 (.close 54)))))) (.step 5 (.step 9 (.step 23 (.step 31 (.close 53))))))) (.step 5 (.step 9 (.step 23 (.step 31 (.close 52)))))) (.step 3 (.step 7 (.close 9)))))))) (.split 40 1 (.reuse 1) (.run (.step 5 (.step 27 (.step 31 (.step 42 (.close 7)))))))) (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 2) (.run (.step 7 (.step 31 (.step 38 (.step 60 (.step 76 (.split 49 1 (.split 55 1 (.split 2 0 (.split 14 0 (.split 49 0 (.split 50 0 (.step 28 (.step 41 (.step 7 (.close 5)))) (.step 7 (.step 5 (.step 31 (.step 21 (.close 22)))))) (.step 7 (.step 31 (.step 16 (.step 22 (.step 16 (.close 21))))))) (.step 7 (.step 5 (.step 16 (.step 31 (.close 37)))))) (.step 7 (.step 5 (.step 31 (.step 37 (.close 41)))))) (.step 5 (.step 7 (.step 38 (.step 16 (.close 41)))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.close 41)))))))))))))) (.run (.step 3 (.step 5 (.step 31 (.close 43)))))) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 5 (.close 42)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567161174868858867508448700980813070724093481457900356580861127784764120506993295057520431419218060921738044943417523009391272218120226127102888290944092196500198507811384329135792614978398292438246333720909723742352965632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 58 (.step 5 (.close 17))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 31 (.step 7 (.step 38 (.step 16 (.step 22 (.step 16 (.step 45 (.close 53))))))))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 55 (.step 57 (.step 31 (.step 7 (.close 52)))))))))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 39 0 (.step 45 (.step 3 (.close 7))) (.step 7 (.close 31))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 5 (.step 31 (.step 37 (.close 39)))))) (.step 5 (.step 7 (.step 31 (.step 5 (.close 39)))))) (.step 7 (.step 22 (.step 23 (.step 31 (.step 39 (.step 16 (.step 21 (.close 22))))))))) (.step 5 (.step 7 (.step 39 (.close 45))))) (.step 7 (.step 22 (.step 23 (.step 31 (.step 38 (.step 39 (.step 45 (.step 52 (.step 53 (.close 57))))))))))) (.step 7 (.step 22 (.step 23 (.step 31 (.step 45 (.step 38 (.step 52 (.step 16 (.step 22 (.close 57))))))))))))) (.step 5 (.step 31 (.close 36)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567161174868858867508448700980813070724093481457900356580861127784764120506993295057520431419218060921738044943415174469048243127070140857063541234485160792072935685175326573064249506917075555174943580103402448310928146432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 37 (.step 23 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37))))))))))) (.step 15 (.step 23 (.step 31 (.step 34 (.step 31 (.step 7 (.step 16 (.step 21 (.step 22 (.step 37 (.step 45 (.step 22 (.close 53)))))))))))))) (.step 15 (.step 16 (.step 23 (.step 31 (.step 34 (.step 55 (.step 52 (.step 5 (.step 7 (.close 16))))))))))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 39 0 (.step 37 (.step 7 (.step 31 (.step 16 (.close 21))))) (.step 7 (.close 31))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 5 (.step 31 (.close 37))))) (.step 5 (.step 7 (.step 31 (.step 5 (.close 37)))))) (.step 7 (.step 23 (.step 31 (.step 16 (.step 21 (.step 22 (.step 21 (.close 37))))))))) (.step 5 (.step 7 (.close 37)))) (.step 7 (.step 23 (.step 31 (.step 37 (.step 38 (.step 45 (.step 16 (.close 52))))))))) (.step 7 (.step 16 (.step 17 (.step 31 (.close 52)))))))) (.step 5 (.step 31 (.close 34)))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083263539908491211968243871515317125863395860159850567032897637623778905492735153514638430175232⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 16 (.step 31 (.step 38 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 42 1 (.split 49 0 (.split 50 0 (.step 28 (.step 41 (.step 7 (.close 5)))) (.step 7 (.step 5 (.step 31 (.step 21 (.close 22)))))) (.step 7 (.step 16 (.step 5 (.step 22 (.close 31)))))) (.step 28 (.step 37 (.close 5)))) (.step 7 (.step 5 (.step 16 (.step 31 (.close 37)))))) (.step 7 (.step 5 (.step 31 (.close 37))))) (.step 3 (.step 5 (.close 37)))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.close 37))))))) (.step 5 (.step 7 (.step 37 (.step 21 (.close 41))))))))))) (.run (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 38 1 (.split 42 1 (.split 39 0 (.step 37 (.step 7 (.step 31 (.step 16 (.close 21))))) (.step 7 (.close 31))) (.step 37 (.close 31))) (.step 28 (.step 37 (.close 5)))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37)))) (.step 5 (.step 7 (.step 31 (.step 5 (.close 37)))))) (.step 7 (.step 22 (.step 23 (.step 31 (.close 37)))))) (.step 5 (.step 7 (.close 37)))) (.step 7 (.step 22 (.step 23 (.step 31 (.step 37 (.step 21 (.step 38 (.step 45 (.step 52 (.step 45 (.step 22 (.close 53))))))))))))) (.step 7 (.step 16 (.step 23 (.step 31 (.step 37 (.close 52))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330581400443702631413589213184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 38 0 (.split 40 0 (.split 49 0 (.split 39 0 (.step 7 (.close 18)) (.step 11 (.step 18 (.step 7 (.close 19))))) (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.close 44))))) (.step 11 (.step 44 (.step 61 (.step 18 (.split 10 0 (.split 14 0 (.step 7 (.close 19)) (.step 17 (.step 20 (.step 7 (.close 19))))) (.step 7 (.close 17)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 44 (.step 48 (.step 55 (.step 27 (.step 53 (.step 31 (.step 44 (.step 19 (.step 17 (.step 42 (.close 53))))))))))))) (.step 4 (.step 44 (.step 48 (.step 55 (.step 27 (.step 52 (.step 17 (.step 25 (.step 31 (.step 19 (.step 44 (.step 42 (.close 52)))))))))))))) (.step 7 (.step 5 (.step 19 (.step 20 (.step 19 (.step 25 (.close 44)))))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 44 (.split 40 1 (.split 10 0 (.step 42 (.close 7)) (.step 7 (.close 17))) (.step 7 (.step 19 (.close 20)))))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330581400443702631413589213184⟩
def references : Fin 4 → Box := ![Part12.root, Part13.root, Part15.root, Part16.root]
def proof : Chunks.Proof 4 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 38 1 (.reuse 1) (.run (.step 31 (.step 38 (.split 49 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 42 1 (.split 49 0 (.split 50 0 (.step 28 (.step 41 (.step 7 (.close 5)))) (.step 7 (.step 5 (.step 22 (.close 31))))) (.step 7 (.step 22 (.step 31 (.step 16 (.close 22)))))) (.step 28 (.step 39 (.close 5)))) (.step 7 (.step 5 (.step 31 (.step 37 (.close 39)))))) (.step 7 (.step 5 (.step 31 (.close 39))))) (.step 3 (.step 5 (.close 39)))) (.step 5 (.step 7 (.step 21 (.step 22 (.step 16 (.close 39))))))) (.step 5 (.step 7 (.step 38 (.step 39 (.close 22)))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 39 (.step 45 (.close 52)))))))))))))))) (.reuse 2)) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 3 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 42)))))))) (.step 7 (.step 31 (.step 53 (.step 7 (.step 3 (.step 27 (.step 31 (.close 42))))))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7)))))))) (.reuse 3))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147119229707115137779673558956759444558487127858588698848567195501330432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 38 0 (.split 40 0 (.split 49 0 (.split 39 0 (.step 7 (.close 18)) (.step 11 (.step 18 (.step 7 (.close 19))))) (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.close 44))))) (.step 11 (.step 61 (.step 3 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 48 (.step 61 (.step 7 (.step 19 (.step 44 (.step 19 (.step 17 (.step 42 (.step 44 (.close 53)))))))))))) (.step 4 (.step 48 (.step 61 (.split 74 1 (.step 55 (.step 27 (.step 52 (.close 7)))) (.step 7 (.step 17 (.step 19 (.close 44))))))))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 61 (.step 19 (.step 7 (.step 17 (.step 7 (.close 20))))))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828111988598038931588921903850101917514759088513220608⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 25 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.step 20 (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 5)))) (.step 7 (.step 18 (.step 20 (.step 17 (.step 19 (.close 25))))))) (.step 11 (.step 18 (.step 20 (.step 19 (.close 61)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 61 (.step 19 (.step 25 (.step 17 (.close 53)))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 44 (.step 53 (.step 61 (.step 19 (.step 25 (.step 52 (.close 53)))))))))))) (.step 7 (.step 5 (.step 18 (.close 20))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 42 (.step 20 (.close 7)))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 19))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147119229707115137778178442781769930873164758274719941319459176509865984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 38 0 (.split 40 0 (.split 49 0 (.split 39 0 (.step 7 (.close 18)) (.step 11 (.step 18 (.step 7 (.close 19))))) (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.close 17))))) (.step 11 (.step 42 (.step 18 (.step 61 (.step 77 (.step 7 (.step 17 (.close 19))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 42 (.step 48 (.step 53 (.step 7 (.step 19 (.step 53 (.close 19))))))))) (.step 4 (.step 42 (.step 48 (.step 53 (.step 61 (.step 7 (.step 17 (.step 19 (.step 44 (.close 52))))))))))) (.step 7 (.step 5 (.close 19)))) (.step 11 (.step 18 (.step 42 (.step 3 (.close 7)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))
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
def root : Box := ⟨2996078356528350982317553907068380190294663860584448, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147120914703781834694662187146839714188322433864947823917366920409513984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.step 20 (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 5)))) (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 19 (.step 17 (.step 20 (.step 42 (.close 53)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 42 (.step 53 (.close 19))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 42 (.step 61 (.step 19 (.step 25 (.step 44 (.step 25 (.step 52 (.step 19 (.close 53)))))))))))))) (.step 7 (.step 5 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471300751149468785396202835943736744398095882374929640813580447298621621251604480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 56 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.split 30 0 (.split 34 0 (.step 23 (.step 27 (.step 3 (.close 17)))) (.step 23 (.close 5))) (.step 7 (.step 11 (.close 17))))) (.step 7 (.step 11 (.close 17)))) (.step 11 (.split 34 0 (.split 36 0 (.step 61 (.step 7 (.close 17))) (.step 3 (.step 7 (.close 17)))) (.step 3 (.step 7 (.close 17)))))) (.step 11 (.split 34 0 (.split 30 0 (.split 36 0 (.step 42 (.step 7 (.close 17))) (.step 7 (.close 17))) (.step 7 (.close 17))) (.step 7 (.close 17))))) (.step 7 (.step 11 (.close 17)))) (.step 11 (.step 23 (.split 30 0 (.step 5 (.step 7 (.close 17))) (.step 3 (.step 5 (.close 7))))))) (.step 11 (.step 17 (.step 7 (.close 5))))) (.step 5 (.step 3 (.close 17)))) (.step 3 (.step 7 (.step 11 (.step 17 (.step 34 (.close 44))))))) (.step 31 (.step 44 (.step 77 (.split 2 0 (.step 55 (.step 27 (.split 16 0 (.step 55 (.step 17 (.step 7 (.step 17 (.step 34 (.close 44)))))) (.step 23 (.step 17 (.close 7)))))) (.step 11 (.step 15 (.step 23 (.close 3))))))))) (.step 11 (.step 17 (.step 61 (.step 7 (.close 5)))))) (.step 5 (.step 18 (.step 31 (.step 18 (.step 48 (.step 58 (.step 17 (.step 34 (.close 44)))))))))) (.step 3 (.step 31 (.step 61 (.step 3 (.step 7 (.step 27 (.step 17 (.close 44))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263365873409341085735697933769687675427237195480366161210624950579325730420660762690893336668061889417183232⟩
def references : Fin 1 → Box := ![Part22.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 31 (.step 48 (.step 61 (.split 51 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.step 55 (.step 27 (.split 16 0 (.step 55 (.step 17 (.step 7 (.step 17 (.step 34 (.close 44)))))) (.step 23 (.step 17 (.close 7)))))) (.step 11 (.step 15 (.step 23 (.close 3))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 3 (.step 7 (.step 27 (.step 34 (.step 44 (.step 17 (.close 53)))))))) (.step 27 (.step 44 (.step 52 (.step 23 (.step 31 (.step 17 (.close 19)))))))) (.step 3 (.step 7 (.step 27 (.step 52 (.close 53))))))))))) (.run (.step 17 (.step 31 (.step 34 (.step 48 (.step 52 (.split 2 0 (.step 55 (.step 27 (.step 34 (.step 7 (.close 17))))) (.step 11 (.step 15 (.step 17 (.step 23 (.close 3))))))))))))) (.run (.step 3 (.step 8 (.step 11 (.step 3 (.step 7 (.step 11 (.close 27))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 17 (.close 7))))))) (.run (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 23 (.step 17 (.step 7 (.close 31))))))))))) (.run (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.step 61 (.step 42 (.step 5 (.close 7))))))))))) (.run (.step 3 (.step 5 (.step 31 (.step 42 (.step 63 (.step 49 (.step 5 (.close 17)))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 36 (.step 7 (.step 5 (.step 31 (.step 5 (.step 37 (.close 39)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066748271481280616189819267039887360⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 34 (.step 7 (.step 31 (.close 37)))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 7 (.step 11 (.close 17))))))))) (.run (.step 7 (.step 11 (.step 18 (.split 38 1 (.step 17 (.split 40 1 (.split 50 1 (.split 56 1 (.step 17 (.step 7 (.step 5 (.step 3 (.close 17))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17))))) (.step 3 (.step 5 (.close 17))))))))) (.run (.step 7 (.step 11 (.step 18 (.step 61 (.step 74 (.step 17 (.step 25 (.split 38 1 (.step 17 (.step 7 (.step 18 (.step 7 (.close 17))))) (.step 3 (.step 5 (.close 17))))))))))))) (.run (.step 7 (.step 11 (.step 18 (.step 42 (.step 67 (.step 17 (.step 19 (.split 40 1 (.split 50 1 (.split 56 1 (.step 17 (.step 7 (.step 5 (.step 3 (.close 17))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763743092736⟩
def references : Fin 4 → Box := ![Part19.root, Part20.root, Part21.root, Part24.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.step 25 (.close 7)) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 5)))) (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 19 (.step 17 (.step 20 (.step 25 (.step 42 (.close 53))))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 42 (.step 53 (.close 19))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 42 (.step 44 (.step 53 (.step 19 (.step 25 (.close 52))))))))))) (.step 7 (.step 5 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 19))))))))) (.reuse 2))))) (.reuse 3)) (.run (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 3 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 52)))))))) (.step 7 (.step 31 (.step 52 (.close 7))))) (.step 3 (.step 31 (.step 42 (.close 52))))) (.step 3 (.close 7))) (.step 3 (.step 17 (.step 3 (.step 7 (.step 17 (.close 31))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763744141312⟩
def references : Fin 1 → Box := ![Part25.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 58 (.step 5 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.step 5 (.split 36 1 (.split 38 1 (.step 5 (.split 39 1 (.step 3 (.step 5 (.step 61 (.split 16 0 (.step 4 (.step 23 (.step 21 (.step 23 (.step 34 (.close 44)))))) (.step 4 (.close 18)))))) (.step 5 (.step 21 (.close 42))))) (.step 5 (.close 41))) (.step 3 (.step 5 (.close 39))))) (.step 3 (.step 5 (.step 31 (.close 37))))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.step 18 (.close 20)))))) (.step 3 (.step 4 (.step 5 (.step 18 (.close 19)))))) (.step 5 (.step 17 (.step 23 (.close 17))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part26

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part26.excludes
end FiveColour.Packed.EnumerationChunks.Case158
