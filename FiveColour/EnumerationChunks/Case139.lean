module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case139
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413614682112⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨18740915245514405755891, 5789228615357111146520048038021683988773733487122101869605338720869906159532568379226031634421092153180474991687746456288884260796616315754835057774399955913938411420916390258617521507017839600618566356805942290412597150720, 0⟩]
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
def root : Box := ⟨2147483648, 5783580587434429433756673792145735206580520665929650998092691679783694669210104598128705822647278416162793696896986131684056577041632788472233773228976088222743109891949793994986542013752704369067075372496855966707881082880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 25 0 (.step 7 (.step 31 (.step 9 (.step 5 (.close 7))))) (.split 34 0 (.split 36 0 (.step 27 (.step 3 (.step 4 (.close 7)))) (.step 7 (.close 5))) (.step 7 (.close 5)))) (.step 31 (.split 34 0 (.split 10 0 (.step 27 (.close 3)) (.step 3 (.close 7))) (.step 5 (.step 7 (.close 5)))))) (.step 7 (.step 3 (.close 5)))) (.step 7 (.step 27 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.step 7 (.step 27 (.step 5 (.close 7))))) (.step 7 (.close 5))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.close 17)))))) (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 5 (.split 22 0 (.split 24 0 (.step 5 (.step 3 (.close 7))) (.step 3 (.close 5))) (.step 3 (.close 4)))) (.step 58 (.step 7 (.step 3 (.close 5))))) (.step 58 (.step 7 (.step 3 (.step 18 (.close 3)))))) (.split 30 0 (.split 43 0 (.split 51 0 (.step 31 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 5 (.step 7 (.step 3 (.close 5)))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041327803083408248821065973113499751072541486551933211826000204806937246280638885736841612676857054114931778701080923298423008684689387355104874351047070765955698995854479893153710080⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 74 1 (.reuse 0) (.run (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 22 0 (.step 31 (.step 7 (.step 27 (.step 5 (.close 7))))) (.step 7 (.close 5))) (.step 11 (.split 25 0 (.step 77 (.step 27 (.step 7 (.step 5 (.close 17))))) (.step 23 (.close 5))))) (.step 11 (.split 25 0 (.step 77 (.step 7 (.close 5))) (.step 3 (.step 18 (.close 17)))))) (.step 11 (.split 25 0 (.step 77 (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.close 17)))))) (.step 31 (.step 7 (.step 5 (.close 14))))) (.step 11 (.step 23 (.step 58 (.split 10 0 (.step 5 (.step 7 (.close 18))) (.step 3 (.step 5 (.close 7)))))))))) (.run (.split 74 1 (.split 14 0 (.split 24 0 (.split 25 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 27))))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301992407735424565354844473286458062706058471700174795441057169795130632859463205865834458500869608102892309963108174047075949985824717818804014437003652828205543131819540480⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 58 1 (.split 59 1 (.reuse 0) (.run (.split 74 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 62 (.step 7 (.step 3 (.step 5 (.close 7))))) (.step 9 (.step 5 (.step 55 (.split 10 0 (.step 27 (.step 7 (.close 16))) (.step 3 (.close 7))))))) (.step 7 (.step 27 (.close 3)))) (.step 7 (.step 27 (.step 7 (.close 3))))) (.step 7 (.step 27 (.step 7 (.step 3 (.close 18)))))) (.step 31 (.step 27 (.step 7 (.step 18 (.step 17 (.close 5))))))) (.split 14 0 (.step 9 (.split 10 0 (.step 27 (.step 31 (.step 3 (.close 5)))) (.step 3 (.close 7)))) (.step 15 (.step 27 (.step 3 (.step 7 (.close 5))))))) (.step 62 (.step 7 (.close 3)))) (.step 27 (.step 31 (.close 44)))))) (.run (.split 59 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 67 1 (.split 30 0 (.step 61 (.step 7 (.step 5 (.step 7 (.close 17))))) (.step 31 (.close 27))) (.step 3 (.step 27 (.step 7 (.close 34))))) (.step 31 (.step 27 (.step 3 (.close 7))))) (.step 3 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 27 (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.step 18 (.step 3 (.close 5))))) (.step 3 (.step 18 (.step 3 (.close 5))))) (.step 27 (.step 18 (.step 5 (.close 3))))))) (.step 11 (.step 27 (.step 61 (.step 3 (.close 7)))))) (.step 27 (.step 44 (.step 61 (.step 5 (.close 7))))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567385983191639432196471305727407451091194415651837569843567242944100769407992952915817967241608698414801901167041341559296257577303673679897066329011341230080⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 10 0 (.split 14 0 (.step 43 (.split 16 0 (.split 2 0 (.split 17 0 (.step 43 (.step 58 (.split 24 0 (.step 7 (.step 55 (.step 9 (.step 5 (.close 7))))) (.step 3 (.close 5))))) (.step 5 (.step 3 (.step 5 (.close 7))))) (.step 5 (.close 3))) (.step 5 (.step 7 (.step 3 (.close 5)))))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 43 (.step 40 (.step 3 (.close 7))))) (.step 5 (.step 3 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 22 (.step 7 (.step 16 (.step 7 (.close 21))))))))))))) (.step 3 (.step 5 (.step 27 (.step 3 (.step 18 (.step 17 (.close 21)))))))))) (.run (.step 58 (.split 58 1 (.step 18 (.step 3 (.step 18 (.step 27 (.step 3 (.step 18 (.close 17))))))) (.step 27 (.step 3 (.step 18 (.step 44 (.close 18)))))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 5783580587434429433761572675456392549017468516331052641474861846568347677163081595709229260282491939531760619404479499147512898852884215439001630765869445112243835179987069140364555358923514818071627199737455200912177889280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 10 0 (.split 24 0 (.step 53 (.step 9 (.step 5 (.close 7)))) (.step 27 (.step 3 (.step 5 (.close 7))))) (.step 7 (.step 31 (.step 7 (.close 27))))) (.step 9 (.step 5 (.step 55 (.split 10 0 (.step 27 (.step 7 (.close 16))) (.step 3 (.close 7))))))) (.step 7 (.step 27 (.close 3)))) (.step 7 (.step 27 (.step 7 (.close 3))))) (.step 7 (.step 27 (.step 7 (.step 3 (.close 18)))))) (.step 31 (.step 27 (.step 7 (.step 18 (.step 17 (.close 5))))))) (.split 14 0 (.step 9 (.split 10 0 (.step 27 (.step 31 (.step 3 (.close 5)))) (.step 3 (.close 7)))) (.step 15 (.step 27 (.step 3 (.step 7 (.close 5))))))) (.split 2 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 40 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 27))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 3 (.step 7 (.step 27 (.close 34))))) (.step 7 (.close 27))) (.step 3 (.close 7)))) (.step 5 (.step 48 (.step 5 (.step 7 (.step 9 (.step 21 (.step 7 (.step 16 (.step 7 (.close 26))))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325437709934763984976463317753067945134267707236722593453332466562980825892572308369042024991633212424945990752120340480⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 24 0 (.split 25 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 27)))))) (.step 70 (.step 3 (.step 7 (.close 3))))) (.step 54 (.step 62 (.step 7 (.close 3))))) (.step 3 (.step 61 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 54)))))))) (.split 58 1 (.split 59 1 (.split 74 1 (.split 51 1 (.reuse 1) (.run (.step 53 (.step 54 (.step 57 (.split 2 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 40 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 27))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 3 (.step 7 (.step 27 (.close 34))))) (.step 7 (.close 27))) (.step 3 (.close 7)))))))) (.run (.step 31 (.step 27 (.step 31 (.step 44 (.step 48 (.step 53 (.close 3))))))))) (.run (.step 53 (.step 62 (.split 56 1 (.step 62 (.step 4 (.step 5 (.close 7)))) (.step 5 (.step 9 (.step 21 (.step 26 (.step 48 (.step 5 (.step 7 (.step 16 (.close 22)))))))))))))) (.run (.step 53 (.step 61 (.step 27 (.step 5 (.step 7 (.close 5)))))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 5783580587434429433761572675456392549017468516331052641474861846568351025844870143977885859820486549729001539326379165700881470718433554510531733408490530692551478029476850275910080630344477629170012367590139960149542961152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 36 0 (.step 52 (.step 3 (.close 5))) (.step 7 (.step 5 (.step 16 (.close 17))))) (.step 7 (.close 3))) (.split 50 0 (.step 31 (.step 3 (.close 5))) (.step 27 (.step 5 (.close 7))))) (.step 7 (.step 27 (.close 3)))) (.step 7 (.step 27 (.step 7 (.close 3))))) (.step 7 (.step 27 (.step 7 (.step 3 (.close 18)))))) (.step 31 (.step 27 (.step 7 (.step 17 (.step 3 (.close 5))))))) (.split 14 0 (.step 9 (.split 10 0 (.step 27 (.step 31 (.step 3 (.close 5)))) (.step 3 (.close 7)))) (.step 15 (.step 27 (.step 3 (.step 7 (.close 5))))))) (.split 2 0 (.split 30 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 43 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.close 27))) (.step 7 (.step 9 (.close 27)))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 7 (.step 9 (.close 27)))) (.step 7 (.close 27))) (.step 3 (.close 7)))) (.step 5 (.step 48 (.step 5 (.step 7 (.step 9 (.step 16 (.step 22 (.step 7 (.step 21 (.close 26))))))))))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 52 (.step 54 (.step 57 (.split 2 0 (.split 30 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 43 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.close 27))) (.step 7 (.step 9 (.close 27)))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 7 (.step 9 (.close 27)))) (.step 7 (.close 27))) (.step 3 (.close 7))))))))
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
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124637754454866599742667208477479669281747166464942958642169071147223905622227400209491941501984933963150481940766734735638528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 24 0 (.split 25 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 11)))) (.step 70 (.step 3 (.step 7 (.close 3))))) (.step 9 (.step 27 (.close 7)))) (.step 3 (.step 11 (.step 27 (.close 7))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 9 (.close 46))))))) (.step 46 (.split 55 1 (.split 56 1 (.split 58 1 (.split 74 1 (.step 46 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 9 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.step 7 (.close 52)))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832323002619724861049712310179709848418892747886638832832090536591190026526158672709466947463058740698884086395262410349871104⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.split 50 1 (.split 58 1 (.split 59 1 (.split 74 1 (.reuse 1) (.run (.step 31 (.step 27 (.step 31 (.step 34 (.step 44 (.step 3 (.step 7 (.step 18 (.step 3 (.step 7 (.close 52))))))))))))) (.run (.step 52 (.step 62 (.split 56 1 (.step 62 (.step 4 (.step 5 (.close 7)))) (.step 5 (.step 9 (.step 26 (.step 48 (.step 5 (.step 16 (.step 22 (.step 7 (.close 21)))))))))))))) (.run (.step 52 (.step 61 (.step 27 (.step 5 (.step 7 (.close 5)))))))) (.run (.step 52 (.split 56 1 (.split 74 1 (.split 2 0 (.split 30 0 (.split 36 0 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 31 (.step 52 (.close 4))))) (.step 31 (.step 52 (.close 4)))) (.step 9 (.step 27 (.step 52 (.close 3))))) (.step 27 (.step 34 (.step 31 (.step 44 (.step 7 (.step 19 (.close 3)))))))) (.step 5 (.step 9 (.step 21 (.step 31 (.step 48 (.step 5 (.step 7 (.step 16 (.step 7 (.step 22 (.step 7 (.close 26))))))))))))))))) (.reuse 2)) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 16 (.step 22 (.step 16 (.close 21))))))))) (.step 23 (.step 31 (.step 44 (.step 31 (.step 7 (.step 21 (.step 28 (.step 16 (.step 22 (.step 16 (.close 45)))))))))))) (.step 23 (.step 31 (.step 44 (.step 58 (.step 55 (.step 9 (.close 52)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587391331344527548635684740417839958361117534975365391953999237345045506882926483056238925061149350123310058574477000704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 10 0 (.step 61 (.split 43 1 (.split 51 1 (.split 55 1 (.split 67 1 (.split 14 0 (.split 17 0 (.split 16 0 (.split 22 0 (.split 40 0 (.split 43 0 (.step 31 (.step 3 (.close 5))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 5 (.step 7 (.step 9 (.step 7 (.step 17 (.step 23 (.close 27)))))))) (.step 27 (.step 3 (.close 7)))) (.step 31 (.step 27 (.step 3 (.close 7))))) (.step 31 (.step 27 (.step 7 (.step 3 (.close 18)))))) (.step 27 (.step 7 (.step 31 (.step 34 (.step 18 (.step 7 (.close 5)))))))) (.step 3 (.step 27 (.step 7 (.close 34))))) (.step 3 (.step 27 (.step 42 (.step 3 (.close 5)))))) (.step 3 (.step 61 (.step 70 (.step 27 (.close 7)))))) (.step 3 (.step 27 (.close 7))))) (.step 5 (.step 31 (.step 27 (.step 31 (.step 18 (.step 3 (.step 7 (.step 27 (.close 42)))))))))) (.step 3 (.step 5 (.step 42 (.close 3))))) (.step 11 (.step 42 (.step 61 (.step 27 (.step 42 (.step 3 (.close 7)))))))) (.step 27 (.step 42 (.step 44 (.step 61 (.step 27 (.step 42 (.step 7 (.step 3 (.close 5)))))))))) (.step 27 (.step 42 (.step 3 (.close 5))))) (.step 21 (.step 27 (.step 42 (.step 53 (.close 3)))))) (.step 27 (.step 42 (.step 52 (.step 61 (.step 27 (.step 42 (.step 5 (.step 7 (.close 5)))))))))) (.step 5 (.step 7 (.step 31 (.step 27 (.close 42)))))) (.step 5 (.step 27 (.step 31 (.close 42))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587391331344527548635684740417839958361117534975365391953999237345045506882926483056238925061149350123310058574477000704⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 40 1 (.reuse 0) (.run (.step 5 (.step 31 (.step 43 (.split 49 1 (.split 50 1 (.split 58 1 (.split 43 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.step 5 (.step 31 (.step 3 (.close 5)))) (.step 31 (.step 3 (.step 5 (.close 9))))) (.step 31 (.close 5))) (.step 31 (.close 5))) (.step 31 (.close 5))) (.step 5 (.step 7 (.step 23 (.step 7 (.step 17 (.step 7 (.close 19)))))))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 27 (.step 31 (.close 44)))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 44)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 27 (.step 7 (.step 31 (.close 61)))))) (.step 5 (.step 9 (.step 23 (.step 27 (.step 31 (.step 44 (.close 53)))))))) (.step 5 (.step 9 (.step 23 (.step 27 (.step 31 (.close 52)))))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567161174868858867513347584291470413161041331859301996181697849386899551940214132596391712908060643501012510066724012294547796739106991340744772394664119607366534003340338273965250815392044308078038367096008798936243372032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 10 0 (.split 14 0 (.step 43 (.split 16 0 (.split 2 0 (.split 17 0 (.step 43 (.step 58 (.split 24 0 (.step 7 (.step 55 (.step 9 (.step 5 (.close 7))))) (.step 3 (.close 5))))) (.step 5 (.step 3 (.step 5 (.close 7))))) (.step 5 (.close 3))) (.step 5 (.step 7 (.step 3 (.close 5)))))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 43 (.step 40 (.step 3 (.close 7))))) (.step 5 (.step 3 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 31 (.step 42 (.step 7 (.step 9 (.step 21 (.step 7 (.close 16)))))))))) (.step 3 (.step 5 (.step 27 (.step 3 (.step 18 (.step 17 (.close 21)))))))) (.step 5 (.step 58 (.split 16 0 (.split 17 0 (.split 22 0 (.split 67 1 (.split 2 0 (.split 14 0 (.split 40 0 (.split 43 0 (.split 51 0 (.step 58 (.step 3 (.close 7))) (.step 28 (.step 3 (.close 7)))) (.step 10 (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 28))))))) (.step 5 (.step 31 (.step 42 (.step 48 (.step 5 (.step 21 (.step 58 (.step 9 (.close 26)))))))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980352459069796044415984113383272240537201631902138452790280430537608988726394880⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.reuse 0) (.step 43 (.split 39 1 (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.reuse 1) (.run (.step 5 (.step 31 (.step 42 (.step 48 (.step 58 (.step 9 (.step 3 (.step 21 (.step 3 (.close 26)))))))))))) (.run (.step 3 (.step 7 (.step 9 (.close 10))))))) (.run (.step 7 (.step 31 (.step 38 (.step 60 (.step 76 (.split 49 1 (.split 55 1 (.split 2 0 (.split 14 0 (.split 24 0 (.split 25 0 (.step 7 (.step 5 (.step 16 (.close 21)))) (.step 28 (.close 5))) (.step 7 (.step 5 (.step 22 (.close 28))))) (.step 7 (.step 5 (.step 16 (.close 28))))) (.step 7 (.step 5 (.close 28)))) (.step 5 (.step 7 (.step 28 (.step 16 (.step 22 (.step 16 (.close 21)))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 28 (.step 22 (.close 41)))))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 5 (.step 27 (.step 23 (.close 42))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567161174868858867508448700980813070724093481457900356580861127784764120506993295057520431419218060921738044943417523009391272218120226127102888292755110437898042445634264267397284093701569286735755765795556080067288236032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 16 (.close 22))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 31 (.step 7 (.step 21 (.step 16 (.step 22 (.step 16 (.close 28)))))))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 55 (.step 57 (.step 9 (.step 31 (.step 7 (.step 16 (.step 21 (.step 28 (.step 21 (.step 28 (.step 29 (.close 52))))))))))))))))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 24 0 (.step 45 (.step 3 (.close 7))) (.step 7 (.step 28 (.step 23 (.close 27))))) (.step 7 (.step 29 (.step 5 (.step 17 (.close 23)))))) (.step 7 (.step 5 (.close 28)))) (.step 5 (.step 7 (.step 29 (.step 5 (.step 23 (.close 17))))))) (.step 7 (.step 5 (.step 22 (.step 23 (.step 29 (.step 31 (.step 16 (.close 21))))))))) (.step 5 (.step 7 (.step 28 (.step 22 (.step 16 (.close 21))))))) (.step 7 (.step 22 (.step 23 (.step 29 (.step 31 (.step 38 (.step 16 (.step 22 (.step 16 (.step 39 (.close 45)))))))))))) (.step 7 (.step 22 (.step 23 (.step 29 (.step 31 (.step 39 (.step 38 (.step 45 (.close 52)))))))))))) (.step 5 (.step 31 (.step 27 (.close 36))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567161174868858867508448700980813070724093481457900356580861127784764120506993295057520431419218060921738044943415174469048243127070140857063541236296179033470779622998206511325740985640246549472453012178048804635863416832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 15 (.step 23 (.step 31 (.step 34 (.step 31 (.step 7 (.step 16 (.step 21 (.step 22 (.step 28 (.step 22 (.close 37))))))))))))) (.step 15 (.step 16 (.step 23 (.step 31 (.step 34 (.step 55 (.step 9 (.step 52 (.step 5 (.step 7 (.close 16)))))))))))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 24 0 (.step 37 (.step 7 (.step 29 (.step 31 (.close 16))))) (.step 7 (.step 28 (.step 23 (.close 27))))) (.step 7 (.step 29 (.step 5 (.step 17 (.close 23)))))) (.step 7 (.step 5 (.close 28)))) (.step 5 (.step 7 (.step 29 (.step 5 (.step 17 (.close 23))))))) (.step 7 (.step 5 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22))))))))) (.step 5 (.step 7 (.step 28 (.close 37))))) (.step 7 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37))))))))) (.step 7 (.step 16 (.step 17 (.step 29 (.step 31 (.close 52))))))))) (.step 5 (.step 31 (.step 27 (.close 34))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083263539908491211970054889756714969801218740098112058511620808618076414924809799870963365445632⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 16 (.step 31 (.step 38 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 42 1 (.split 24 0 (.split 25 0 (.step 7 (.step 5 (.step 16 (.close 21)))) (.step 28 (.close 5))) (.step 7 (.step 5 (.step 22 (.close 28))))) (.step 28 (.close 37))) (.step 7 (.step 5 (.step 16 (.step 28 (.step 5 (.step 31 (.close 37)))))))) (.step 7 (.step 5 (.step 28 (.step 5 (.step 31 (.close 37))))))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 28 (.step 22 (.close 37))))))))) (.step 5 (.step 7 (.step 28 (.step 37 (.close 21))))))))))) (.run (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 38 1 (.split 42 1 (.split 24 0 (.step 37 (.step 7 (.step 29 (.step 31 (.close 16))))) (.step 7 (.step 28 (.step 23 (.close 27))))) (.step 37 (.close 29))) (.step 28 (.close 37))) (.step 7 (.step 29 (.step 31 (.close 37))))) (.step 7 (.step 28 (.step 5 (.step 31 (.close 37)))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 5 (.close 37))))))) (.step 7 (.step 22 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.step 22 (.step 21 (.close 37))))))))))) (.step 5 (.step 7 (.step 28 (.close 37))))) (.step 7 (.step 22 (.step 23 (.step 29 (.step 31 (.close 37))))))) (.step 7 (.step 16 (.step 17 (.step 29 (.step 31 (.step 37 (.close 52)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546456141158202403379179379791566505724447871444758525769306109563207669548843008⟩
def references : Fin 3 → Box := ![Part12.root, Part13.root, Part15.root]
def proof : Chunks.Proof 3 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 38 1 (.reuse 1) (.run (.step 31 (.step 38 (.split 49 1 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 42 1 (.split 24 0 (.split 25 0 (.step 7 (.step 5 (.step 16 (.close 21)))) (.step 28 (.close 5))) (.step 7 (.step 5 (.step 22 (.close 28))))) (.step 28 (.step 39 (.close 5)))) (.step 7 (.step 5 (.step 28 (.step 5 (.step 16 (.step 31 (.close 37)))))))) (.step 7 (.step 5 (.step 28 (.step 5 (.step 31 (.step 37 (.close 39)))))))) (.step 3 (.step 5 (.step 28 (.close 39))))) (.step 5 (.step 7 (.step 21 (.step 22 (.step 16 (.close 28))))))) (.step 5 (.step 7 (.step 28 (.step 38 (.step 22 (.close 39))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 28 (.close 39))))))))))))))) (.reuse 2)) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 3 (.step 18 (.step 7 (.step 17 (.close 19))))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 7 (.close 31)))))))) (.step 7 (.step 31 (.step 53 (.step 7 (.step 3 (.step 27 (.step 7 (.close 31))))))))) (.step 3 (.step 31 (.step 27 (.close 42))))) (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124637754454866599742667208477479669281747166464944767893563404212777398918868160958052148845495334596963598465516858378289152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 10 0 (.split 14 0 (.step 43 (.split 16 0 (.split 2 0 (.split 17 0 (.step 43 (.step 58 (.split 24 0 (.step 7 (.step 29 (.close 3))) (.step 3 (.close 5))))) (.step 5 (.step 3 (.step 5 (.close 7))))) (.step 5 (.close 3))) (.step 5 (.step 7 (.step 3 (.close 5)))))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 43 (.step 29 (.step 3 (.close 7))))) (.step 5 (.step 3 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 9 (.step 26 (.step 27 (.step 7 (.step 26 (.step 7 (.step 16 (.close 21)))))))))) (.step 3 (.step 5 (.close 27)))) (.step 5 (.step 58 (.split 16 0 (.split 17 0 (.split 22 0 (.split 67 1 (.split 2 0 (.split 14 0 (.split 40 0 (.step 29 (.step 28 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7))))))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 28 (.close 26))))))) (.step 5 (.step 27 (.step 48 (.step 5 (.step 9 (.step 58 (.close 26)))))))) (.step 5 (.step 27 (.step 48 (.step 9 (.step 58 (.step 3 (.step 21 (.step 3 (.close 26)))))))))) (.step 3 (.step 7 (.step 9 (.close 10)))))))
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
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212404732723200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176443801223117202671504767215926594615752823278738184209563994484113408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 10 0 (.step 61 (.step 27 (.split 14 0 (.split 43 1 (.split 51 1 (.split 67 1 (.split 16 0 (.split 17 0 (.step 27 (.close 3)) (.step 31 (.close 27))) (.step 31 (.close 27))) (.step 3 (.step 27 (.close 7)))) (.step 3 (.step 54 (.step 27 (.close 7))))) (.step 3 (.step 27 (.close 7)))) (.step 27 (.step 3 (.close 7)))))) (.step 5 (.step 31 (.step 27 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.step 27 (.split 16 0 (.split 17 0 (.split 22 0 (.split 51 0 (.step 27 (.close 3)) (.step 3 (.step 5 (.close 23)))) (.step 3 (.close 27))) (.step 3 (.step 18 (.close 27)))) (.step 18 (.step 3 (.close 27)))))))) (.step 11 (.step 27 (.step 23 (.step 18 (.close 5)))))) (.step 27 (.step 9 (.step 31 (.close 27))))) (.step 27 (.close 61))) (.step 27 (.step 9 (.step 31 (.close 27))))) (.step 27 (.step 9 (.step 31 (.close 27))))) (.step 5 (.step 7 (.step 27 (.step 7 (.close 27)))))) (.step 5 (.close 27))) (.step 27 (.step 31 (.step 27 (.step 42 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 29 (.step 5 (.close 27)))))) (.step 5 (.step 7 (.step 29 (.close 27))))) (.step 5 (.step 7 (.step 29 (.close 27))))) (.step 3 (.step 7 (.step 18 (.step 29 (.step 31 (.close 27))))))) (.step 3 (.step 5 (.step 27 (.step 29 (.step 27 (.step 5 (.close 28)))))))))
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
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933904369533342669925600264592995344063459753984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.step 27 (.step 19 (.close 17))))))) (.step 11 (.step 44 (.step 61 (.step 18 (.split 16 0 (.step 7 (.step 17 (.close 19))) (.step 42 (.step 7 (.step 17 (.close 19)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 44 (.step 48 (.step 11 (.step 23 (.step 27 (.step 25 (.step 31 (.step 19 (.step 44 (.step 19 (.step 17 (.step 42 (.close 53))))))))))))))) (.step 4 (.step 44 (.step 48 (.step 55 (.step 27 (.step 52 (.step 7 (.step 17 (.close 19)))))))))) (.step 7 (.step 5 (.step 19 (.step 20 (.step 19 (.step 25 (.close 27)))))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 42 (.close 7))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 18 (.step 5 (.close 7)))))) (.step 18 (.step 11 (.step 27 (.step 18 (.split 16 0 (.step 7 (.step 17 (.close 19))) (.step 42 (.step 7 (.step 17 (.close 19)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933904369533342669925600264592995344063459753984⟩
def references : Fin 4 → Box := ![Part16.root, Part17.root, Part18.root, Part19.root]
def proof : Chunks.Proof 4 := (.split 22 1 (.split 24 1 (.split 25 1 (.reuse 0) (.step 43 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.reuse 1) (.run (.step 7 (.step 28 (.step 5 (.step 7 (.step 5 (.step 28 (.step 16 (.step 21 (.close 29))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 27 (.step 3 (.step 5 (.close 28))))))))) (.run (.step 10 (.step 28 (.step 5 (.step 58 (.split 16 0 (.split 17 0 (.split 22 0 (.split 51 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 40 0 (.step 29 (.step 28 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 28))))))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7)))) (.step 5 (.step 3 (.close 7)))))))))) (.run (.step 7 (.step 28 (.step 5 (.step 7 (.step 5 (.step 22 (.step 28 (.step 16 (.step 21 (.close 29)))))))))))) (.run (.step 7 (.step 16 (.step 28 (.step 5 (.step 7 (.step 5 (.step 16 (.step 21 (.step 22 (.step 21 (.step 22 (.close 28)))))))))))))) (.run (.step 3 (.close 7)))))) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887741921183602025394990783539550081939716890900475722877452848141279845371871232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.step 27 (.step 19 (.close 17))))))) (.step 11 (.step 61 (.step 3 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 48 (.step 11 (.step 23 (.step 27 (.step 53 (.step 7 (.step 19 (.step 17 (.close 20))))))))))) (.step 4 (.step 48 (.step 55 (.step 27 (.step 52 (.step 7 (.step 17 (.step 19 (.close 20)))))))))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 42 (.close 7))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 18 (.step 5 (.close 7)))))) (.step 18 (.step 11 (.step 27 (.step 18 (.step 61 (.step 7 (.step 17 (.close 19))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587988511580996377930910498868966066807471738383761408⟩
def references : Fin 2 → Box := ![Part20.root, Part21.root]
def proof : Chunks.Proof 2 := (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.split 24 1 (.split 25 1 (.split 38 1 (.step 25 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 24 0 (.split 25 0 (.step 20 (.step 3 (.close 4))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.close 20)))) (.step 7 (.step 18 (.close 5)))) (.step 7 (.step 18 (.step 20 (.step 17 (.close 19)))))) (.step 11 (.step 18 (.step 20 (.step 19 (.close 27)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 20 (.step 25 (.step 27 (.close 53))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 27 (.step 52 (.step 19 (.close 20))))))))) (.step 7 (.step 5 (.step 18 (.step 19 (.close 20)))))) (.step 11 (.step 18 (.step 19 (.step 42 (.step 20 (.close 7)))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 28))))))) (.step 11 (.step 18 (.step 20 (.step 27 (.step 20 (.step 7 (.step 17 (.close 19))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887741921183602025394990783538054965764727377215153353293584090612171826380406784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 77 (.step 7 (.close 5))))) (.step 7 (.step 18 (.step 19 (.close 17))))) (.step 11 (.step 42 (.step 18 (.step 61 (.close 7)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 42 (.step 48 (.step 11 (.step 23 (.step 27 (.step 7 (.step 19 (.step 44 (.step 17 (.step 19 (.close 53))))))))))))) (.step 4 (.step 42 (.step 48 (.step 52 (.step 7 (.step 17 (.step 19 (.close 27))))))))) (.step 7 (.step 5 (.close 19)))) (.step 11 (.step 18 (.step 42 (.close 3))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 18 (.step 5 (.close 7)))))) (.step 18 (.step 11 (.step 27 (.step 18 (.step 42 (.step 7 (.step 17 (.close 19))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887741921183603710391657480453042132453170315942070455615110499397951895356047360⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.step 19 (.step 7 (.close 5))) (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 19 (.step 17 (.step 20 (.step 25 (.close 27)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 27 (.close 53))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 27 (.step 19 (.step 42 (.step 25 (.close 52)))))))))) (.step 7 (.step 5 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 27 (.close 42)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 28))))))) (.step 11 (.step 18 (.step 27 (.step 19 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471302562167710183240140658823675005889574605545923938323012521944977946186874880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 56 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 74 1 (.split 2 0 (.split 16 0 (.split 25 0 (.split 17 0 (.step 27 (.step 7 (.step 5 (.close 17)))) (.step 11 (.step 61 (.step 7 (.close 17))))) (.step 27 (.close 3))) (.step 11 (.split 25 0 (.split 17 0 (.step 42 (.step 7 (.close 17))) (.step 17 (.step 3 (.close 7)))) (.step 7 (.step 17 (.step 3 (.close 5))))))) (.step 11 (.step 23 (.step 5 (.step 7 (.close 17)))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 31 (.split 2 0 (.step 7 (.step 11 (.split 16 0 (.split 17 0 (.step 31 (.split 22 0 (.split 24 0 (.step 7 (.close 17)) (.step 17 (.close 3))) (.step 3 (.step 7 (.close 17))))) (.step 7 (.close 17))) (.step 7 (.close 17))))) (.step 3 (.step 5 (.step 3 (.step 7 (.close 17)))))))) (.step 31 (.split 2 0 (.step 7 (.step 11 (.step 17 (.step 3 (.close 7))))) (.step 3 (.step 5 (.step 3 (.step 7 (.close 15)))))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 27)))))) (.step 3 (.step 5 (.step 3 (.close 17))))) (.step 31 (.step 27 (.step 44 (.step 23 (.step 55 (.step 23 (.close 17)))))))) (.step 11 (.step 17 (.step 61 (.step 5 (.close 7)))))) (.step 5 (.step 18 (.step 27 (.step 31 (.step 34 (.step 48 (.step 5 (.step 17 (.step 5 (.close 21))))))))))) (.step 3 (.step 31 (.step 61 (.step 3 (.step 7 (.step 27 (.step 17 (.step 34 (.close 44)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457950409596736444732873088207266474401875363177090349465208479998315785617408⟩
def references : Fin 1 → Box := ![Part25.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 31 (.step 27 (.step 48 (.step 61 (.split 51 1 (.split 59 1 (.split 67 1 (.step 23 (.step 55 (.step 23 (.close 17)))) (.step 3 (.step 7 (.step 17 (.step 34 (.close 44)))))) (.step 44 (.step 23 (.step 31 (.close 17))))) (.step 3 (.step 7 (.step 52 (.step 44 (.step 17 (.close 53))))))))))))) (.run (.step 17 (.step 31 (.step 27 (.step 34 (.step 48 (.step 52 (.step 23 (.step 31 (.step 17 (.close 3)))))))))))) (.run (.step 3 (.step 8 (.step 11 (.step 3 (.step 7 (.step 11 (.close 27))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 17 (.close 7))))))) (.run (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 23 (.step 17 (.close 27)))))))))) (.run (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.step 61 (.step 27 (.step 42 (.step 3 (.close 7)))))))))))) (.run (.step 3 (.step 5 (.step 31 (.step 42 (.step 63 (.step 49 (.step 5 (.close 17)))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 36 (.step 7 (.step 5 (.step 29 (.step 5 (.step 31 (.step 5 (.close 37)))))))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 34 (.step 7 (.step 29 (.step 5 (.step 31 (.step 5 (.close 37))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 7 (.step 11 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 27 (.step 29 (.step 63 (.step 49 (.step 5 (.close 17))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408736866500144765482531916910428160⟩
def references : Fin 1 → Box := ![Part26.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.reuse 0) (.run (.step 11 (.step 27 (.step 11 (.step 31 (.step 42 (.step 27 (.step 23 (.step 18 (.close 5))))))))))) (.run (.step 7 (.step 18 (.step 27 (.split 25 1 (.step 11 (.split 38 1 (.step 17 (.split 40 1 (.split 50 1 (.split 56 1 (.step 17 (.step 7 (.close 5))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17))))) (.step 3 (.step 5 (.close 17))))) (.step 3 (.step 5 (.close 17))))))))) (.run (.step 7 (.step 18 (.step 27 (.step 61 (.step 74 (.step 11 (.split 22 1 (.split 25 1 (.step 17 (.split 38 1 (.step 17 (.step 7 (.step 5 (.step 7 (.close 17))))) (.step 3 (.step 5 (.close 17))))) (.step 3 (.step 5 (.close 17)))) (.step 17 (.step 5 (.step 7 (.close 5))))))))))))) (.run (.step 7 (.step 18 (.step 19 (.step 27 (.step 42 (.step 67 (.step 11 (.split 25 1 (.step 17 (.split 40 1 (.split 50 1 (.split 56 1 (.step 17 (.step 7 (.close 5))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17))))) (.step 3 (.step 5 (.close 17)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413613633536⟩
def references : Fin 3 → Box := ![Part22.root, Part24.root, Part27.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.step 7 (.step 18 (.split 17 1 (.reuse 1) (.run (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.step 19 (.step 7 (.close 5))) (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 19 (.step 17 (.step 20 (.close 27))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 27 (.close 53))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 27 (.step 19 (.step 42 (.step 20 (.close 52)))))))))) (.step 7 (.step 5 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 27 (.close 42)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))) (.step 4 (.step 5 (.step 7 (.step 18 (.step 5 (.close 28))))))) (.step 11 (.step 18 (.step 27 (.step 19 (.close 7)))))))))))) (.reuse 2)) (.run (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 3 (.step 18 (.step 7 (.step 17 (.close 19))))))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 7 (.close 31)))))))) (.step 7 (.step 31 (.step 52 (.close 7))))) (.step 3 (.step 31 (.step 27 (.close 42))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 31 (.close 27)))) (.step 3 (.step 17 (.step 3 (.step 7 (.close 17)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part24.excludes
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413614682112⟩
def references : Fin 1 → Box := ![Part28.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 5 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 5 (.split 39 1 (.step 3 (.step 5 (.step 27 (.step 23 (.step 61 (.step 3 (.step 17 (.step 21 (.step 17 (.close 23)))))))))) (.step 5 (.step 21 (.step 27 (.step 23 (.close 42))))))) (.step 5 (.close 28))) (.step 3 (.step 5 (.step 28 (.close 39))))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 5 (.close 28))) (.step 5 (.close 27))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.step 18 (.close 19)))))) (.step 5 (.step 17 (.step 23 (.step 17 (.close 27))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part28.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part29

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part29.excludes
end FiveColour.Packed.EnumerationChunks.Case139
