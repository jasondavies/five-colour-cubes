module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case26
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413614682112⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301992407735424565354844473286458062706058471700174795441057169795130632859463205865834458500869608102892309963108174047075949985824717818804014437003652828205543131819540480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 24 0 (.step 7 (.step 31 (.step 9 (.close 58)))) (.split 34 0 (.split 36 0 (.step 27 (.close 3)) (.step 5 (.close 7))) (.step 7 (.close 5)))) (.step 7 (.close 5))) (.step 7 (.step 27 (.close 31)))) (.split 10 0 (.split 14 0 (.split 24 0 (.step 5 (.close 7)) (.step 3 (.close 27))) (.split 30 0 (.split 43 0 (.step 31 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 5 (.step 3 (.close 7))))) (.split 2 0 (.split 10 0 (.split 14 0 (.step 7 (.step 27 (.close 31))) (.step 11 (.step 77 (.step 27 (.close 31))))) (.step 7 (.close 5))) (.step 23 (.step 5 (.close 3))))) (.split 74 1 (.split 14 0 (.split 24 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 27))))) (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.step 5 (.close 7))) (.step 7 (.close 3))) (.step 7 (.close 55))) (.step 27 (.step 7 (.close 55)))) (.step 7 (.close 3))) (.step 27 (.step 31 (.close 3)))) (.step 23 (.step 27 (.step 7 (.close 44))))) (.step 62 (.close 7)))) (.split 2 0 (.split 10 0 (.split 59 1 (.split 67 1 (.step 61 (.close 31)) (.step 3 (.step 27 (.close 61)))) (.step 27 (.step 31 (.close 61)))) (.step 31 (.close 61))) (.step 3 (.step 27 (.step 31 (.close 61)))))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471302562167710183240140658823675005888180808971015774376666539552937423592751104⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.split 2 0 (.step 7 (.step 5 (.close 7))) (.step 3 (.close 5)))) (.step 5 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 48 (.step 5 (.close 58))))))) (.run (.step 58 (.step 3 (.step 27 (.close 48)))))) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 25 0 (.split 38 0 (.step 54 (.step 7 (.close 3))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.step 11 (.close 44))))) (.step 54 (.close 7))) (.step 3 (.step 54 (.close 61)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.close 54))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648367788162588456525916099996604360235085837362406836571939520537194905761480704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 55 1 (.split 56 1 (.step 62 (.split 74 1 (.split 14 0 (.split 17 0 (.split 58 1 (.split 67 1 (.split 22 0 (.split 24 0 (.step 52 (.step 5 (.close 7))) (.step 27 (.close 3))) (.step 7 (.close 3))) (.step 52 (.close 7))) (.step 27 (.step 31 (.close 3)))) (.step 27 (.step 7 (.close 3)))) (.step 27 (.step 31 (.close 34)))) (.step 27 (.step 23 (.step 7 (.step 17 (.step 7 (.close 44)))))))) (.step 48 (.step 5 (.close 58)))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 48 (.step 55 (.step 27 (.close 52))))) (.step 31 (.step 58 (.step 52 (.step 7 (.step 27 (.close 31))))))) (.step 5 (.step 27 (.step 58 (.step 61 (.step 62 (.step 31 (.step 3 (.close 5))))))))) (.step 54 (.step 57 (.step 52 (.close 7))))) (.step 52 (.split 74 1 (.split 30 0 (.step 52 (.step 55 (.close 52))) (.step 31 (.step 7 (.close 52)))) (.step 27 (.step 31 (.close 52)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294554124637754454866599742667208477479669281747166464942958642169071147223905622227400209491941501984933963150481940766734735638528⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 55 1 (.split 56 1 (.step 62 (.split 74 1 (.split 14 0 (.split 17 0 (.split 58 1 (.split 67 1 (.split 22 0 (.split 24 0 (.step 53 (.step 5 (.close 7))) (.step 27 (.close 3))) (.step 7 (.close 3))) (.step 53 (.close 7))) (.step 27 (.step 31 (.close 3)))) (.step 27 (.step 7 (.close 3)))) (.step 27 (.step 31 (.close 34)))) (.step 27 (.step 23 (.step 44 (.step 7 (.close 17))))))) (.step 48 (.step 5 (.close 58)))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 48 (.step 55 (.step 27 (.close 53))))) (.step 31 (.step 58 (.split 58 1 (.step 7 (.step 52 (.step 7 (.close 27)))) (.step 27 (.step 31 (.close 44))))))) (.step 5 (.step 27 (.step 58 (.step 61 (.step 62 (.step 31 (.step 3 (.close 5))))))))) (.step 54 (.step 57 (.step 53 (.close 7))))))) (.reuse 1)) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 24 0 (.split 25 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 7 (.close 9))) (.step 3 (.step 7 (.close 27)))) (.step 7 (.close 27))) (.step 7 (.close 11))) (.step 46 (.close 7))) (.step 27 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.split 55 1 (.step 54 (.step 3 (.step 7 (.close 3)))) (.step 3 (.close 46)))) (.step 9 (.close 53))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587391331344527548635684740417839958361117534975365391953999237345045506882926483056238925061149350123310058574477000704⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 58 (.split 49 1 (.step 31 (.step 7 (.step 31 (.close 45)))) (.step 44 (.step 31 (.step 7 (.close 45)))))))) (.run (.step 43 (.split 49 1 (.split 43 1 (.split 50 1 (.split 51 1 (.split 58 1 (.step 31 (.step 27 (.split 59 1 (.step 43 (.close 7)) (.step 5 (.close 62))))) (.step 5 (.step 27 (.step 31 (.close 44))))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 31 (.close 53)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 31 (.close 52))))))) (.run (.split 40 1 (.split 42 1 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 2 0 (.split 10 0 (.split 55 1 (.split 59 1 (.split 67 1 (.step 42 (.step 27 (.close 31))) (.step 3 (.step 27 (.close 42)))) (.step 27 (.step 31 (.close 42)))) (.step 42 (.step 3 (.close 5)))) (.step 31 (.step 18 (.step 27 (.close 31))))) (.step 3 (.step 27 (.step 31 (.close 42))))) (.step 3 (.step 42 (.step 54 (.step 27 (.step 7 (.close 34))))))) (.step 27 (.step 42 (.close 53)))) (.step 42 (.close 52))) (.step 27 (.close 7)))) (.step 31 (.close 42))) (.step 5 (.step 27 (.step 31 (.close 42)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263365873409341085735697933769689486445478593324303984090563212069410657016746896253979428922377691758329856⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 43 (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 42 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.split 2 0 (.step 7 (.step 5 (.close 7))) (.step 3 (.close 5)))) (.step 5 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 42 (.close 58)))) (.step 5 (.step 43 (.step 28 (.step 7 (.close 58)))))) (.step 3 (.step 7 (.close 54)))) (.step 31 (.step 21 (.step 42 (.step 7 (.step 9 (.close 21))))))) (.step 42 (.step 58 (.close 26)))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 5 (.close 58)))))))) (.run (.step 31 (.split 38 1 (.split 39 1 (.split 42 1 (.step 58 (.split 49 1 (.step 31 (.step 7 (.step 29 (.step 31 (.close 22))))) (.step 36 (.step 31 (.step 7 (.close 58)))))) (.step 7 (.step 31 (.close 45)))) (.step 31 (.close 36))) (.step 38 (.split 42 1 (.step 7 (.step 5 (.close 41))) (.step 28 (.step 7 (.step 5 (.close 39))))))))))
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
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457950409596736444732873088207266473008078788268926403119226087957793191493632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 43 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 27 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.split 2 0 (.step 7 (.step 5 (.close 7))) (.step 3 (.close 5)))) (.step 5 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 26 (.step 27 (.close 28))))) (.step 5 (.step 43 (.step 28 (.close 4))))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 9 (.step 27 (.close 58))))) (.step 27 (.step 58 (.close 26)))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 29)))) (.step 28 (.step 43 (.step 58 (.step 28 (.close 4)))))) (.step 28 (.step 7 (.close 29)))) (.step 28 (.step 7 (.close 29)))) (.step 3 (.close 7)))))
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176443801223117202671504767215926594615752823278738184209563994484113408⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 29 (.step 31 (.close 37))))) (.step 34 (.step 31 (.step 7 (.close 16))))) (.step 7 (.step 31 (.close 45)))) (.step 31 (.close 34))) (.step 16 (.step 31 (.step 38 (.step 45 (.step 7 (.step 5 (.close 41)))))))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.step 37 (.step 7 (.step 29 (.close 31)))) (.step 7 (.step 31 (.close 37)))) (.step 5 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37))))))))) (.run (.step 18 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 3 (.step 7 (.close 31))))) (.step 31 (.step 7 (.close 52)))) (.step 31 (.close 42))) (.step 3 (.close 7)))))) (.reuse 1)) (.run (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 2 0 (.split 10 0 (.step 42 (.step 27 (.split 43 1 (.split 51 1 (.split 67 1 (.step 31 (.close 27)) (.step 3 (.step 27 (.close 7)))) (.step 3 (.step 27 (.close 7)))) (.step 27 (.close 7))))) (.step 5 (.step 27 (.step 7 (.close 27))))) (.step 5 (.step 27 (.close 3)))) (.step 5 (.step 27 (.close 31)))) (.step 29 (.close 27))) (.step 29 (.close 27))) (.step 31 (.close 27))) (.step 27 (.step 29 (.step 5 (.close 3)))))))
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
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587988511580996377930910498868966066807471738383761408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 22 1 (.split 24 1 (.split 25 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.close 62)))) (.step 18 (.close 61))) (.step 7 (.step 5 (.close 18)))) (.step 31 (.step 48 (.step 23 (.step 27 (.step 7 (.step 19 (.close 44)))))))) (.step 4 (.step 48 (.step 11 (.step 23 (.step 27 (.step 52 (.close 19)))))))) (.step 7 (.step 5 (.close 20)))) (.step 11 (.step 42 (.step 18 (.step 19 (.step 7 (.close 20))))))) (.step 7 (.step 18 (.close 5)))) (.step 27 (.step 18 (.step 7 (.close 19))))) (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 25 (.step 7 (.step 5 (.step 7 (.close 18))))) (.step 18 (.step 20 (.close 19)))) (.step 7 (.close 20))) (.step 7 (.step 19 (.step 20 (.close 27))))) (.step 7 (.step 27 (.step 20 (.close 52))))) (.step 18 (.step 19 (.step 20 (.close 42))))) (.step 7 (.step 18 (.close 5)))) (.step 7 (.step 18 (.close 5)))) (.step 11 (.step 18 (.step 27 (.close 20)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973082633708833828702553798783090491394316304384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.close 19))) (.step 18 (.step 42 (.step 7 (.close 61))))) (.step 7 (.step 5 (.close 18)))) (.step 42 (.step 7 (.step 27 (.step 19 (.close 17)))))) (.step 42 (.step 48 (.step 27 (.step 7 (.close 52)))))) (.step 42 (.close 3))) (.step 7 (.step 18 (.close 5)))) (.step 27 (.step 18 (.step 7 (.close 19))))) (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.close 7)) (.step 18 (.step 19 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 19 (.close 27)))) (.step 7 (.step 27 (.step 19 (.close 52))))) (.step 7 (.step 5 (.close 19)))) (.step 19 (.close 42))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 5)))) (.step 11 (.step 18 (.step 27 (.close 19)))))) (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.close 7)) (.step 18 (.step 19 (.close 7)))) (.step 7 (.close 20))) (.step 7 (.step 19 (.close 27)))) (.step 7 (.step 27 (.step 19 (.close 52))))) (.step 7 (.step 5 (.close 19)))) (.step 19 (.close 42))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 5)))) (.step 11 (.step 18 (.step 27 (.close 19))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176443801223117202671504767217320391190660987225084166601604517078237184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 38 1 (.split 56 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 16 0 (.step 27 (.step 7 (.close 31))) (.step 7 (.step 17 (.close 3)))) (.step 23 (.close 5))) (.step 11 (.close 77))) (.step 27 (.step 23 (.close 17)))) (.step 5 (.close 17))) (.step 5 (.close 17))) (.step 5 (.step 31 (.step 7 (.step 11 (.step 77 (.step 7 (.close 5)))))))) (.step 5 (.step 17 (.step 31 (.close 7))))) (.step 3 (.step 7 (.close 77)))) (.step 17 (.step 42 (.step 27 (.step 31 (.close 61)))))) (.step 5 (.step 18 (.step 27 (.step 17 (.step 5 (.step 23 (.close 17)))))))) (.step 7 (.step 18 (.step 3 (.step 27 (.close 77)))))) (.step 31 (.step 27 (.step 55 (.step 61 (.step 62 (.step 23 (.step 31 (.close 53))))))))) (.step 31 (.step 27 (.step 34 (.step 31 (.step 34 (.close 52))))))) (.step 7 (.close 27))) (.step 5 (.step 7 (.close 31)))) (.step 5 (.step 7 (.step 23 (.close 17))))) (.step 17 (.step 31 (.step 42 (.close 5))))) (.step 31 (.step 7 (.step 5 (.close 28))))) (.step 31 (.step 7 (.close 37)))) (.step 31 (.close 7))) (.step 27 (.step 29 (.step 5 (.close 17))))) (.step 27 (.step 31 (.step 27 (.step 5 (.close 17)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413613633536⟩
def references : Fin 4 → Box := ![Part7.root, Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 24 1 (.split 25 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.close 62))) (.step 18 (.step 44 (.close 61)))) (.step 7 (.step 5 (.close 18)))) (.step 31 (.step 44 (.step 48 (.step 23 (.step 27 (.close 53))))))) (.step 4 (.step 48 (.step 11 (.step 23 (.step 27 (.step 44 (.close 52)))))))) (.step 7 (.step 5 (.close 25)))) (.step 11 (.step 42 (.step 18 (.step 19 (.step 7 (.close 20))))))) (.step 7 (.step 18 (.close 5)))) (.step 27 (.step 18 (.step 7 (.close 19))))))))) (.reuse 1)) (.reuse 2)) (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 3) (.run (.step 7 (.step 11 (.step 18 (.split 25 1 (.split 38 1 (.step 17 (.step 7 (.close 5))) (.step 5 (.close 17))) (.step 5 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 18 (.step 74 (.step 17 (.step 20 (.split 25 1 (.step 17 (.step 7 (.close 5))) (.step 5 (.close 17))))))))))) (.run (.step 7 (.step 11 (.step 18 (.step 19 (.step 67 (.split 25 1 (.step 17 (.step 7 (.close 5))) (.step 5 (.close 17))))))))))) (.run (.step 18 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 3 (.step 7 (.close 31))))) (.step 31 (.step 7 (.close 52)))) (.step 31 (.close 42))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 31 (.close 27))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134150744993711933413614682112⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 34 1 (.split 36 1 (.step 5 (.step 3 (.step 27 (.step 23 (.step 21 (.step 23 (.close 42))))))) (.step 3 (.step 5 (.close 28)))) (.step 5 (.close 37))) (.step 5 (.close 28))) (.step 5 (.close 27))) (.step 4 (.step 5 (.close 18)))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 5 (.step 23 (.close 17)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case26
