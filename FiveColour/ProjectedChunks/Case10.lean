module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case10
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134153162845351164870987350016⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18740915245514405755619, 5789228615351851010618494880448709935079879776571393911013839255768432661963521880064360904848620755638098170412487433395995188289264892881255633757817586178196485084283839045905928401896080274871501735988781987986060346368, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301992407735424565354844473286458062706058471700174795441057169795130632859463205865834458500869608102892309963108174047075949985824717818804014437004861754025158860505874432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.step 7 (.step 27 (.split 8 0 (.step 7 (.step 31 (.step 3 (.close 7)))) (.step 7 (.step 11 (.close 5)))))) (.split 8 0 (.split 4 0 (.split 10 0 (.split 30 0 (.step 27 (.step 3 (.close 5))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 7)))) (.split 4 0 (.split 10 0 (.split 14 0 (.step 3 (.step 5 (.close 3))) (.step 8 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.split 2 0 (.split 8 0 (.step 7 (.step 27 (.step 7 (.close 5)))) (.step 11 (.close 3))) (.step 11 (.step 23 (.step 5 (.close 3)))))) (.step 7 (.step 3 (.step 7 (.close 11))))) (.split 67 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 4 0 (.split 10 0 (.split 14 0 (.step 31 (.split 16 0 (.step 62 (.step 3 (.step 4 (.close 7)))) (.step 7 (.close 3)))) (.step 7 (.step 23 (.step 18 (.close 5))))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.step 9 (.close 11)))) (.step 9 (.step 27 (.step 7 (.step 3 (.close 5)))))) (.step 23 (.step 27 (.step 7 (.step 11 (.step 3 (.step 7 (.close 17)))))))) (.step 44 (.step 62 (.close 7))))) (.split 59 1 (.split 67 1 (.split 74 1 (.step 31 (.step 27 (.close 61))) (.step 11 (.step 27 (.step 7 (.step 31 (.step 44 (.step 3 (.close 5)))))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 31 (.step 44 (.step 31 (.step 3 (.step 21 (.close 8))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471302562167710183240140658823675005888180808971015774377875465372553152279085056⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 58 (.step 3 (.step 4 (.close 7)))))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.close 7)))))))))) (.run (.step 58 (.step 3 (.step 18 (.step 27 (.step 3 (.step 18 (.close 11))))))))) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 24 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 54 (.step 3 (.close 7)))) (.step 3 (.step 27 (.step 7 (.step 11 (.step 34 (.close 44))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648367788162588456525916099996604360235085837362406836573148446356810634447814656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 58 1 (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 67 1 (.split 4 0 (.step 52 (.step 31 (.split 10 0 (.split 17 0 (.step 52 (.step 3 (.step 4 (.close 7)))) (.step 7 (.close 3))) (.step 7 (.close 3))))) (.step 7 (.close 3))) (.step 52 (.step 4 (.close 7)))) (.step 7 (.step 27 (.close 7)))) (.step 7 (.step 27 (.step 7 (.step 17 (.step 23 (.close 17))))))) (.step 9 (.step 27 (.step 7 (.step 9 (.step 7 (.step 11 (.close 3)))))))) (.step 27 (.step 23 (.step 31 (.step 11 (.step 7 (.step 17 (.step 7 (.close 18))))))))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21))))))))))) (.step 48 (.step 52 (.close 58)))) (.step 5 (.step 9 (.step 27 (.step 31 (.step 3 (.step 5 (.close 17)))))))) (.step 52 (.step 7 (.close 3)))) (.step 27 (.step 52 (.step 31 (.step 34 (.close 61)))))) (.step 52 (.step 4 (.step 5 (.step 7 (.close 5)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648367788162588456525916099996604360235085837362406836573148446356810634447814656⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 58 1 (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 67 1 (.split 4 0 (.step 62 (.step 31 (.split 10 0 (.split 17 0 (.step 53 (.step 3 (.step 4 (.step 5 (.close 7))))) (.step 7 (.close 3))) (.step 7 (.close 3))))) (.step 7 (.close 3))) (.step 53 (.close 7))) (.step 7 (.step 27 (.close 7)))) (.step 7 (.step 27 (.step 7 (.step 23 (.close 17)))))) (.step 9 (.step 27 (.step 7 (.step 9 (.step 7 (.step 11 (.close 3)))))))) (.step 27 (.step 23 (.step 31 (.step 11 (.step 7 (.step 25 (.step 7 (.close 17))))))))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21))))))))))) (.step 48 (.step 53 (.close 58)))) (.step 5 (.step 9 (.step 27 (.step 31 (.step 3 (.step 5 (.close 17)))))))) (.step 53 (.step 7 (.close 3)))) (.step 27 (.step 53 (.step 31 (.close 61))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325584869602947958301966098881851430767077592431662055603367250546567173780689550661577108412020837924448118050111783698432⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 24 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 46 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 46 (.split 55 1 (.step 46 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 27 (.step 7 (.close 46))))) (.step 9 (.step 27 (.step 7 (.close 46))))))) (.run (.step 7 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 16 (.step 21 (.step 16 (.close 22)))))))))))) (.run (.step 5 (.step 31 (.step 43 (.step 31 (.step 5 (.step 27 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 43 (.close 7)) (.step 5 (.step 7 (.close 9)))) (.step 5 (.step 7 (.step 9 (.step 7 (.close 44)))))) (.step 5 (.step 7 (.step 9 (.step 7 (.step 23 (.step 7 (.close 44)))))))) (.step 3 (.step 7 (.close 9)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980352459069796044415984113383272240537201631902138452791489356357224717412728832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 43 (.step 58 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 42 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 42 (.close 7)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 5 (.step 26 (.step 31 (.step 42 (.close 7))))))) (.step 5 (.step 43 (.step 7 (.step 28 (.step 5 (.close 7))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 31 (.step 42 (.step 7 (.step 9 (.close 21))))))) (.step 5 (.step 31 (.step 42 (.step 9 (.step 16 (.close 58))))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 16 (.close 22))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 27 (.step 18 (.step 9 (.step 17 (.close 21)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083263539908491211970054889756714969801218740098112058511620808618076416133735619486692051779584⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.reuse 0) (.run (.split 40 1 (.split 42 1 (.step 42 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 74 1 (.step 31 (.step 27 (.close 42))) (.step 11 (.step 27 (.step 7 (.step 31 (.close 42)))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 31 (.close 42)))) (.step 3 (.step 27 (.step 42 (.close 3))))) (.step 3 (.step 27 (.step 7 (.step 11 (.step 34 (.close 42))))))) (.step 27 (.step 42 (.step 7 (.step 3 (.close 5)))))) (.step 27 (.step 34 (.step 42 (.close 52))))) (.step 3 (.step 11 (.step 9 (.close 27))))))) (.step 5 (.step 7 (.step 27 (.close 31))))) (.step 5 (.step 27 (.step 31 (.close 42))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 22 (.step 16 (.close 21)))))))) (.step 5 (.step 31 (.close 27)))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 22 (.step 16 (.step 21 (.step 16 (.close 28)))))))))))))) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 5 (.step 31 (.close 27)))) (.step 5 (.step 7 (.step 5 (.step 16 (.step 21 (.step 28 (.step 16 (.step 21 (.close 22)))))))))) (.step 31 (.split 49 1 (.step 45 (.step 7 (.step 5 (.step 29 (.step 31 (.close 37)))))) (.step 7 (.step 16 (.step 9 (.step 17 (.step 29 (.close 31)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457950409596736444732873088207266473008078788268926404328151907573521877827584⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 3 (.step 27 (.close 31)))) (.step 3 (.close 7)))))))) (.run (.step 43 (.split 30 1 (.split 34 1 (.split 36 1 (.step 58 (.split 38 1 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 27 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 27 (.close 7)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 5 (.step 9 (.step 26 (.step 27 (.close 7))))))) (.step 5 (.step 43 (.step 7 (.step 28 (.step 3 (.close 4))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 9 (.step 27 (.step 7 (.step 21 (.step 7 (.step 22 (.step 7 (.close 26)))))))))) (.step 5 (.step 9 (.step 27 (.step 16 (.close 58)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 7 (.step 5 (.close 28))))) (.step 3 (.step 5 (.step 21 (.step 23 (.close 27)))))) (.step 5 (.step 10 (.step 28 (.step 43 (.step 58 (.step 7 (.step 28 (.step 3 (.close 4))))))))))) (.step 7 (.step 28 (.step 5 (.step 7 (.step 5 (.step 16 (.step 21 (.step 16 (.close 22)))))))))) (.step 7 (.step 16 (.step 28 (.step 5 (.step 7 (.step 5 (.step 16 (.close 21))))))))) (.step 3 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933904369533342669925601473518814959792146087936⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.step 19 (.close 17))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 31 (.step 44 (.step 48 (.step 11 (.step 17 (.step 23 (.step 25 (.step 27 (.step 7 (.close 19)))))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 7 (.step 19 (.close 7)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 18 (.step 7 (.close 17)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933904369533342669925601473518814959792146087936⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 24 1 (.reuse 0) (.run (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 43 1 (.split 51 1 (.split 55 1 (.split 67 1 (.split 38 1 (.step 31 (.close 27)) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 5 (.close 27)))) (.step 3 (.step 27 (.close 7)))) (.step 3 (.step 9 (.close 27)))) (.step 11 (.step 27 (.close 3)))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 5 (.step 7 (.step 27 (.close 7))))) (.step 5 (.close 27))) (.step 27 (.step 3 (.close 5)))) (.step 5 (.step 7 (.step 27 (.step 7 (.step 23 (.close 27))))))) (.step 5 (.step 7 (.step 29 (.close 27))))) (.step 3 (.step 7 (.step 18 (.step 27 (.step 3 (.close 7))))))) (.step 3 (.step 5 (.step 27 (.step 29 (.step 5 (.close 3))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887741921183602025394990783539550081939716890900475722878661773960895574058205184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.step 19 (.close 17))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 31 (.step 48 (.step 11 (.step 17 (.step 23 (.step 27 (.step 7 (.step 19 (.close 20))))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 7 (.step 19 (.close 7)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 18 (.step 7 (.close 17)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887741921183602025394990783538054965764727377215153353294793016431787555066740736⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 18)))))) (.step 7 (.step 11 (.step 18 (.step 17 (.close 19)))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.close 17))))))) (.step 4 (.step 31 (.step 42 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 27)))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 42 (.close 3))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 18 (.step 7 (.close 17)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973082633708833828702555007708910107123002638336⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.step 5 (.step 3 (.close 18))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 27)))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 17 (.step 20 (.step 25 (.close 27)))))))))))) (.run (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.step 5 (.step 3 (.close 18))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 27)))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 17 (.step 20 (.close 27)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980352459069796044415984113383272240538595428477046616737835338749265240006852608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 38 1 (.split 56 1 (.step 77 (.split 59 1 (.step 11 (.split 2 0 (.step 7 (.step 27 (.step 7 (.close 5)))) (.step 23 (.close 5)))) (.step 23 (.step 27 (.step 7 (.step 11 (.step 3 (.step 7 (.close 17))))))))) (.step 5 (.step 3 (.step 11 (.step 3 (.close 17)))))) (.step 5 (.step 3 (.step 11 (.step 3 (.close 17)))))) (.step 5 (.step 17 (.step 31 (.step 3 (.close 7)))))) (.step 5 (.step 31 (.step 7 (.step 11 (.step 7 (.close 17))))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 11 (.step 17 (.step 27 (.step 31 (.step 34 (.step 42 (.close 61)))))))) (.step 5 (.step 18 (.step 11 (.step 17 (.step 5 (.step 23 (.close 17)))))))) (.step 3 (.step 7 (.step 18 (.step 3 (.step 11 (.step 17 (.step 27 (.step 17 (.step 34 (.close 44))))))))))) (.step 27 (.step 31 (.step 48 (.step 55 (.step 23 (.step 55 (.step 11 (.step 17 (.step 31 (.step 17 (.step 7 (.step 34 (.close 44)))))))))))))) (.step 17 (.step 27 (.step 31 (.step 34 (.step 31 (.step 34 (.close 3)))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.close 27))))))) (.step 5 (.step 7 (.step 11 (.step 17 (.close 23)))))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 23 (.close 17)))))))) (.step 11 (.step 17 (.step 31 (.step 27 (.step 34 (.step 42 (.close 3)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408736866501353691302147645596762112⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 5 (.step 7 (.step 23 (.step 11 (.step 7 (.step 17 (.close 27))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 7 (.step 5 (.close 28))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.close 7)))))))) (.run (.step 3 (.step 5 (.step 27 (.step 29 (.step 5 (.step 3 (.step 8 (.close 9)))))))))) (.run (.step 11 (.step 17 (.step 27 (.step 7 (.step 29 (.step 27 (.close 3))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 7 (.step 18 (.step 17 (.step 3 (.close 5))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 20 (.step 7 (.step 18 (.step 17 (.step 3 (.close 5)))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 7 (.step 18 (.step 17 (.step 3 (.close 5))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134151953919531549142299967488⟩
def references : Fin 4 → Box := ![Part9.root, Part10.root, Part12.root, Part14.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.step 20 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.step 20 (.step 7 (.step 5 (.step 3 (.step 7 (.close 18)))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20)))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 20 (.step 19 (.close 27)))))))))) (.step 7 (.step 5 (.step 11 (.close 19))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 20 (.step 7 (.close 27)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.step 8 (.close 18))))))) (.step 4 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 17 (.close 19))))))))))))) (.reuse 2)) (.reuse 3)) (.run (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 3 (.step 27 (.close 31)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 27 (.step 3 (.close 7))))) (.step 3 (.step 17 (.step 3 (.step 7 (.step 11 (.close 17))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part12.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2417851639229260496896000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546456141158202403379179379791566505724447871444758525771723961202438027409883136⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 11 (.split 55 1 (.split 38 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 58 1 (.split 22 0 (.step 31 (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 5))) (.step 11 (.step 3 (.close 5)))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.step 5 (.close 3)))) (.step 3 (.step 7 (.close 11)))) (.step 9 (.step 11 (.step 3 (.step 7 (.close 27)))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 9)))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 9)))))) (.step 3 (.step 5 (.step 18 (.step 11 (.step 5 (.close 9)))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.step 27 (.close 44)))))))) (.step 9 (.step 11 (.step 27 (.step 31 (.step 9 (.step 48 (.step 53 (.close 11))))))))) (.step 9 (.step 11 (.step 27 (.step 31 (.step 9 (.step 34 (.step 48 (.step 52 (.step 7 (.step 8 (.close 11)))))))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.close 27))))))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 31 (.step 11 (.step 27 (.close 42)))))) (.step 5 (.step 7 (.step 9 (.step 11 (.step 7 (.step 9 (.close 11)))))))) (.step 5 (.step 7 (.step 9 (.step 31 (.step 7 (.step 5 (.close 28)))))))) (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134153162845351164870987350016⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 4 1 (.split 8 1 (.reuse 0) (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 9 (.step 27 (.step 29 (.step 5 (.step 3 (.step 8 (.close 9))))))))))) (.run (.step 11 (.step 27 (.step 5 (.step 7 (.step 9 (.close 11)))))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 5 (.close 7))))) (.run (.step 3 (.step 7 (.step 11 (.step 3 (.step 7 (.close 11))))))))) (.run (.step 7 (.step 18 (.step 31 (.split 8 1 (.split 14 1 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 3 (.step 27 (.close 31)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 27 (.step 3 (.close 7))))) (.step 3 (.step 27 (.step 31 (.step 3 (.close 7)))))) (.step 3 (.step 11 (.step 3 (.step 7 (.close 11))))))))))) (.run (.step 3 (.step 5 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 34 1 (.step 5 (.step 3 (.step 5 (.step 23 (.step 21 (.step 27 (.step 23 (.close 8)))))))) (.step 3 (.step 5 (.close 28)))) (.step 5 (.close 28))) (.step 5 (.close 27))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 8 (.close 18)))))) (.step 5 (.step 11 (.step 17 (.step 23 (.close 17)))))) (.step 5 (.step 8 (.step 11 (.close 9)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part17.excludes
end FiveColour.Packed.ProjectedChunks.Case10
