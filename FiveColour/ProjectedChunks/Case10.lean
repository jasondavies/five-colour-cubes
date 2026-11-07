module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567385983191639432196471305727407451091194415651837569843567242944100769407992952915817967241608698414801901167041341559296257577303674888822885944740027564032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.step 7 (.step 27 (.split 8 0 (.step 7 (.step 31 (.close 9))) (.step 7 (.step 11 (.close 5)))))) (.split 8 0 (.split 4 0 (.split 10 0 (.split 30 0 (.step 27 (.step 3 (.close 5))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 4 (.close 7))) (.split 14 0 (.step 3 (.close 58)) (.step 8 (.step 5 (.close 3)))))) (.split 2 0 (.split 8 0 (.step 7 (.step 27 (.close 31))) (.step 11 (.close 3))) (.step 23 (.step 5 (.close 3))))) (.step 7 (.step 3 (.close 70)))) (.split 67 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 4 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 62 (.close 43)) (.step 7 (.close 3))) (.step 7 (.close 55))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.step 9 (.close 11)))) (.step 27 (.step 7 (.close 5)))) (.step 23 (.step 27 (.step 11 (.close 62))))) (.step 62 (.close 7)))) (.split 59 1 (.split 67 1 (.split 74 1 (.step 31 (.close 61)) (.step 27 (.step 31 (.close 61)))) (.step 3 (.step 7 (.close 61)))) (.step 27 (.step 31 (.close 61))))) (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 58 (.close 54)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 26 (.step 48 (.close 58)))))) (.step 58 (.step 27 (.close 48)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338417012525741888069246846699380325437709934763984976463317753067945134267707236722593453332466562980825892572308369042024991634421350765606480806674432⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 24 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 77)))) (.step 54 (.close 7))) (.step 3 (.step 27 (.close 61)))) (.step 3 (.step 7 (.close 26)))) (.step 3 (.step 7 (.close 54)))))) (.run (.split 58 1 (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 16 0 (.split 67 1 (.split 4 0 (.step 62 (.step 31 (.split 10 0 (.split 17 0 (.step 53 (.close 43)) (.step 7 (.close 3))) (.step 7 (.close 3))))) (.step 7 (.close 3))) (.step 53 (.close 7))) (.step 7 (.close 53))) (.step 27 (.step 7 (.step 9 (.close 53))))) (.step 27 (.step 31 (.close 53)))) (.step 48 (.step 5 (.close 58)))) (.step 48 (.step 53 (.close 58)))) (.step 5 (.step 9 (.step 27 (.step 31 (.step 3 (.close 58))))))) (.step 53 (.step 7 (.close 3)))) (.step 27 (.step 53 (.step 31 (.close 61)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832323002619724861049712310179709848418892747886638832832090536591190026526158672709466947463058740700093012214878139036205056⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 58 1 (.split 51 1 (.split 2 0 (.split 55 1 (.split 56 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 67 1 (.split 4 0 (.step 52 (.step 31 (.split 17 0 (.step 52 (.close 43)) (.step 7 (.close 3))))) (.step 7 (.close 3))) (.step 52 (.close 7))) (.step 7 (.step 27 (.close 7)))) (.step 27 (.step 7 (.close 55)))) (.step 27 (.step 7 (.step 9 (.close 52))))) (.step 27 (.step 31 (.close 52)))) (.step 48 (.step 5 (.close 58)))) (.step 48 (.step 52 (.close 58)))) (.step 5 (.step 9 (.step 27 (.step 31 (.step 3 (.close 58))))))) (.step 52 (.close 54))) (.step 27 (.step 52 (.step 31 (.close 61))))) (.step 52 (.step 7 (.close 5)))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 24 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 7 (.close 11))) (.step 46 (.close 7))) (.step 3 (.close 27))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.split 55 1 (.step 46 (.close 54)) (.step 3 (.close 46)))) (.step 27 (.step 7 (.close 46)))) (.step 9 (.step 27 (.close 46)))))) (.run (.step 31 (.step 7 (.step 29 (.step 31 (.close 45)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980352459069796044415984113383272240537201631902138452791489356357224717412728832⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 39 1 (.split 40 1 (.reuse 0) (.run (.step 43 (.step 31 (.step 27 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 43 (.close 7)) (.step 5 (.close 62))) (.step 5 (.step 9 (.close 53)))) (.step 5 (.step 9 (.close 52)))) (.step 7 (.close 9))))))))) (.run (.split 42 1 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 74 1 (.step 31 (.close 42)) (.step 27 (.step 31 (.close 42)))) (.step 3 (.step 7 (.close 42)))) (.step 27 (.step 31 (.close 42)))) (.step 27 (.step 42 (.close 3)))) (.step 3 (.step 27 (.step 7 (.close 42))))) (.step 27 (.step 42 (.close 53)))) (.step 42 (.close 52))) (.step 3 (.step 11 (.step 9 (.close 27)))))) (.step 5 (.step 7 (.close 44)))))) (.run (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 42 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 42 (.close 7)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 26 (.step 42 (.close 7))))) (.step 5 (.step 43 (.step 7 (.step 28 (.step 5 (.close 7))))))) (.step 3 (.step 7 (.close 54)))) (.step 42 (.close 58))) (.step 42 (.step 9 (.close 58)))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 5 (.close 41)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457950409596736444732873088207266473008078788268926404328151907573521877827584⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 31 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.close 58)))))) (.step 31 (.close 27))) (.step 7 (.step 5 (.close 58))))))) (.run (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.step 5 (.step 29 (.step 31 (.close 37)))))) (.step 31 (.close 27))) (.step 7 (.step 5 (.close 58)))) (.step 31 (.split 49 1 (.step 45 (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 31))))))))) (.run (.step 7 (.step 18 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.close 31))) (.step 3 (.close 42))) (.step 3 (.close 7))))))) (.run (.split 30 1 (.split 34 1 (.split 36 1 (.step 58 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 27 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 4 0 (.split 8 0 (.split 10 0 (.step 5 (.step 7 (.step 27 (.close 7)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 7 (.close 5)))) (.step 5 (.close 3))) (.step 3 (.close 7))) (.step 26 (.step 27 (.close 7))))) (.step 5 (.step 43 (.step 28 (.close 4))))) (.step 3 (.step 7 (.close 28)))) (.step 27 (.close 58))) (.step 5 (.step 9 (.step 27 (.close 58))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 29))) (.step 28 (.step 43 (.step 58 (.step 28 (.close 4))))))) (.step 28 (.step 7 (.close 29)))) (.step 28 (.step 7 (.close 29)))) (.step 3 (.close 7)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933904369533342669925601473518814959792146087936⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 24 1 (.reuse 0) (.run (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 43 1 (.split 51 1 (.split 55 1 (.split 67 1 (.split 38 1 (.step 31 (.close 27)) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 11)))) (.step 5 (.close 27))) (.step 3 (.step 27 (.close 7)))) (.step 3 (.close 46))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 27 (.close 3))) (.step 5 (.step 7 (.close 44)))) (.step 5 (.close 27))) (.step 27 (.close 5))) (.step 5 (.step 27 (.close 31)))) (.step 29 (.close 27))) (.step 7 (.step 18 (.step 27 (.close 7))))) (.step 27 (.step 29 (.step 5 (.close 3))))))) (.run (.step 7 (.step 18 (.split 24 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.close 62)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.step 18 (.close 62))))) (.step 31 (.step 44 (.step 48 (.step 11 (.step 17 (.step 27 (.step 7 (.close 19))))))))) (.step 7 (.step 5 (.close 25)))) (.step 11 (.step 42 (.step 18 (.step 19 (.close 7)))))) (.step 11 (.step 27 (.step 18 (.step 7 (.close 17))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973082633708833828702555007708910107123002638336⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 24 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.step 19 (.close 17))))) (.step 42 (.step 7 (.step 11 (.step 17 (.step 19 (.close 27))))))) (.step 7 (.step 5 (.close 19)))) (.step 42 (.close 3))) (.step 11 (.step 27 (.step 18 (.step 7 (.close 17)))))) (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 7 (.step 5 (.close 19)))) (.step 18 (.close 42))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 5)))) (.step 11 (.step 18 (.step 19 (.close 27)))))) (.step 19 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 7 (.close 20))) (.step 18 (.close 42))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 5)))) (.step 11 (.step 18 (.step 19 (.close 27))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899586491933905763329917578089547819501207000314740211712⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 38 1 (.split 56 1 (.step 77 (.split 59 1 (.step 11 (.split 2 0 (.step 7 (.step 27 (.close 17))) (.step 23 (.close 5)))) (.step 23 (.step 27 (.step 7 (.close 17)))))) (.step 5 (.close 17))) (.step 5 (.close 17))) (.step 5 (.step 17 (.step 31 (.close 7))))) (.step 5 (.step 31 (.step 7 (.step 11 (.step 7 (.close 17))))))) (.step 3 (.step 7 (.close 77)))) (.step 17 (.step 27 (.step 31 (.close 61))))) (.step 5 (.step 18 (.step 11 (.step 17 (.step 5 (.step 23 (.close 17)))))))) (.step 7 (.step 18 (.step 3 (.step 27 (.close 77)))))) (.step 27 (.step 48 (.step 55 (.step 23 (.step 55 (.step 11 (.step 17 (.close 53))))))))) (.step 27 (.step 31 (.step 34 (.step 31 (.step 34 (.close 3))))))) (.step 7 (.close 27))) (.step 5 (.step 7 (.close 31)))) (.step 5 (.step 7 (.step 23 (.close 17))))) (.step 11 (.step 17 (.step 31 (.step 42 (.close 3)))))) (.step 5 (.step 23 (.step 11 (.step 7 (.close 31)))))) (.step 31 (.step 7 (.close 37)))) (.step 31 (.close 7))) (.step 27 (.step 29 (.step 5 (.close 17))))) (.step 11 (.step 27 (.step 29 (.step 27 (.close 3)))))) (.step 11 (.step 17 (.step 18 (.step 7 (.step 18 (.step 17 (.close 5)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408736866501353691302147645596762112⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 24 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 8 0 (.split 24 0 (.step 7 (.step 18 (.close 19))) (.step 18 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.step 18 (.close 62))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.step 18 (.step 19 (.close 44)))))) (.step 31 (.step 48 (.step 11 (.step 27 (.step 7 (.close 52))))))) (.step 7 (.step 5 (.close 20)))) (.step 11 (.step 42 (.step 18 (.step 19 (.close 7)))))) (.step 11 (.step 27 (.step 18 (.step 7 (.close 17)))))) (.step 20 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 20 (.step 7 (.step 5 (.close 61)))) (.step 18 (.step 19 (.close 20)))) (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 61))))))) (.step 18 (.step 19 (.step 20 (.close 27))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.close 5)))) (.step 18 (.step 27 (.close 20)))))))))) (.reuse 1)) (.split 16 1 (.split 17 1 (.reuse 2) (.run (.step 11 (.step 17 (.step 18 (.step 20 (.step 7 (.step 18 (.step 17 (.close 5)))))))))) (.run (.step 11 (.step 17 (.step 18 (.step 19 (.step 7 (.step 18 (.step 17 (.close 5)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2417851639229260496896000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134153162845351163771474673664⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 1 (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 11 (.split 55 1 (.split 38 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 58 1 (.split 22 0 (.step 31 (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 5))) (.step 11 (.close 5))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.step 5 (.close 3)))) (.step 3 (.step 7 (.close 11)))) (.step 9 (.step 11 (.close 44)))) (.step 5 (.close 11))) (.step 5 (.close 11))) (.step 5 (.step 18 (.step 11 (.close 58)))))) (.step 7 (.step 8 (.step 3 (.step 11 (.close 44)))))) (.step 11 (.step 27 (.step 31 (.step 9 (.step 48 (.step 53 (.close 11)))))))) (.step 11 (.step 27 (.step 31 (.step 9 (.step 48 (.step 52 (.close 11)))))))) (.step 7 (.close 27))) (.step 5 (.step 7 (.close 11)))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 11 (.close 42))) (.step 5 (.step 11 (.step 7 (.close 31))))) (.step 31 (.step 7 (.close 37)))) (.step 11 (.step 7 (.close 11)))) (.step 27 (.step 29 (.step 5 (.close 11))))) (.step 11 (.step 27 (.step 5 (.close 11))))) (.step 11 (.step 5 (.close 7)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546457952176445486219783899587989973084027505408738134153162845351164870987350016⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 4 1 (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 14 1 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.close 31))) (.step 3 (.step 27 (.close 31)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 27 (.close 7)))) (.step 17 (.step 7 (.close 17)))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.split 24 1 (.split 25 1 (.split 38 1 (.split 39 1 (.step 31 (.step 7 (.close 31))) (.step 3 (.step 27 (.close 31)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 27 (.close 31))))))) (.run (.step 3 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 34 1 (.step 5 (.step 3 (.step 5 (.step 23 (.step 21 (.step 27 (.step 23 (.close 8)))))))) (.step 3 (.step 5 (.close 28)))) (.step 5 (.close 28))) (.step 5 (.close 27))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 5 (.step 23 (.close 17)))) (.step 5 (.step 11 (.close 9)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case10
