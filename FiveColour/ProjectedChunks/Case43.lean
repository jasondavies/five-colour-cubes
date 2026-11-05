module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case43
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763744141312⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301992407735424565354844473286458062706058471700174795441057169795130632859463205865834458500869606291874068565264236224196011724333239095633020139494220753559186806884270080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.step 7 (.split 14 0 (.step 7 (.step 31 (.step 9 (.step 5 (.close 7))))) (.step 7 (.step 31 (.step 17 (.step 3 (.close 5))))))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 5 (.step 7 (.close 5))) (.step 7 (.step 3 (.close 5)))) (.step 3 (.step 31 (.close 5)))) (.step 3 (.close 7)))) (.split 2 0 (.step 7 (.split 14 0 (.step 7 (.step 31 (.close 18))) (.step 11 (.step 7 (.step 17 (.step 31 (.step 18 (.step 7 (.close 5))))))))) (.step 11 (.step 23 (.step 5 (.close 3)))))) (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.step 11 (.close 17)))))) (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.close 3)) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 17 (.close 18))))))) (.step 7 (.close 3))) (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5))))) (.step 27 (.step 23 (.step 31 (.close 44))))) (.step 44 (.step 62 (.close 7))))) (.split 59 1 (.split 74 1 (.split 67 1 (.split 2 0 (.step 31 (.step 27 (.close 61))) (.step 61 (.close 3))) (.step 3 (.step 70 (.close 7)))) (.step 11 (.step 61 (.step 3 (.close 7))))) (.step 27 (.step 44 (.step 61 (.step 5 (.close 7))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389335143621917845746199233657002552726285493292717941911673834461699849000471300751149468785396202835943736744396702085800021476867234464906581098657480704⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 61 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.step 7 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 7)))) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.close 16))))))))))))) (.run (.step 58 (.step 18 (.step 3 (.step 18 (.step 27 (.step 44 (.close 18))))))))) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.step 7 (.step 54 (.close 3))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.step 27 (.close 34)))))) (.step 3 (.step 7 (.step 11 (.step 17 (.close 44)))))) (.step 54 (.step 3 (.close 7)))) (.step 3 (.step 54 (.step 7 (.step 27 (.step 17 (.close 44))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 54))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648365977144347058681978277116666098743607114191412539062507445890838580826210304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 58 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.step 5 (.close 17)))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.close 17)))))) (.step 7 (.close 3))) (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5))))) (.step 27 (.step 23 (.step 31 (.step 17 (.step 7 (.step 18 (.close 19)))))))) (.step 52 (.close 7))) (.step 52 (.step 4 (.step 7 (.close 5))))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 16 (.step 22 (.step 7 (.step 21 (.close 26))))))))))))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 52 (.step 54 (.step 57 (.step 52 (.close 7)))))) (.step 52 (.step 61 (.step 7 (.step 3 (.close 5)))))) (.step 52 (.split 74 1 (.split 2 0 (.split 30 0 (.step 52 (.step 9 (.step 55 (.step 5 (.close 52))))) (.step 31 (.step 7 (.close 52)))) (.step 5 (.step 9 (.step 52 (.close 3))))) (.step 27 (.step 31 (.step 34 (.step 31 (.step 44 (.step 7 (.step 19 (.close 3))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645291781454943633640007021328483065393776232844671790648365977144347058681978277116666098743607114191412539062507445890838580826210304⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 58 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.step 53 (.close 3)) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 17)))) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 27 (.step 7 (.step 31 (.step 17 (.close 18))))))) (.step 7 (.close 3))) (.split 14 0 (.step 9 (.step 31 (.step 3 (.close 5)))) (.step 3 (.step 7 (.close 5))))) (.step 27 (.step 23 (.step 31 (.step 44 (.step 7 (.close 17))))))) (.step 53 (.close 7))) (.step 53 (.step 7 (.close 5)))) (.step 5 (.step 31 (.step 48 (.step 5 (.step 7 (.step 9 (.step 7 (.step 21 (.step 7 (.step 16 (.step 7 (.close 26))))))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 53 (.step 54 (.step 57 (.step 53 (.close 7)))))) (.step 53 (.step 61 (.step 7 (.step 3 (.close 5)))))))) (.reuse 1))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325584869602947958301966098881851430767077592429851037361969406608744293842428059182853937417723327283447652078058162094080⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 67 1 (.split 74 1 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.step 7 (.step 46 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 11)))) (.step 46 (.step 70 (.close 3)))) (.step 3 (.step 11 (.step 27 (.close 7))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 46 (.split 55 1 (.step 54 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.step 7 (.close 52)))))))) (.run (.step 7 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.close 45))))) (.step 23 (.step 31 (.step 44 (.step 31 (.step 7 (.step 16 (.step 45 (.step 21 (.step 22 (.step 45 (.close 52))))))))))))))) (.run (.step 5 (.step 31 (.step 43 (.step 31 (.split 43 1 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 51 1 (.step 5 (.split 67 1 (.step 5 (.close 7)) (.step 3 (.step 7 (.close 9))))) (.step 3 (.step 7 (.step 9 (.close 44))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 7 (.close 44))))))) (.step 5 (.step 7 (.step 9 (.step 23 (.step 31 (.step 44 (.close 53)))))))) (.step 5 (.step 9 (.step 23 (.step 31 (.step 44 (.close 52)))))))) (.step 3 (.step 7 (.close 9))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793969914823290635507857846217336980350648051554646572046290503333979045722908731144155280848355891252663791124480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 43 (.step 58 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 42 (.split 59 1 (.split 67 1 (.split 74 1 (.step 43 (.split 10 0 (.split 14 0 (.split 16 0 (.step 58 (.step 7 (.step 5 (.close 7)))) (.step 5 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 7)))) (.step 5 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 31 (.step 42 (.step 7 (.step 9 (.step 7 (.close 16)))))))))) (.step 5 (.step 43 (.step 58 (.step 7 (.step 28 (.split 67 1 (.step 5 (.step 7 (.close 16))) (.step 3 (.step 7 (.close 21)))))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 31 (.step 42 (.step 21 (.step 7 (.step 9 (.step 21 (.close 26))))))))) (.step 5 (.step 31 (.step 42 (.step 16 (.step 58 (.step 9 (.close 26)))))))) (.step 3 (.step 7 (.step 9 (.close 10))))) (.step 5 (.step 7 (.step 5 (.step 21 (.step 16 (.step 22 (.step 16 (.close 41))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.close 42)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263365873409341085735697933769687675427237195480366161210624950577931933845752598744547354276021366823059456⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.split 39 1 (.reuse 0) (.run (.split 40 1 (.split 42 1 (.step 42 (.step 61 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 2 0 (.step 31 (.step 27 (.close 42))) (.step 42 (.close 3))) (.step 11 (.step 42 (.step 3 (.close 7))))) (.step 3 (.step 42 (.step 70 (.close 7))))) (.step 27 (.step 42 (.step 7 (.step 3 (.close 5)))))) (.step 3 (.step 27 (.step 42 (.step 3 (.close 5)))))) (.step 3 (.step 42 (.step 54 (.step 61 (.step 7 (.step 27 (.step 7 (.close 34))))))))) (.step 27 (.step 42 (.step 53 (.close 3))))) (.step 27 (.step 42 (.step 34 (.close 52))))) (.step 3 (.step 11 (.step 27 (.close 7))))))) (.step 5 (.step 7 (.step 31 (.close 42))))) (.step 5 (.step 27 (.step 31 (.close 42))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 22 (.step 16 (.close 21))))))) (.step 22 (.step 23 (.step 31 (.step 36 (.step 31 (.step 7 (.step 16 (.step 21 (.step 22 (.step 21 (.close 52)))))))))))) (.step 7 (.step 31 (.step 45 (.step 23 (.step 31 (.step 38 (.step 16 (.step 45 (.close 52)))))))))) (.step 5 (.step 31 (.close 36)))) (.step 31 (.step 38 (.split 49 1 (.step 45 (.step 5 (.step 7 (.step 5 (.step 22 (.step 16 (.close 21))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.close 39))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139961005535241556911628244232969148273764228259874034916851344613572608⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 5 (.step 31 (.step 16 (.step 21 (.step 22 (.step 21 (.close 37))))))))) (.step 15 (.step 16 (.step 17 (.step 31 (.step 34 (.step 31 (.step 7 (.close 16))))))))) (.step 7 (.step 31 (.step 37 (.step 23 (.step 31 (.step 37 (.step 16 (.close 52))))))))) (.step 5 (.step 31 (.close 34)))) (.step 16 (.step 31 (.step 38 (.step 45 (.step 5 (.step 7 (.step 5 (.step 37 (.close 21)))))))))) (.step 31 (.split 49 1 (.split 50 1 (.step 45 (.split 55 1 (.split 59 1 (.step 37 (.step 7 (.step 5 (.step 31 (.close 16))))) (.step 7 (.step 5 (.step 22 (.step 23 (.step 31 (.step 16 (.step 21 (.close 22))))))))) (.step 5 (.step 7 (.close 37))))) (.step 7 (.step 22 (.step 23 (.step 31 (.close 37)))))) (.step 7 (.step 16 (.step 17 (.step 31 (.step 37 (.close 52))))))))))))) (.run (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 17 (.close 19)))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 42)))))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253826615410921412087000681330581400443702631413589213184⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.split 39 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.step 17 (.step 19 (.close 17)))))) (.step 11 (.step 18 (.step 44 (.step 7 (.step 17 (.step 19 (.close 17)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 44 (.step 48 (.step 11 (.step 23 (.step 25 (.step 31 (.step 19 (.step 44 (.step 19 (.step 17 (.step 42 (.close 53)))))))))))))) (.step 4 (.step 44 (.step 48 (.step 55 (.step 27 (.step 52 (.step 7 (.step 17 (.close 19)))))))))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 19 (.step 7 (.step 17 (.step 7 (.close 20)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147119229707115137779673558956759444558487127858588698848567195501330432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.split 39 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.step 17 (.step 19 (.close 17)))))) (.step 11 (.step 18 (.step 20 (.step 7 (.step 19 (.close 44))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 48 (.step 11 (.step 23 (.step 53 (.step 7 (.step 19 (.step 17 (.close 20)))))))))) (.step 4 (.step 48 (.step 55 (.step 27 (.step 52 (.step 7 (.step 17 (.step 19 (.close 20)))))))))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 42 (.step 18 (.step 19 (.step 7 (.step 17 (.step 7 (.close 20)))))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080429297359759202320030024320934048748070134770864887738299147120914703781834693165609470212869600081860596246350105239245485506560⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 2 0 (.split 38 0 (.split 39 0 (.step 7 (.step 18 (.step 7 (.close 17)))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.step 17 (.close 19))))) (.step 11 (.step 18 (.step 42 (.step 7 (.step 17 (.step 19 (.close 17)))))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 42 (.step 7 (.step 18 (.step 19 (.step 44 (.step 17 (.step 19 (.close 53)))))))))) (.step 4 (.step 42 (.step 48 (.step 52 (.step 7 (.step 17 (.close 19)))))))) (.step 7 (.step 5 (.close 19)))) (.step 11 (.step 18 (.step 42 (.close 3))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.close 53)))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 19 (.step 42 (.step 25 (.close 52))))))))) (.step 7 (.step 5 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450099676262491840107534934633797778744445763584⟩
def references : Fin 3 → Box := ![Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 3 := (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.step 25 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 25 (.step 7 (.step 5 (.step 3 (.close 18))))) (.step 11 (.step 18 (.step 20 (.close 19))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.step 17 (.step 20 (.step 17 (.step 25 (.close 53)))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 52 (.step 19 (.close 20)))))))) (.step 7 (.step 5 (.step 19 (.close 20))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 7 (.step 17 (.step 25 (.close 42))))))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))))))) (.step 7 (.step 18 (.split 17 1 (.reuse 2) (.run (.step 19 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 19 (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 7))))) (.step 4 (.step 5 (.step 7 (.step 5 (.close 18)))))) (.step 4 (.step 7 (.step 18 (.step 19 (.close 53)))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 19 (.step 42 (.step 20 (.close 52))))))))) (.step 7 (.step 5 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 42))))) (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832323002622187486436986965130477288425151723749454505518253229163998971983985768830100596530185998776728301368497022258118656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 58 1 (.split 38 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 2 0 (.split 10 0 (.split 74 1 (.step 7 (.split 16 0 (.split 17 0 (.step 7 (.step 27 (.step 7 (.step 5 (.close 17))))) (.step 7 (.close 17))) (.step 7 (.step 17 (.close 3))))) (.step 11 (.step 17 (.close 3)))) (.step 7 (.step 11 (.close 17)))) (.step 11 (.step 17 (.step 23 (.step 5 (.close 3)))))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 27 (.step 44 (.step 23 (.step 55 (.step 23 (.close 17))))))) (.step 3 (.step 5 (.step 3 (.close 17))))) (.step 3 (.step 5 (.step 3 (.close 17))))) (.step 11 (.step 17 (.step 42 (.step 61 (.step 3 (.close 7))))))) (.step 5 (.step 18 (.step 31 (.step 34 (.step 48 (.step 5 (.step 17 (.step 5 (.close 21)))))))))) (.step 3 (.step 7 (.step 27 (.step 18 (.step 3 (.step 34 (.step 44 (.step 17 (.close 54)))))))))) (.step 31 (.step 27 (.step 48 (.step 61 (.split 51 1 (.split 59 1 (.split 67 1 (.step 23 (.step 55 (.step 23 (.close 17)))) (.step 3 (.step 7 (.step 17 (.step 34 (.close 44)))))) (.step 44 (.step 23 (.step 31 (.close 17))))) (.step 3 (.step 7 (.step 52 (.step 44 (.step 17 (.close 53)))))))))))) (.step 17 (.step 31 (.step 27 (.step 34 (.step 48 (.step 52 (.step 23 (.step 31 (.step 17 (.close 3))))))))))) (.step 3 (.step 7 (.step 8 (.step 3 (.step 11 (.close 27))))))) (.step 5 (.step 7 (.step 17 (.close 23))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763743092736⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 40 1 (.reuse 1) (.run (.step 5 (.step 7 (.step 17 (.step 23 (.step 7 (.close 17)))))))) (.run (.step 11 (.step 17 (.step 31 (.step 34 (.step 42 (.step 3 (.step 5 (.close 7)))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 7 (.step 5 (.close 37))))))))) (.run (.step 5 (.step 7 (.step 23 (.step 31 (.step 7 (.step 5 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.close 7)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.split 38 1 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17)))))) (.step 3 (.step 5 (.close 17)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 25 (.step 74 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17)))))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 67 (.step 17 (.step 7 (.step 5 (.step 3 (.step 7 (.close 17))))))))))))))) (.run (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 38 1 (.split 39 1 (.split 49 1 (.step 31 (.step 7 (.step 17 (.close 19)))) (.step 7 (.step 31 (.step 7 (.step 3 (.step 27 (.step 31 (.close 52)))))))) (.step 3 (.step 31 (.close 42)))) (.step 3 (.close 7))) (.step 3 (.step 17 (.step 3 (.step 7 (.close 17)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041331859301996185383359567389338420209196257411645294556832325587393793972263368113154083265576944467546454330139962690531908253828113450101070059066749539131880844419220763744141312⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 5 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.step 5 (.step 3 (.step 5 (.step 42 (.step 23 (.step 61 (.step 3 (.step 17 (.step 21 (.step 17 (.close 23))))))))))) (.step 3 (.step 5 (.close 39)))) (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.close 18))))) (.step 3 (.step 4 (.step 5 (.step 18 (.close 19)))))) (.step 5 (.step 17 (.step 23 (.close 17)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part14.excludes
end FiveColour.Packed.ProjectedChunks.Case43
