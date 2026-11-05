module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case218
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941794206991798234622625843120460821168128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 36 0 (.step 29 (.split 38 0 (.step 55 (.step 53 (.close 13))) (.step 38 (.step 3 (.close 5))))) (.step 57 (.step 3 (.step 9 (.close 13))))) (.split 42 0 (.split 35 0 (.split 63 0 (.step 38 (.step 5 (.step 9 (.close 19)))) (.step 27 (.step 38 (.step 5 (.step 13 (.step 19 (.close 42))))))) (.step 29 (.close 38))) (.step 38 (.step 5 (.step 9 (.step 20 (.step 13 (.step 19 (.close 39))))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 9 (.step 15 (.step 3 (.step 5 (.close 19)))))) (.step 15 (.step 43 (.step 3 (.close 9))))) (.step 43 (.step 15 (.step 9 (.step 3 (.step 18 (.step 22 (.step 3 (.close 33))))))))) (.step 29 (.step 38 (.step 15 (.step 43 (.step 3 (.close 33)))))))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 3 (.step 9 (.close 13))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.step 9 (.step 3 (.step 13 (.close 33))))))) (.step 38 (.step 43 (.step 15 (.step 9 (.step 18 (.close 33)))))))) (.split 34 0 (.split 30 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 75 (.step 5 (.step 9 (.step 19 (.close 13)))))) (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 42 (.close 3)))) (.step 75 (.split 35 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 38 (.step 43 (.close 3))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568638795232371503324099655248135745175552⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.split 36 0 (.step 42 (.step 4 (.step 9 (.step 19 (.step 13 (.close 20)))))) (.step 38 (.step 24 (.step 3 (.close 4)))))) (.step 43 (.step 3 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 13 (.step 19 (.close 20)))))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 33 (.step 37 (.step 33 (.step 20 (.close 4)))))) (.step 4 (.step 33 (.step 13 (.step 15 (.close 17)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.close 20)))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 43 (.step 3 (.close 15)))))) (.step 24 (.step 33 (.split 34 0 (.step 61 (.step 33 (.close 20))) (.step 17 (.step 24 (.step 3 (.close 20)))))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205969698150575188156815938267791677718528⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.close 3)))) (.split 39 0 (.step 38 (.step 11 (.close 13))) (.step 24 (.close 42)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.step 19 (.close 3))))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15))))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.close 20))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15)))))))) (.step 24 (.step 19 (.step 20 (.step 19 (.step 9 (.close 13))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188232872090892652054982859859442199449380914439651328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 52 (.step 27 (.step 5 (.step 19 (.step 20 (.close 38)))))) (.step 42 (.step 9 (.step 15 (.step 5 (.step 17 (.close 19))))))) (.split 35 0 (.split 43 0 (.step 57 (.step 58 (.step 15 (.step 17 (.step 19 (.close 20)))))) (.step 15 (.step 9 (.step 5 (.step 9 (.close 11)))))) (.step 38 (.step 15 (.step 29 (.step 5 (.step 20 (.close 17)))))))) (.split 35 0 (.split 36 0 (.step 52 (.close 5)) (.step 43 (.step 5 (.step 15 (.step 17 (.close 9)))))) (.step 38 (.step 29 (.step 37 (.step 15 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 5 (.step 15 (.close 24))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 15 (.step 17 (.close 9))))) (.step 37 (.step 5 (.step 9 (.close 11))))) (.step 3 (.step 38 (.close 9)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616455962435370140535449670082047288658339299328⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 20 (.step 11 (.step 17 (.step 19 (.close 24)))))))) (.step 3 (.step 19 (.step 24 (.close 13))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))))) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 67 (.step 13 (.step 20 (.close 3))))) (.step 3 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))) (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 74 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.step 11 (.step 17 (.step 3 (.close 19)))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568640124460367288239972559055196025520128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.split 38 0 (.split 42 0 (.step 55 (.step 17 (.step 15 (.close 38)))) (.step 15 (.step 43 (.step 17 (.close 3))))) (.step 15 (.step 38 (.step 5 (.close 3))))) (.step 38 (.step 53 (.step 3 (.step 13 (.close 15))))))) (.step 62 (.step 43 (.step 9 (.step 15 (.step 4 (.step 17 (.close 24)))))))) (.step 57 (.step 9 (.step 15 (.step 13 (.step 3 (.step 19 (.close 20)))))))) (.split 22 0 (.split 30 0 (.step 29 (.step 38 (.step 15 (.step 53 (.step 20 (.step 3 (.close 5))))))) (.step 38 (.close 9))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19))))))))) (.split 35 0 (.split 22 0 (.step 15 (.step 43 (.step 9 (.close 15)))) (.step 43 (.step 3 (.close 15)))) (.step 15 (.step 29 (.step 15 (.step 5 (.step 19 (.close 20)))))))) (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 43 (.step 17 (.step 24 (.close 15))))) (.step 18 (.step 9 (.step 15 (.step 17 (.step 20 (.close 19))))))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19)))))))) (.step 15 (.step 18 (.step 9 (.step 24 (.close 13)))))) (.step 24 (.step 4 (.step 17 (.step 15 (.step 9 (.step 20 (.close 19)))))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602286734919418671234115374552186880⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 17 0 (.split 35 0 (.step 9 (.step 17 (.step 4 (.close 24)))) (.step 38 (.close 9))) (.step 17 (.step 18 (.close 24)))) (.step 24 (.step 9 (.step 4 (.step 17 (.step 24 (.step 15 (.close 38)))))))) (.step 18 (.step 4 (.step 9 (.step 3 (.step 4 (.close 15))))))) (.step 38 (.step 24 (.step 9 (.step 5 (.step 15 (.step 13 (.close 19)))))))) (.step 38 (.step 43 (.step 15 (.close 3))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33)))))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 34 0 (.split 35 0 (.split 42 0 (.step 52 (.step 5 (.step 9 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 5)))) (.step 15 (.step 5 (.close 13)))) (.step 15 (.step 29 (.step 5 (.step 13 (.close 17))))))) (.step 24 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))))) (.step 24 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))))) (.split 17 0 (.step 24 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15))))))) (.step 13 (.close 17))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188232872089498855480075963563696445286741888548732928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 43 (.step 3 (.close 9)))) (.step 43 (.step 11 (.step 19 (.step 20 (.step 19 (.close 38))))))) (.split 36 0 (.split 39 0 (.step 29 (.step 52 (.step 3 (.close 19)))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 29 (.step 3 (.step 24 (.close 13))))))) (.step 15 (.split 35 0 (.step 43 (.close 15)) (.step 15 (.step 3 (.close 17)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 3 (.close 9)))) (.step 42 (.step 3 (.step 13 (.step 9 (.close 20)))))) (.split 39 0 (.split 38 0 (.step 43 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 13 (.step 18 (.close 33)))) (.step 33 (.step 13 (.close 19))))) (.split 36 0 (.split 38 0 (.step 42 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 3 (.step 9 (.step 13 (.close 18))))) (.step 33 (.step 13 (.close 19))))) (.step 15 (.step 33 (.split 35 0 (.step 33 (.step 13 (.step 15 (.step 3 (.step 11 (.close 15)))))) (.step 15 (.step 3 (.step 13 (.close 17))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568638795233639153924327884649632448380928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.step 19 (.step 13 (.step 3 (.close 20)))))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 13)))))) (.split 39 0 (.step 43 (.close 3)) (.step 3 (.step 19 (.close 24))))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.close 4))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 24 (.step 3 (.close 20)))))) (.step 13 (.step 17 (.close 14)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205969698151842838757044167669288380923904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.close 19))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 19 (.close 13))))))) (.split 39 0 (.step 38 (.step 9 (.close 13))) (.step 3 (.step 19 (.close 24))))) (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 24 (.close 4)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.step 19 (.close 9))))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14)))))) (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 42 (.step 11 (.step 3 (.close 19)))))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14))))) (.step 19 (.step 20 (.step 13 (.step 15 (.step 4 (.step 9 (.close 19))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599766273060006785103026559709810975047680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.split 43 0 (.step 66 (.step 15 (.close 3))) (.step 15 (.close 11))) (.step 15 (.step 3 (.close 13)))) (.step 15 (.step 3 (.step 13 (.close 17))))) (.split 34 0 (.split 35 0 (.split 49 0 (.step 13 (.step 3 (.step 9 (.close 15)))) (.step 15 (.step 11 (.step 13 (.close 17))))) (.step 3 (.step 15 (.close 13)))) (.step 13 (.step 15 (.step 3 (.close 13))))))) (.step 24 (.split 30 0 (.step 17 (.step 66 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))))) (.split 22 0 (.step 24 (.split 30 0 (.step 17 (.step 61 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17))))) (.step 13 (.step 15 (.close 17))))) (.split 17 0 (.split 22 0 (.step 24 (.split 30 0 (.step 17 (.step 42 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17)))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def references : Fin 4 → Box := ![Part7.root, Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 4 := (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 75 (.step 42 (.step 43 (.close 3))))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 15 (.split 36 0 (.step 52 (.step 9 (.step 3 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 13))))) (.step 24 (.step 4 (.step 9 (.close 13))))) (.step 15 (.step 18 (.step 15 (.step 13 (.close 17)))))) (.step 15 (.close 5))) (.step 24 (.step 39 (.step 4 (.close 13))))) (.split 17 0 (.step 24 (.step 38 (.step 4 (.step 9 (.close 13))))) (.step 13 (.step 4 (.close 17))))) (.split 16 0 (.step 15 (.step 3 (.step 11 (.close 13)))) (.step 3 (.step 13 (.close 15)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def references : Fin 4 → Box := ![Part2.root, Part4.root, Part6.root, Part11.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.close 38))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.step 42 (.step 3 (.close 13))))) (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20))))))))) (.split 22 0 (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20)))))))) (.step 19 (.step 20 (.step 11 (.step 13 (.step 5 (.step 17 (.close 19)))))))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part4.excludes
  · exact Part6.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case218
