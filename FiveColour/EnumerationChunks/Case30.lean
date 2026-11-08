module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case30
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850961488486346982229721996655181814111587466768969714487229578434461641052063066397769536416510414055014400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 0 (.split 39 0 (.split 42 0 (.split 35 0 (.split 63 0 (.step 9 (.step 3 (.step 5 (.close 53)))) (.step 52 (.step 9 (.step 3 (.step 5 (.close 53)))))) (.step 29 (.step 53 (.step 3 (.step 5 (.close 52)))))) (.step 62 (.step 9 (.step 3 (.step 5 (.close 13)))))) (.split 42 0 (.split 35 0 (.split 63 0 (.split 64 0 (.step 57 (.close 3)) (.step 27 (.step 38 (.step 3 (.step 5 (.close 42)))))) (.step 27 (.step 52 (.step 38 (.step 3 (.step 5 (.close 42))))))) (.step 38 (.step 9 (.step 23 (.step 38 (.close 42)))))) (.step 38 (.step 5 (.step 9 (.step 24 (.step 19 (.close 42)))))))) (.split 35 0 (.split 39 0 (.step 57 (.split 43 0 (.step 48 (.step 20 (.step 13 (.step 20 (.close 43))))) (.step 9 (.step 3 (.close 5))))) (.step 38 (.step 43 (.step 9 (.step 24 (.step 19 (.close 42))))))) (.step 38 (.step 29 (.step 53 (.step 39 (.step 3 (.close 13)))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188232872089498855480074695913096217057340391845527552⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 30 0 (.split 34 0 (.reuse 0) (.run (.split 36 0 (.split 38 0 (.split 39 0 (.split 42 0 (.step 29 (.step 52 (.step 15 (.step 24 (.step 3 (.close 5)))))) (.step 15 (.step 43 (.step 9 (.step 37 (.step 3 (.close 33))))))) (.step 38 (.step 43 (.step 9 (.step 17 (.step 15 (.close 19))))))) (.step 38 (.step 43 (.step 3 (.step 9 (.step 3 (.close 15))))))) (.split 38 0 (.step 57 (.split 35 0 (.split 39 0 (.step 15 (.step 43 (.step 9 (.step 3 (.close 33))))) (.step 38 (.close 43))) (.step 38 (.step 29 (.step 43 (.step 15 (.step 3 (.close 33)))))))) (.step 38 (.step 57 (.step 43 (.step 3 (.step 9 (.step 3 (.close 15))))))))))) (.run (.split 34 0 (.split 36 0 (.split 35 0 (.split 39 0 (.step 53 (.step 43 (.step 3 (.close 9)))) (.step 42 (.step 38 (.close 11)))) (.split 39 0 (.split 50 0 (.step 29 (.step 38 (.close 13))) (.step 42 (.step 29 (.step 33 (.step 13 (.step 21 (.close 38))))))) (.step 38 (.close 11)))) (.split 39 0 (.split 35 0 (.split 38 0 (.step 43 (.step 29 (.step 18 (.step 33 (.close 13))))) (.step 18 (.step 38 (.close 5)))) (.step 38 (.close 9))) (.step 38 (.close 11)))) (.split 36 0 (.split 39 0 (.split 35 0 (.split 38 0 (.step 43 (.step 29 (.step 15 (.step 18 (.close 33))))) (.step 18 (.step 38 (.close 5)))) (.step 38 (.close 9))) (.step 38 (.close 11))) (.step 38 (.step 57 (.step 43 (.step 15 (.step 33 (.step 3 (.close 9)))))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941794206991798234622625843120460821168128⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 36 0 (.step 62 (.step 3 (.step 9 (.close 13)))) (.step 43 (.step 3 (.step 11 (.step 24 (.close 13)))))) (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38)))))) (.step 24 (.step 38 (.step 3 (.close 24)))))) (.step 75 (.split 36 0 (.step 42 (.step 9 (.step 4 (.step 19 (.step 13 (.close 20)))))) (.step 43 (.close 3))))) (.step 75 (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 43 (.close 3))) (.step 43 (.step 3 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 3 (.step 20 (.step 13 (.close 24)))))))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.close 24))) (.step 5 (.step 24 (.close 19)))) (.step 4 (.step 5 (.close 33))))) (.split 39 0 (.step 75 (.step 42 (.close 3))) (.step 3 (.step 24 (.step 19 (.close 20)))))) (.split 35 0 (.split 39 0 (.step 45 (.step 75 (.step 43 (.step 5 (.step 17 (.close 24)))))) (.step 5 (.step 17 (.step 24 (.step 19 (.close 20)))))) (.step 33 (.step 4 (.step 24 (.step 25 (.close 33))))))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110189729449766125700068315269181797690869468066769534976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 68 (.close 52)) (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38))))))) (.split 38 0 (.step 43 (.step 11 (.step 19 (.step 13 (.close 20))))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4))))))) (.split 36 0 (.split 38 0 (.step 42 (.step 43 (.step 9 (.step 24 (.close 38))))) (.step 5 (.close 42))) (.step 43 (.step 38 (.step 3 (.step 13 (.close 19))))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 43 (.step 11 (.close 17))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.step 43 (.step 3 (.close 15)))) (.step 43 (.step 29 (.step 38 (.step 39 (.step 3 (.step 13 (.step 15 (.close 17)))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 42 (.step 53 (.step 3 (.step 11 (.step 13 (.close 20)))))) (.step 43 (.step 11 (.close 19)))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.close 24))) (.step 5 (.step 24 (.close 19)))) (.step 4 (.step 5 (.close 33))))) (.split 39 0 (.split 54 0 (.step 42 (.step 4 (.step 11 (.step 19 (.close 20))))) (.step 4 (.step 24 (.step 29 (.step 33 (.step 13 (.close 38))))))) (.step 3 (.step 24 (.step 19 (.close 20)))))) (.split 35 0 (.split 39 0 (.split 43 0 (.step 43 (.step 3 (.close 15))) (.step 33 (.step 24 (.step 9 (.step 4 (.close 37)))))) (.step 5 (.step 17 (.step 24 (.step 19 (.close 20)))))) (.step 33 (.step 4 (.step 24 (.step 25 (.close 33)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568638795232371503324099655248135745175552⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.reuse 0) (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 61 (.step 24 (.step 11 (.close 13))))) (.step 24 (.step 74 (.step 3 (.step 13 (.close 19)))))) (.split 36 0 (.split 38 0 (.step 61 (.step 24 (.step 4 (.step 24 (.step 9 (.step 19 (.close 38))))))) (.step 4 (.close 3))) (.step 4 (.step 24 (.step 19 (.close 20)))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 43 (.step 24 (.step 5 (.step 11 (.step 15 (.close 20))))))) (.step 24 (.step 4 (.step 17 (.step 24 (.step 19 (.close 20)))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 33 (.step 20 (.step 24 (.step 11 (.close 13)))))) (.step 20 (.step 4 (.step 9 (.close 19))))) (.step 19 (.step 24 (.step 3 (.close 20))))) (.step 24 (.step 33 (.close 20)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1684996666696914988628190080269629835306006359125068799725981925376, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103221500279579125109910001919455342126140116753711104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 42 (.step 24 (.step 11 (.close 13))))) (.step 24 (.step 38 (.step 24 (.step 3 (.close 19)))))) (.split 36 0 (.split 38 0 (.split 39 0 (.step 24 (.step 4 (.step 24 (.step 9 (.step 19 (.close 38)))))) (.step 11 (.step 18 (.step 19 (.close 24))))) (.step 4 (.close 3))) (.step 4 (.step 24 (.close 19))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 43 (.step 24 (.step 5 (.step 11 (.step 15 (.close 19))))))) (.step 24 (.step 4 (.step 17 (.step 19 (.step 15 (.step 19 (.close 20))))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 3)) (.step 20 (.step 24 (.step 3 (.close 19))))) (.step 19 (.step 24 (.close 3)))) (.step 24 (.step 33 (.step 25 (.step 3 (.close 9)))))))))
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
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077956205969698150575188156815938267791677718528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 42 (.step 20 (.step 4 (.close 9))))) (.step 24 (.step 38 (.step 24 (.step 3 (.close 19)))))) (.split 36 0 (.split 38 0 (.step 61 (.step 24 (.step 4 (.step 24 (.step 9 (.step 19 (.close 38))))))) (.step 4 (.close 3))) (.step 4 (.step 24 (.close 19))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 43 (.step 24 (.step 5 (.step 11 (.step 15 (.close 19))))))) (.step 24 (.step 4 (.step 17 (.step 19 (.step 15 (.step 19 (.close 20))))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 3)) (.step 20 (.step 4 (.step 9 (.close 19))))) (.step 19 (.step 24 (.close 3)))) (.step 24 (.step 33 (.close 20)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 61 (.step 24 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 19 (.step 3 (.step 4 (.close 9))))) (.step 20 (.step 23 (.step 20 (.step 9 (.step 13 (.close 19))))))) (.step 24 (.step 19 (.close 3)))) (.split 35 0 (.split 36 0 (.step 24 (.step 19 (.step 20 (.close 11)))) (.step 20 (.step 17 (.step 20 (.step 4 (.step 15 (.close 19))))))) (.step 17 (.step 24 (.step 4 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089160033932554097462382555865588414466949136764478424956401418842410505060899686044208256253952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 55 (.step 9 (.step 20 (.step 24 (.close 53)))))) (.step 42 (.step 27 (.step 52 (.step 5 (.step 19 (.step 20 (.close 38)))))))) (.split 38 0 (.split 39 0 (.step 15 (.step 52 (.step 43 (.close 9)))) (.split 51 0 (.step 38 (.step 67 (.step 5 (.step 9 (.step 15 (.step 17 (.close 20))))))) (.step 5 (.step 15 (.step 24 (.step 11 (.step 17 (.close 19)))))))) (.step 5 (.step 42 (.step 5 (.close 3)))))) (.split 36 0 (.split 38 0 (.step 42 (.step 15 (.step 9 (.step 38 (.step 5 (.step 17 (.close 20))))))) (.step 5 (.close 42))) (.split 38 0 (.step 57 (.step 42 (.step 15 (.step 43 (.close 9))))) (.step 3 (.step 5 (.close 15)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 52 (.close 5)) (.step 5 (.step 42 (.step 5 (.close 3))))) (.split 38 0 (.step 57 (.step 43 (.step 11 (.step 15 (.close 17))))) (.step 5 (.step 15 (.step 5 (.step 3 (.close 33))))))) (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 3 (.close 5))) (.step 3 (.step 5 (.close 15)))) (.step 5 (.step 17 (.step 9 (.step 19 (.close 24)))))) (.step 29 (.step 38 (.step 37 (.close 17))))))))
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
def root : Box := ⟨1684996666696914987166689836735301825266267872391177820592643506176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038779335590781899962180968608235160983415291904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.close 11))) (.step 24 (.step 3 (.step 4 (.close 15))))) (.split 43 0 (.split 49 0 (.step 67 (.step 24 (.close 3))) (.step 17 (.step 3 (.close 5)))) (.step 11 (.step 3 (.close 5))))) (.step 24 (.step 74 (.step 3 (.step 13 (.step 15 (.close 17))))))) (.split 36 0 (.split 38 0 (.split 39 0 (.step 75 (.step 15 (.step 23 (.step 24 (.close 17))))) (.step 11 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19))))))) (.step 3 (.close 4))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.close 3))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 20)))))) (.step 3 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.close 20)))))) (.step 5 (.step 13 (.close 24)))) (.step 3 (.step 5 (.step 11 (.step 17 (.close 19)))))) (.step 5 (.step 13 (.step 20 (.close 24))))) (.step 3 (.step 19 (.step 24 (.step 13 (.close 20)))))) (.step 5 (.step 13 (.step 17 (.close 24))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110189729449767519496643223433128143673261508589363658752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.split 39 0 (.step 24 (.step 11 (.step 17 (.step 13 (.step 15 (.close 20)))))) (.step 61 (.step 11 (.step 17 (.step 3 (.step 13 (.close 19)))))))) (.step 24 (.step 74 (.step 3 (.step 13 (.step 15 (.close 17))))))) (.split 36 0 (.split 38 0 (.step 61 (.split 39 0 (.step 15 (.step 23 (.step 24 (.step 9 (.close 17))))) (.step 11 (.step 17 (.step 4 (.step 15 (.step 24 (.close 38)))))))) (.step 3 (.close 4))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.close 3))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 20)))))) (.step 3 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.split 38 0 (.step 61 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 3 (.step 5 (.step 11 (.close 17)))))) (.step 5 (.step 13 (.step 20 (.step 9 (.close 17)))))) (.step 3 (.step 19 (.step 24 (.step 13 (.close 20)))))) (.step 5 (.step 13 (.step 17 (.close 24))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616455962435370140535449670082047288658339299328⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 17 0 (.split 22 0 (.split 30 0 (.reuse 0) (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 42 (.close 3))) (.step 5 (.close 42))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.step 15 (.close 24)))) (.step 5 (.step 24 (.step 17 (.step 19 (.close 13)))))) (.step 3 (.step 5 (.close 33))))) (.split 36 0 (.step 42 (.close 3)) (.step 3 (.step 38 (.step 9 (.close 17)))))) (.split 35 0 (.split 39 0 (.split 43 0 (.step 37 (.step 15 (.close 17))) (.step 13 (.step 43 (.step 33 (.step 24 (.step 3 (.step 9 (.close 37)))))))) (.step 5 (.step 17 (.close 24)))) (.step 3 (.step 38 (.step 9 (.close 17)))))))) (.reuse 1)) (.split 22 0 (.reuse 2) (.run (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.split 42 0 (.step 61 (.step 11 (.step 17 (.step 13 (.step 3 (.close 19)))))) (.step 11 (.step 13 (.step 17 (.step 20 (.step 3 (.close 19)))))))) (.step 11 (.step 13 (.step 17 (.close 20))))) (.step 11 (.step 17 (.step 19 (.step 20 (.step 3 (.close 13))))))) (.step 13 (.step 17 (.close 5))))) (.step 13 (.split 34 0 (.step 24 (.step 20 (.step 11 (.step 17 (.step 24 (.close 3)))))) (.step 17 (.step 5 (.close 20)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103221500280972921684818165865801324518180639347834880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 38 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.step 15 (.close 20))))))) (.step 24 (.step 3 (.step 4 (.close 15)))))) (.step 24 (.step 38 (.step 24 (.step 42 (.step 3 (.step 13 (.step 15 (.close 17))))))))) (.split 36 0 (.split 38 0 (.split 43 0 (.step 67 (.step 15 (.step 23 (.step 24 (.close 17))))) (.step 3 (.step 11 (.close 9)))) (.step 3 (.close 4))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 36 0 (.step 24 (.step 17 (.close 3))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 20)))))) (.step 3 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.step 24 (.split 34 0 (.step 42 (.step 3 (.close 13))) (.step 5 (.step 13 (.step 17 (.close 24))))))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 42 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 3 (.close 19)))))) (.step 11 (.step 13 (.step 17 (.step 19 (.step 3 (.close 20)))))))) (.step 11 (.step 13 (.step 17 (.step 19 (.step 5 (.close 20))))))) (.step 11 (.step 17 (.step 19 (.step 4 (.step 13 (.close 15))))))) (.step 13 (.step 17 (.close 5))))) (.step 13 (.step 42 (.step 33 (.step 24 (.step 25 (.close 3)))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599766273058739134502798330308314271842304⟩
def references : Fin 5 → Box := ![Part4.root, Part5.root, Part6.root, Part10.root, Part11.root]
def proof : Chunks.Proof 5 := (.split 14 0 (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 68 (.close 38)) (.step 42 (.step 3 (.step 9 (.step 13 (.close 19)))))) (.split 38 0 (.step 43 (.step 11 (.close 19))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4))))))) (.split 39 0 (.step 38 (.step 9 (.close 13))) (.step 43 (.step 27 (.step 38 (.step 13 (.close 19))))))) (.split 36 0 (.split 35 0 (.split 38 0 (.step 43 (.step 11 (.close 17))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.step 38 (.close 9))) (.step 38 (.step 43 (.step 3 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.step 38 (.step 11 (.close 19)))) (.step 38 (.step 11 (.close 19)))) (.step 38 (.step 11 (.close 17)))))) (.reuse 1)) (.reuse 2))) (.split 16 0 (.reuse 3) (.split 17 0 (.reuse 4) (.run (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 61 (.step 19 (.step 11 (.step 17 (.step 13 (.step 3 (.close 19)))))))) (.step 11 (.step 13 (.step 17 (.step 19 (.step 5 (.close 20))))))) (.step 11 (.step 17 (.step 19 (.step 4 (.step 13 (.close 15))))))) (.step 13 (.step 17 (.close 5))))) (.step 13 (.step 42 (.step 33 (.step 20 (.close 9)))))) (.split 34 0 (.step 25 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20))))))) (.step 17 (.step 19 (.close 20)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089160033932554097462382555867273411133646051751645112005544900079344665157198983590814918115328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 42 0 (.split 63 0 (.split 64 0 (.step 57 (.step 3 (.step 4 (.close 5)))) (.step 53 (.step 55 (.step 17 (.close 42))))) (.step 15 (.step 17 (.close 38)))) (.step 62 (.step 15 (.step 3 (.step 5 (.close 13))))))) (.step 62 (.split 39 0 (.step 29 (.step 43 (.close 15))) (.step 43 (.step 9 (.step 17 (.step 19 (.close 15)))))))) (.step 57 (.split 38 0 (.step 43 (.step 9 (.step 57 (.step 15 (.step 13 (.close 19)))))) (.step 18 (.step 38 (.step 18 (.step 5 (.close 15)))))))) (.split 36 0 (.split 38 0 (.split 22 0 (.step 9 (.step 38 (.step 15 (.step 53 (.step 24 (.step 13 (.step 5 (.close 17)))))))) (.step 62 (.step 68 (.step 23 (.step 17 (.step 24 (.step 15 (.close 38)))))))) (.split 22 0 (.split 43 0 (.step 21 (.step 38 (.close 3))) (.step 4 (.close 9))) (.step 4 (.step 15 (.step 3 (.step 5 (.close 17))))))) (.step 57 (.step 29 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.split 35 0 (.split 22 0 (.step 15 (.split 36 0 (.step 9 (.step 52 (.step 15 (.step 5 (.step 15 (.close 19)))))) (.step 15 (.close 5)))) (.step 43 (.step 15 (.close 3)))) (.step 15 (.step 29 (.step 15 (.close 37)))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941795536219794019538498746927521101512704⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 30 0 (.reuse 0) (.run (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 53 (.step 15 (.step 3 (.close 13))))) (.step 18 (.step 9 (.step 15 (.step 37 (.step 24 (.close 33))))))) (.split 42 0 (.step 42 (.step 4 (.step 9 (.step 17 (.step 15 (.close 20)))))) (.step 3 (.step 9 (.step 15 (.step 24 (.step 13 (.close 33)))))))) (.step 57 (.step 9 (.step 15 (.step 13 (.step 3 (.step 19 (.close 20)))))))) (.split 39 0 (.split 36 0 (.split 38 0 (.split 43 0 (.step 38 (.close 13)) (.step 9 (.close 3))) (.step 4 (.step 15 (.step 9 (.step 18 (.close 21)))))) (.step 29 (.step 37 (.close 38)))) (.step 4 (.step 9 (.close 38))))) (.split 36 0 (.step 15 (.step 18 (.step 9 (.step 38 (.step 15 (.step 13 (.close 20))))))) (.step 29 (.step 15 (.step 24 (.step 3 (.close 37))))))) (.step 24 (.split 34 0 (.step 18 (.split 35 0 (.step 24 (.step 9 (.step 43 (.close 15)))) (.step 38 (.step 9 (.close 13))))) (.step 24 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568640124460367288239972559055196025520128⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.split 38 0 (.split 42 0 (.step 68 (.step 27 (.step 17 (.step 61 (.close 15))))) (.step 9 (.step 18 (.step 15 (.step 17 (.step 20 (.close 19))))))) (.step 5 (.step 9 (.step 18 (.step 3 (.step 4 (.close 15))))))) (.step 18 (.step 17 (.close 24)))) (.step 43 (.step 66 (.step 5 (.close 24))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 9 (.step 42 (.step 15 (.step 4 (.step 17 (.step 19 (.close 20))))))) (.step 18 (.step 9 (.step 24 (.step 15 (.step 24 (.step 13 (.close 17)))))))) (.step 4 (.step 15 (.step 3 (.step 5 (.close 17)))))) (.step 29 (.step 38 (.step 37 (.step 18 (.step 20 (.close 19))))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))))) (.step 43 (.step 66 (.close 4)))) (.step 24 (.split 34 0 (.step 18 (.split 35 0 (.step 24 (.step 9 (.step 39 (.step 13 (.close 15))))) (.step 38 (.step 9 (.close 13))))) (.step 24 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15)))))))))))
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
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602286734919418671234115374552186880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 15 (.split 42 0 (.step 52 (.split 30 0 (.step 9 (.step 15 (.close 17))) (.step 5 (.step 11 (.step 15 (.step 13 (.close 17))))))) (.step 15 (.step 3 (.close 5))))) (.step 57 (.split 30 0 (.step 15 (.close 5)) (.step 3 (.step 13 (.close 15)))))) (.step 15 (.step 29 (.step 5 (.step 13 (.step 15 (.close 17))))))) (.step 15 (.step 29 (.step 43 (.step 5 (.step 24 (.step 5 (.close 16)))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 15 (.step 17 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 13 (.close 15)))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))))) (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 15 (.step 17 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 13 (.close 15)))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17)))))) (.step 17 (.step 3 (.close 13))))) (.split 17 0 (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 15 (.step 17 (.close 3))) (.step 3 (.close 4))) (.step 3 (.step 13 (.close 15)))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17)))))) (.step 17 (.step 3 (.close 13)))) (.step 17 (.close 13)))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602286734919418671234115374552186880⟩
def references : Fin 3 → Box := ![Part12.root, Part15.root, Part16.root]
def proof : Chunks.Proof 3 := (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.split 38 0 (.split 42 0 (.step 53 (.step 9 (.step 4 (.step 17 (.step 24 (.close 15)))))) (.step 9 (.step 18 (.step 15 (.step 17 (.step 19 (.step 20 (.close 19)))))))) (.step 5 (.step 9 (.step 18 (.step 3 (.step 4 (.close 15))))))) (.step 18 (.step 17 (.close 24)))) (.step 43 (.step 38 (.step 43 (.step 3 (.close 15)))))) (.split 22 0 (.split 39 0 (.step 38 (.step 3 (.close 9))) (.step 4 (.step 9 (.step 17 (.close 38))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))))) (.step 43 (.step 38 (.step 43 (.step 15 (.close 3)))))) (.step 24 (.split 34 0 (.step 18 (.step 53 (.close 15))) (.step 24 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15))))))))) (.split 22 0 (.step 24 (.split 34 0 (.step 18 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))) (.step 24 (.step 4 (.step 13 (.close 15)))))) (.step 24 (.step 3 (.step 19 (.step 15 (.close 20))))))))) (.reuse 2)))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636141717004981527992738203960344576, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188232872089498855480075963563696445286741888548732928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 52 (.step 33 (.step 3 (.step 9 (.close 20))))) (.split 42 0 (.step 42 (.step 3 (.step 33 (.step 9 (.step 13 (.close 24)))))) (.step 33 (.close 24)))) (.step 18 (.step 42 (.step 13 (.step 3 (.close 9)))))) (.split 38 0 (.split 39 0 (.split 49 0 (.split 42 0 (.step 43 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 13 (.step 33 (.step 39 (.close 3))))) (.step 13 (.step 20 (.close 24)))) (.step 33 (.step 20 (.step 13 (.close 19))))) (.step 33 (.close 3)))) (.split 36 0 (.split 38 0 (.split 39 0 (.split 42 0 (.step 42 (.step 29 (.step 18 (.step 13 (.step 33 (.close 38)))))) (.step 33 (.step 24 (.close 13)))) (.step 3 (.step 33 (.step 19 (.step 20 (.close 24)))))) (.step 3 (.step 9 (.step 13 (.close 18))))) (.step 33 (.step 24 (.close 13))))) (.split 35 0 (.split 36 0 (.step 15 (.split 39 0 (.split 38 0 (.step 52 (.close 3)) (.step 13 (.step 15 (.close 3)))) (.step 33 (.step 13 (.close 15))))) (.step 38 (.step 15 (.step 3 (.close 13))))) (.step 15 (.close 33)))))
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
def root : Box := ⟨1684996666696914987166688442938726918369972126637015181566752587776, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807103220038777941794206993065885222854072521957524373504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 3 (.step 13 (.close 20))))))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.close 24))) (.step 5 (.step 24 (.close 13)))) (.step 4 (.step 5 (.close 13))))) (.split 39 0 (.step 75 (.split 43 0 (.step 43 (.close 3)) (.step 24 (.step 4 (.close 9))))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 39 0 (.step 45 (.step 15 (.step 43 (.step 5 (.step 15 (.step 11 (.step 13 (.close 17)))))))) (.step 5 (.step 15 (.close 17)))) (.step 15 (.step 17 (.step 33 (.step 4 (.step 11 (.step 13 (.close 15))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 42 0 (.step 52 (.step 33 (.step 3 (.step 9 (.close 20))))) (.step 13 (.step 24 (.step 4 (.close 9))))) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 5 (.step 18 (.step 24 (.step 3 (.close 4))))))) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 33 (.step 43 (.step 3 (.step 4 (.close 39)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110189729449766125700068316536832397919098869563472740352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.close 24))) (.step 5 (.step 24 (.close 13)))) (.step 4 (.step 5 (.close 13))))) (.split 39 0 (.split 54 0 (.split 58 0 (.step 43 (.step 4 (.step 11 (.step 13 (.close 19))))) (.step 3 (.step 19 (.step 13 (.step 9 (.close 20)))))) (.step 4 (.step 24 (.step 29 (.step 38 (.step 13 (.step 19 (.close 20)))))))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 39 0 (.split 43 0 (.step 15 (.step 17 (.step 15 (.step 3 (.close 13))))) (.step 13 (.step 39 (.step 5 (.close 9))))) (.step 5 (.step 15 (.close 17)))) (.step 15 (.step 17 (.step 33 (.step 4 (.step 11 (.step 13 (.close 15))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 42 0 (.step 52 (.step 33 (.step 3 (.step 9 (.close 20))))) (.step 13 (.step 24 (.step 4 (.close 9))))) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 5 (.step 18 (.step 24 (.step 3 (.close 4))))))) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 33 (.step 39 (.step 5 (.step 9 (.close 15)))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568638795233639153924327884649632448380928⟩
def references : Fin 3 → Box := ![Part18.root, Part19.root, Part20.root]
def proof : Chunks.Proof 3 := (.split 17 0 (.split 22 0 (.split 30 0 (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 43 (.step 3 (.close 9)))) (.split 42 0 (.step 52 (.step 43 (.close 11))) (.step 43 (.step 11 (.step 13 (.close 19)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 29 (.step 18 (.step 13 (.close 33))))) (.step 43 (.step 11 (.step 13 (.close 19))))) (.step 18 (.step 43 (.step 33 (.step 3 (.close 9))))))) (.split 36 0 (.split 38 0 (.split 39 0 (.step 52 (.step 29 (.step 38 (.step 3 (.step 19 (.close 20)))))) (.step 42 (.step 4 (.step 9 (.step 13 (.close 19)))))) (.step 58 (.close 3))) (.split 38 0 (.step 57 (.step 43 (.step 29 (.step 33 (.step 13 (.close 3)))))) (.step 3 (.step 29 (.step 33 (.step 3 (.close 38)))))))) (.step 15 (.split 35 0 (.split 36 0 (.split 38 0 (.step 52 (.close 3)) (.step 15 (.close 3))) (.step 15 (.step 3 (.close 17)))) (.step 15 (.step 33 (.step 3 (.close 37)))))))) (.reuse 0)) (.reuse 1)) (.split 22 0 (.reuse 2) (.run (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.split 38 0 (.step 25 (.step 3 (.step 11 (.close 13)))) (.step 13 (.step 5 (.step 19 (.step 3 (.close 5))))))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 24 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 17 (.step 5 (.close 14)))))) (.step 13 (.step 33 (.step 24 (.split 42 0 (.step 17 (.close 20)) (.step 24 (.step 20 (.close 14)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188234333591136186382994167248529161569761544481275904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.step 5 (.step 18 (.step 24 (.step 3 (.close 4)))))) (.split 38 0 (.split 39 0 (.step 43 (.step 5 (.close 24))) (.step 5 (.step 24 (.close 13)))) (.step 4 (.step 5 (.close 13))))) (.split 39 0 (.split 54 0 (.split 58 0 (.step 38 (.step 9 (.close 13))) (.step 3 (.step 19 (.step 9 (.close 13))))) (.step 4 (.step 24 (.step 29 (.close 38))))) (.step 3 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.split 39 0 (.split 43 0 (.step 15 (.step 17 (.step 15 (.step 3 (.close 13))))) (.step 13 (.step 43 (.close 5)))) (.step 5 (.step 15 (.close 17)))) (.step 15 (.step 17 (.step 33 (.step 4 (.step 11 (.step 13 (.close 15))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 53 (.close 3)) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 5 (.step 18 (.step 24 (.step 3 (.close 4))))))) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.close 19))) (.step 13 (.step 33 (.close 38))))))
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
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616455962435370141803100270310276690155042504704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 15 (.step 11 (.step 13 (.close 17)))) (.step 42 (.step 15 (.step 11 (.step 13 (.close 17)))))) (.step 5 (.step 15 (.close 3)))) (.step 15 (.step 3 (.close 13)))) (.step 15 (.step 4 (.step 13 (.close 17))))) (.step 15 (.step 37 (.close 9))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 15 (.split 38 0 (.split 39 0 (.split 42 0 (.step 15 (.step 11 (.step 13 (.close 17)))) (.step 13 (.close 15))) (.step 17 (.close 13))) (.step 3 (.close 13)))) (.step 13 (.step 15 (.step 3 (.close 13))))) (.step 3 (.step 15 (.step 13 (.close 17))))) (.step 13 (.step 15 (.step 5 (.step 13 (.close 17))))))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 17 (.close 13)) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 5 (.step 13 (.close 15)))) (.step 3 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 15 (.close 17)))))) (.step 13 (.step 15 (.close 17))))) (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.split 38 0 (.step 17 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.step 11 (.close 13)))))) (.step 5 (.step 13 (.close 15)))) (.step 3 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 15 (.close 17)))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599766273060006785103026559709810975047680⟩
def references : Fin 3 → Box := ![Part21.root, Part22.root, Part23.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 38 0 (.step 25 (.step 3 (.step 11 (.close 13)))) (.step 13 (.step 5 (.close 19))))) (.step 13 (.step 20 (.step 19 (.close 9))))) (.step 19 (.step 13 (.step 19 (.step 4 (.close 20)))))) (.step 13 (.step 17 (.step 5 (.close 14)))))) (.step 13 (.step 33 (.step 24 (.step 38 (.step 20 (.step 17 (.step 11 (.close 4))))))))))) (.run (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 61 (.step 13 (.step 24 (.close 11))))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 19 (.step 4 (.close 20)))))) (.step 13 (.step 17 (.step 5 (.close 14)))))) (.step 13 (.step 33 (.step 24 (.step 38 (.step 20 (.step 4 (.step 14 (.close 15))))))))) (.split 34 0 (.step 25 (.step 19 (.step 13 (.step 11 (.step 3 (.close 20)))))) (.step 17 (.step 14 (.close 20)))))))) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 38 0 (.step 17 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.step 11 (.close 13)))))) (.step 5 (.step 13 (.close 15)))) (.step 3 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 15 (.close 17)))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17))) (.step 17 (.close 13))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104718077957599767602288002570018899463516871255392256⟩
def references : Fin 2 → Box := ![Part17.root, Part24.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 15 (.split 38 0 (.step 52 (.split 39 0 (.step 9 (.step 3 (.step 13 (.close 15)))) (.step 24 (.step 3 (.step 9 (.close 13)))))) (.step 15 (.close 3)))) (.step 57 (.step 15 (.close 3)))) (.step 15 (.step 29 (.step 15 (.step 24 (.step 33 (.close 37))))))) (.step 15 (.close 13))) (.step 24 (.split 30 0 (.split 34 0 (.step 18 (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.close 5))) (.step 24 (.close 13))))) (.split 22 0 (.step 24 (.split 30 0 (.split 34 0 (.step 18 (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.close 5))) (.step 24 (.close 13)))) (.step 17 (.close 13)))) (.split 17 0 (.split 22 0 (.step 24 (.split 30 0 (.split 34 0 (.step 18 (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.close 5))) (.step 24 (.close 13)))) (.step 17 (.close 13))) (.step 17 (.close 13)))) (.split 16 0 (.split 17 0 (.step 15 (.step 3 (.close 13))) (.step 3 (.close 17))) (.step 3 (.close 17)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part25

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part25.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case30

namespace FiveColour.Packed.EnumerationChunks.Projected.Case30
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 274 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 274 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 274 0).upper i := by decide +kernel
lemma budget_model : (⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 274), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 274) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 274 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 274 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 274) (Archive.root 274) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 274 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 274 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case30

namespace FiveColour.Packed.EnumerationChunks.Case30
def root : Box := Archive.root 274
def families : Fin 78 → List Cut := Enumeration.families 274
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case30.original_covered points
end FiveColour.Packed.EnumerationChunks.Case30
