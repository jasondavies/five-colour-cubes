module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case42
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005536014537700937011843338568940388352⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908127039438376985589, 5783586103091957813513448549065477704101332453097102403927030543402094319394108592887551773511915116652793239902302694320363413592187732277592161523456540874451485486766787986221277724849666005459465451175879706183626392577, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211477167045576225916296209049657889987411320775726604922069988042342400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.step 58 (.step 3 (.step 5 (.close 8)))) (.split 38 0 (.step 58 (.step 26 (.step 9 (.close 38)))) (.split 54 0 (.step 3 (.step 33 (.close 21))) (.step 38 (.close 3))))) (.split 35 0 (.split 36 0 (.step 58 (.step 3 (.step 5 (.close 8)))) (.split 38 0 (.step 58 (.step 37 (.step 39 (.close 3)))) (.step 37 (.step 39 (.step 3 (.close 28)))))) (.split 36 0 (.split 38 0 (.step 58 (.step 26 (.step 9 (.close 37)))) (.step 37 (.step 3 (.step 18 (.step 3 (.close 21)))))) (.step 37 (.step 39 (.step 3 (.step 9 (.step 3 (.close 21))))))))) (.split 34 0 (.split 35 0 (.split 38 0 (.step 58 (.step 33 (.step 28 (.close 9)))) (.step 33 (.step 41 (.close 9)))) (.split 38 0 (.split 46 0 (.step 38 (.close 3)) (.step 3 (.step 9 (.close 18)))) (.step 3 (.step 33 (.step 3 (.close 38)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 58 (.step 33 (.step 28 (.close 9)))) (.step 33 (.close 3))) (.step 37 (.step 33 (.step 39 (.step 3 (.close 28)))))) (.step 37 (.step 38 (.close 3)))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832779953414727673302568996365954487519977731941990400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.step 4 (.step 39 (.step 3 (.close 4)))) (.step 39 (.step 4 (.close 3)))) (.step 43 (.split 46 0 (.step 40 (.step 9 (.close 37))) (.step 4 (.step 23 (.step 4 (.step 24 (.close 8)))))))) (.step 59 (.step 33 (.close 4)))) (.split 38 0 (.split 43 0 (.step 39 (.step 4 (.step 33 (.step 3 (.close 4))))) (.step 33 (.step 39 (.step 3 (.close 4))))) (.step 33 (.close 3)))) (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.split 35 0 (.step 4 (.step 20 (.close 4))) (.step 4 (.step 19 (.close 20)))) (.step 39 (.close 4))) (.step 23 (.step 43 (.step 24 (.step 25 (.close 4)))))) (.step 39 (.step 4 (.step 5 (.close 8))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 4 (.step 23 (.step 20 (.close 25)))) (.step 33 (.step 4 (.close 8)))) (.step 25 (.step 4 (.close 5)))) (.step 33 (.step 20 (.close 9)))) (.step 24 (.step 4 (.step 3 (.close 5))))) (.step 33 (.step 39 (.close 4)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922831284837239738159617246626782085729990869712950525952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.step 4 (.step 38 (.step 4 (.close 3)))) (.split 36 0 (.step 4 (.step 38 (.close 3))) (.step 37 (.step 4 (.step 18 (.step 4 (.close 38))))))) (.step 43 (.split 46 0 (.step 40 (.step 9 (.close 37))) (.step 4 (.step 23 (.step 4 (.step 24 (.close 8)))))))) (.split 54 0 (.split 34 0 (.step 48 (.step 3 (.step 8 (.close 19)))) (.step 33 (.step 37 (.step 33 (.step 4 (.close 8)))))) (.step 3 (.step 4 (.step 38 (.close 3)))))) (.split 38 0 (.split 43 0 (.step 38 (.step 33 (.step 4 (.close 16)))) (.step 33 (.step 40 (.step 9 (.step 4 (.close 37)))))) (.step 33 (.close 3)))) (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.split 35 0 (.step 4 (.step 20 (.step 4 (.close 19)))) (.step 4 (.step 19 (.close 20)))) (.split 46 0 (.step 45 (.step 4 (.close 17))) (.step 4 (.step 17 (.close 16))))) (.step 23 (.step 43 (.step 24 (.step 25 (.close 4)))))) (.split 35 0 (.split 46 0 (.step 23 (.step 5 (.step 8 (.close 19)))) (.step 3 (.step 4 (.step 8 (.close 19))))) (.step 3 (.step 4 (.close 5))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 4 (.step 19 (.close 4))) (.step 33 (.step 4 (.close 8)))) (.step 25 (.step 4 (.close 5)))) (.step 33 (.step 20 (.step 4 (.close 9))))) (.step 24 (.step 4 (.step 3 (.close 5))))) (.step 33 (.step 38 (.step 8 (.step 16 (.close 20)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004205487200050787203802997387874533376⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.split 35 0 (.step 4 (.step 20 (.close 4))) (.step 4 (.step 19 (.close 20)))) (.step 39 (.close 4))) (.step 23 (.step 43 (.step 24 (.step 54 (.close 4)))))) (.step 39 (.step 4 (.step 5 (.close 8))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 4 (.step 19 (.close 4))) (.step 33 (.step 4 (.close 8)))) (.step 25 (.step 4 (.step 5 (.step 8 (.close 19)))))) (.step 33 (.step 20 (.close 9)))) (.step 24 (.step 4 (.step 3 (.close 5))))) (.step 33 (.step 38 (.step 8 (.step 16 (.close 20))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 25 (.step 48 (.close 8))) (.step 19 (.step 3 (.step 4 (.close 9))))) (.step 25 (.step 19 (.close 20)))) (.step 24 (.step 19 (.close 3)))) (.split 35 0 (.split 36 0 (.step 25 (.step 19 (.step 20 (.close 4)))) (.step 20 (.step 25 (.step 4 (.step 19 (.step 3 (.close 4))))))) (.step 17 (.step 24 (.step 3 (.close 4)))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922831283375738100828714329690747853241937251553721188352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 38 0 (.step 58 (.step 13 (.step 28 (.close 9)))) (.step 33 (.step 55 (.step 9 (.close 13))))) (.split 38 0 (.split 46 0 (.step 58 (.step 9 (.close 13))) (.step 3 (.step 9 (.close 13)))) (.step 3 (.step 33 (.step 3 (.close 38)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 52 (.close 8)) (.step 16 (.step 9 (.close 13)))) (.step 37 (.step 39 (.step 15 (.step 3 (.close 16)))))) (.step 37 (.split 51 0 (.split 53 0 (.step 15 (.close 3)) (.step 3 (.step 9 (.close 15)))) (.step 15 (.close 3)))))) (.split 34 0 (.step 33 (.split 35 0 (.step 13 (.step 33 (.step 3 (.step 18 (.step 4 (.close 9)))))) (.step 33 (.close 3)))) (.split 43 0 (.split 35 0 (.split 36 0 (.step 33 (.step 13 (.close 3))) (.step 37 (.step 33 (.step 3 (.step 15 (.close 4)))))) (.step 33 (.close 3))) (.step 13 (.step 33 (.step 52 (.close 14))))))) (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.split 35 0 (.step 4 (.step 13 (.close 4))) (.step 4 (.step 13 (.close 38)))) (.step 45 (.step 4 (.close 13)))) (.step 13 (.step 40 (.step 9 (.step 4 (.close 15)))))) (.step 33 (.step 45 (.step 4 (.close 8))))) (.step 13 (.step 33 (.step 45 (.step 3 (.close 4))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922831284837239738159617247894432685958220271209653731328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 46 0 (.split 34 0 (.step 4 (.step 13 (.close 38))) (.split 57 0 (.step 15 (.step 3 (.close 4))) (.step 4 (.step 13 (.step 4 (.close 14)))))) (.step 4 (.close 13))) (.step 13 (.step 40 (.step 9 (.step 4 (.close 15)))))) (.step 33 (.step 41 (.step 4 (.step 13 (.step 4 (.close 8))))))) (.step 13 (.step 33 (.step 38 (.step 8 (.close 14)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 4 (.step 19 (.close 3))) (.step 13 (.step 4 (.close 19)))) (.step 13 (.step 23 (.step 4 (.step 9 (.close 19)))))) (.step 13 (.step 4 (.step 5 (.step 8 (.close 19)))))) (.step 13 (.step 20 (.step 24 (.step 3 (.close 8)))))) (.step 13 (.step 45 (.step 17 (.step 4 (.step 5 (.step 8 (.close 14)))))))) (.step 13 (.step 33 (.step 38 (.step 14 (.step 8 (.close 20)))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004205488467701387432032398884577738752⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.step 39 (.step 4 (.step 13 (.close 4)))) (.step 13 (.step 39 (.step 3 (.close 4))))) (.step 33 (.step 39 (.close 4)))) (.step 13 (.step 33 (.step 39 (.close 3))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 4 (.step 24 (.close 13))) (.step 13 (.step 4 (.step 19 (.step 4 (.close 8)))))) (.step 13 (.step 23 (.step 4 (.step 9 (.close 19)))))) (.step 13 (.step 4 (.step 5 (.step 8 (.close 19)))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 19)))))) (.step 13 (.step 39 (.step 4 (.step 14 (.close 9)))))) (.step 13 (.step 33 (.step 39 (.step 3 (.close 4))))))))) (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 4 (.step 19 (.close 3))) (.step 13 (.step 4 (.close 19)))) (.step 13 (.step 23 (.step 4 (.step 9 (.close 19)))))) (.step 13 (.step 4 (.step 5 (.step 8 (.close 19)))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 19)))))) (.step 13 (.step 39 (.step 4 (.step 14 (.close 9)))))) (.step 13 (.step 33 (.step 38 (.step 14 (.step 8 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 25 (.step 19 (.step 3 (.close 4)))) (.step 13 (.step 17 (.close 14)))) (.step 13 (.step 19 (.step 20 (.step 23 (.step 17 (.step 4 (.close 9))))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832779953414727674631796992150870360423784792222334976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 38 0 (.step 43 (.step 58 (.close 9))) (.split 36 0 (.step 3 (.step 55 (.step 9 (.close 13)))) (.step 37 (.step 3 (.step 18 (.close 21)))))) (.split 36 0 (.split 51 0 (.split 56 0 (.step 9 (.step 18 (.close 16))) (.step 21 (.step 3 (.step 9 (.step 3 (.close 16)))))) (.step 57 (.step 3 (.close 9)))) (.step 29 (.step 37 (.step 38 (.close 3)))))) (.split 38 0 (.split 46 0 (.split 49 0 (.split 54 0 (.step 37 (.close 3)) (.step 15 (.close 3))) (.step 15 (.step 3 (.close 9)))) (.step 37 (.close 3))) (.step 37 (.close 3)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 13 (.step 43 (.step 18 (.close 9)))) (.step 3 (.step 37 (.step 3 (.step 9 (.close 18)))))) (.step 37 (.step 33 (.step 39 (.close 3))))) (.step 29 (.step 37 (.close 38))))) (.split 30 0 (.split 38 0 (.split 43 0 (.step 43 (.step 48 (.close 13))) (.step 4 (.close 9))) (.step 4 (.step 37 (.step 3 (.step 5 (.close 21)))))) (.step 4 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15)))))))) (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.step 43 (.step 48 (.close 13))) (.step 4 (.close 9))) (.step 4 (.step 37 (.step 3 (.step 5 (.close 21)))))) (.step 4 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15))))))) (.split 30 0 (.step 4 (.step 13 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))) (.step 13 (.step 23 (.close 24)))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005534716463486303304936205944858083328⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 10 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 36 0 (.split 38 0 (.split 35 0 (.step 13 (.close 3)) (.step 13 (.step 3 (.close 15)))) (.step 3 (.step 16 (.step 9 (.close 13))))) (.step 37 (.step 39 (.step 15 (.close 3))))) (.step 13 (.close 3))) (.split 30 0 (.step 37 (.close 3)) (.step 13 (.step 3 (.close 15))))) (.step 13 (.step 4 (.close 13)))) (.step 13 (.step 4 (.close 13)))))) (.run (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.step 43 (.step 38 (.step 3 (.step 18 (.step 15 (.step 3 (.close 16))))))) (.step 4 (.close 9))) (.step 4 (.step 37 (.step 3 (.step 5 (.close 21)))))) (.step 4 (.step 13 (.step 33 (.step 4 (.step 9 (.close 15))))))) (.split 30 0 (.step 4 (.step 13 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))) (.step 13 (.step 23 (.close 24))))) (.split 22 0 (.split 30 0 (.step 4 (.step 13 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))) (.step 13 (.step 23 (.close 24)))) (.step 23 (.close 24)))) (.step 13 (.step 4 (.close 13))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1298074214633706907132625156046848, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922831283375738100828715626497311886720614982681100288000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 38 0 (.split 34 0 (.split 35 0 (.step 43 (.step 4 (.step 3 (.step 4 (.close 8))))) (.step 4 (.step 3 (.step 9 (.close 13))))) (.split 46 0 (.split 35 0 (.step 43 (.step 3 (.close 8))) (.step 15 (.close 3))) (.step 16 (.step 28 (.close 37))))) (.split 54 0 (.step 28 (.split 35 0 (.split 51 0 (.step 5 (.step 4 (.close 13))) (.step 3 (.step 5 (.step 13 (.close 14))))) (.step 3 (.step 4 (.step 3 (.step 5 (.close 37))))))) (.step 3 (.step 4 (.step 16 (.step 3 (.step 5 (.close 15)))))))) (.split 38 0 (.split 43 0 (.step 37 (.step 58 (.step 3 (.close 13)))) (.step 13 (.step 28 (.step 9 (.step 4 (.close 15)))))) (.step 3 (.step 13 (.step 23 (.step 5 (.close 15))))))) (.split 30 0 (.split 54 0 (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))) (.step 3 (.step 4 (.close 13)))) (.step 13 (.step 4 (.step 33 (.step 4 (.step 8 (.close 14)))))))))
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
def root : Box := ⟨1461501637330904216277899466423190152281088589824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004206786541916021138939531508660043776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 10 0 (.split 22 0 (.split 30 0 (.split 54 0 (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))) (.step 3 (.step 4 (.close 13)))) (.step 13 (.step 4 (.step 33 (.step 4 (.step 8 (.close 14))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 25 (.step 4 (.step 8 (.close 13)))) (.step 3 (.step 4 (.step 8 (.step 13 (.close 19)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.close 19)))))) (.step 4 (.close 3))) (.step 4 (.step 13 (.step 14 (.close 15))))) (.step 13 (.step 33 (.step 25 (.step 4 (.close 8))))))) (.step 13 (.step 4 (.close 13)))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 48 (.step 3 (.step 8 (.close 13)))) (.step 4 (.step 13 (.step 4 (.close 8))))) (.step 4 (.step 8 (.step 4 (.step 13 (.close 19)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.close 19)))))) (.step 13 (.step 4 (.step 14 (.close 15))))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 8)))))) (.split 30 0 (.split 34 0 (.step 25 (.step 13 (.step 4 (.step 8 (.step 4 (.close 13)))))) (.step 13 (.step 39 (.step 4 (.step 14 (.close 15)))))) (.step 13 (.step 19 (.step 20 (.step 4 (.close 8)))))))))
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
def root : Box := ⟨1298074214633706907132625156046848, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004206786541916021138939531508660043776⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 16 0 (.split 10 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 54 0 (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))) (.step 3 (.step 4 (.close 13)))) (.step 13 (.step 4 (.step 33 (.step 4 (.step 8 (.close 14))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 25 (.step 4 (.step 8 (.close 13)))) (.step 3 (.step 4 (.step 8 (.step 13 (.close 19)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.step 19 (.close 20))))))) (.step 4 (.close 3))) (.step 4 (.step 13 (.step 14 (.close 15))))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 8))))))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.step 37 (.step 58 (.step 3 (.close 13)))) (.step 13 (.step 28 (.step 9 (.step 4 (.close 13)))))) (.step 3 (.step 13 (.close 16)))) (.step 13 (.close 3))) (.step 13 (.step 4 (.close 13)))) (.step 13 (.step 4 (.close 13)))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005536014537700937011843338568940388352⟩
def references : Fin 6 → Box := ![Part0.root, Part1.root, Part3.root, Part6.root, Part8.root, Part11.root]
def proof : Chunks.Proof 6 := (.split 11 0 (.split 12 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 38 0 (.split 43 0 (.split 34 0 (.step 4 (.step 43 (.close 3))) (.step 45 (.step 4 (.close 3)))) (.step 43 (.split 46 0 (.step 40 (.step 9 (.close 37))) (.step 4 (.step 23 (.step 4 (.step 24 (.close 8)))))))) (.split 54 0 (.split 34 0 (.step 48 (.step 3 (.step 8 (.close 19)))) (.step 33 (.step 37 (.step 33 (.step 4 (.close 8)))))) (.step 3 (.step 4 (.step 38 (.close 3)))))) (.split 38 0 (.split 43 0 (.split 34 0 (.split 35 0 (.step 4 (.step 33 (.close 4))) (.step 4 (.close 33))) (.step 45 (.step 4 (.close 33)))) (.step 33 (.step 40 (.step 9 (.step 4 (.close 37)))))) (.step 33 (.close 3)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.split 12 0 (.reuse 5) (.run (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 43 (.step 48 (.close 4))) (.split 38 0 (.step 68 (.step 15 (.step 3 (.close 4)))) (.step 4 (.step 15 (.step 3 (.close 16)))))) (.step 3 (.step 4 (.step 13 (.step 15 (.close 3)))))) (.step 4 (.step 17 (.step 4 (.close 15))))) (.step 4 (.step 17 (.step 23 (.step 4 (.step 15 (.close 14))))))) (.split 17 0 (.step 4 (.step 17 (.step 23 (.step 4 (.step 15 (.close 14)))))) (.step 4 (.step 17 (.step 3 (.step 4 (.step 14 (.step 4 (.step 19 (.step 4 (.close 20))))))))))) (.step 3 (.step 13 (.step 4 (.step 13 (.step 4 (.step 9 (.close 13)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part3.excludes
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part12.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case42

namespace FiveColour.Packed.EnumerationChunks.Projected.Case42
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 286 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 286 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 286 0).upper i := by decide +kernel
lemma budget_model : (⟨32908127039438376985589, 5783586103091957813513448549065477704101332453097102403927030543402094319394108592887551773511915116652793239902302694320363413592187732277592161523456540874451485486766787986221277724849666005459465451175879706183626392577, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 286), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908127039438376985589, 5783586103091957813513448549065477704101332453097102403927030543402094319394108592887551773511915116652793239902302694320363413592187732277592161523456540874451485486766787986221277724849666005459465451175879706183626392577, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 286) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 286 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 286 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 286) (Archive.root 286) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 286 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 286 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case42

namespace FiveColour.Packed.EnumerationChunks.Case42
def root : Box := Archive.root 286
def families : Fin 78 → List Cut := Enumeration.families 286
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case42.original_covered points
end FiveColour.Packed.EnumerationChunks.Case42
