module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case24
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129522136097096728576⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908127039438343431061, 5783586103091952671645525683118855883637551141936173497392551503491581408797949995482171711615842564202850511802448845755556307643640324931011181750967616418607933381130575579083625450524929735347627775953700440625201021953, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416127924136486661036057838823731066130232600180660633600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 51 0 (.step 28 (.step 5 (.step 3 (.close 21)))) (.step 58 (.step 3 (.step 7 (.close 21))))) (.split 25 0 (.split 35 0 (.step 58 (.step 3 (.step 5 (.close 8)))) (.split 36 0 (.step 38 (.step 3 (.step 9 (.step 3 (.close 16))))) (.step 37 (.step 38 (.close 3))))) (.split 35 0 (.step 28 (.step 3 (.close 7))) (.step 29 (.step 3 (.step 7 (.close 16))))))) (.split 34 0 (.split 35 0 (.step 7 (.step 58 (.close 8))) (.step 38 (.step 7 (.step 3 (.close 9))))) (.split 25 0 (.split 35 0 (.split 36 0 (.step 33 (.step 48 (.close 9))) (.step 37 (.step 33 (.close 3)))) (.step 37 (.step 33 (.close 3)))) (.step 7 (.step 16 (.close 28)))))) (.split 25 0 (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 45 (.step 4 (.close 3)))) (.step 33 (.split 34 0 (.split 35 0 (.step 4 (.step 33 (.close 4))) (.step 4 (.step 9 (.close 33)))) (.step 33 (.step 45 (.close 4)))))) (.step 7 (.step 4 (.step 5 (.step 16 (.close 28))))))))
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925211548997600684600320327747511517184000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.split 35 0 (.step 55 (.step 4 (.step 37 (.step 4 (.close 3))))) (.step 4 (.step 37 (.step 33 (.step 4 (.step 9 (.step 3 (.close 4))))))))) (.step 33 (.step 38 (.step 33 (.step 4 (.close 8)))))) (.step 7 (.step 4 (.step 5 (.step 16 (.close 28)))))) (.split 30 0 (.split 25 0 (.split 34 0 (.split 35 0 (.step 23 (.step 4 (.step 19 (.step 4 (.close 9))))) (.step 4 (.step 9 (.close 19)))) (.step 45 (.step 4 (.close 20)))) (.step 7 (.close 3))) (.step 7 (.step 33 (.step 38 (.step 23 (.step 25 (.close 4)))))))) (.split 22 0 (.split 30 0 (.step 39 (.split 25 0 (.split 34 0 (.step 4 (.step 23 (.step 4 (.step 19 (.close 3))))) (.step 39 (.close 4))) (.step 4 (.step 5 (.close 7))))) (.step 7 (.step 33 (.step 38 (.step 20 (.step 23 (.step 19 (.close 4)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 24 (.step 19 (.step 4 (.close 7)))) (.step 4 (.step 5 (.step 7 (.step 8 (.close 19)))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 39 (.step 4 (.step 19 (.step 3 (.close 4))))))) (.step 7 (.step 19 (.step 20 (.step 19 (.step 4 (.close 9))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1329227995784915872903807061354086400, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212878225596469516193231554571797528576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 37 (.step 3 (.step 9 (.step 3 (.close 16)))))) (.step 48 (.step 9 (.step 13 (.close 15))))) (.step 37 (.split 36 0 (.step 43 (.step 9 (.step 16 (.close 3)))) (.step 29 (.step 37 (.step 3 (.step 18 (.close 21)))))))) (.step 37 (.split 35 0 (.step 13 (.step 18 (.step 3 (.close 9)))) (.step 29 (.step 37 (.step 18 (.close 33))))))) (.split 30 0 (.split 35 0 (.step 48 (.step 7 (.close 15))) (.step 29 (.close 3))) (.step 7 (.close 29)))) (.step 43 (.step 37 (.step 4 (.step 5 (.step 16 (.step 21 (.close 28)))))))) (.split 22 0 (.step 43 (.step 37 (.step 4 (.step 5 (.step 16 (.step 21 (.close 28))))))) (.step 4 (.step 7 (.step 13 (.step 23 (.step 9 (.step 15 (.step 19 (.close 20)))))))))) (.split 17 0 (.split 22 0 (.step 43 (.step 37 (.step 4 (.step 5 (.step 16 (.step 21 (.close 28))))))) (.step 4 (.step 7 (.step 13 (.step 23 (.step 9 (.step 15 (.step 19 (.close 20))))))))) (.step 23 (.step 13 (.step 7 (.step 23 (.close 24))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129420714163287881975308660435283705177936412568190976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 12 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 58 (.step 39 (.step 28 (.step 3 (.close 13))))) (.split 35 0 (.split 36 0 (.step 16 (.step 9 (.step 5 (.close 13)))) (.step 37 (.step 16 (.close 9)))) (.step 37 (.step 15 (.close 3))))) (.step 33 (.split 57 0 (.step 13 (.step 33 (.step 3 (.close 9)))) (.step 45 (.step 4 (.step 3 (.step 9 (.close 13)))))))) (.step 7 (.step 15 (.step 16 (.close 28))))) (.step 7 (.split 30 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.close 8))) (.step 4 (.step 9 (.close 13)))) (.step 45 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9))))))))) (.split 22 0 (.split 25 0 (.split 30 0 (.step 37 (.split 35 0 (.step 13 (.step 16 (.close 9))) (.step 29 (.step 37 (.step 15 (.close 3)))))) (.step 13 (.close 3))) (.step 7 (.step 15 (.step 3 (.step 16 (.close 28)))))) (.step 4 (.step 7 (.close 13))))) (.step 7 (.split 12 0 (.split 22 0 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 25 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))) (.step 13 (.step 4 (.close 13)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212878226864120116421460956068500733952⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.step 7 (.split 12 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 34 0 (.split 35 0 (.step 4 (.step 13 (.close 4))) (.step 4 (.step 9 (.close 13)))) (.split 35 0 (.step 13 (.step 4 (.step 20 (.step 4 (.close 9))))) (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 13 (.step 5 (.step 8 (.close 14)))))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 25 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.split 38 0 (.step 23 (.step 19 (.step 3 (.close 4)))) (.step 4 (.step 5 (.step 8 (.close 13)))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9))))))) (.step 19 (.step 20 (.step 19 (.step 13 (.step 4 (.close 9)))))))) (.step 13 (.step 4 (.close 13)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1298074214633706907132625156046848, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925211550295674899234027234880135599489024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 3 (.close 8))) (.step 28 (.step 5 (.step 16 (.step 3 (.close 4)))))) (.step 4 (.step 37 (.close 3)))) (.step 37 (.step 58 (.step 3 (.step 8 (.close 13)))))) (.step 7 (.step 28 (.step 4 (.close 3))))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))))) (.split 22 0 (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.split 30 0 (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.step 7 (.step 13 (.step 4 (.step 20 (.step 4 (.close 8))))))))) (.split 17 0 (.split 22 0 (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.split 30 0 (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.step 7 (.step 13 (.step 4 (.step 19 (.step 4 (.step 8 (.close 14))))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 4 (.step 13 (.close 4))) (.step 7 (.step 13 (.step 4 (.close 8))))) (.step 4 (.step 7 (.step 8 (.close 13))))) (.step 7 (.step 4 (.step 8 (.step 13 (.close 19)))))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.close 19))))))) (.step 4 (.step 7 (.step 13 (.step 14 (.close 15)))))) (.step 7 (.step 13 (.step 19 (.step 20 (.step 4 (.close 8))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750128368088692583038976⟩
def references : Fin 5 → Box := ![Part0.root, Part1.root, Part2.root, Part4.root, Part5.root]
def proof : Chunks.Proof 5 := (.split 11 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 39 (.step 5 (.step 4 (.close 8))))) (.step 33 (.step 39 (.step 4 (.step 33 (.step 3 (.close 4))))))) (.step 7 (.step 4 (.step 5 (.step 16 (.close 28)))))) (.split 30 0 (.step 39 (.split 25 0 (.split 34 0 (.step 4 (.step 23 (.step 4 (.step 19 (.step 4 (.close 8)))))) (.step 39 (.close 4))) (.step 4 (.step 5 (.close 7))))) (.step 7 (.step 33 (.split 34 0 (.step 24 (.step 25 (.step 23 (.step 24 (.close 8))))) (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 10 0 (.split 12 0 (.reuse 4) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 43 (.split 25 0 (.step 37 (.step 4 (.step 3 (.step 5 (.close 15))))) (.step 4 (.step 15 (.step 3 (.close 16)))))) (.step 4 (.close 13))) (.step 4 (.step 17 (.close 4)))) (.step 23 (.step 4 (.step 13 (.step 4 (.close 14)))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 37 (.split 12 0 (.step 7 (.step 58 (.step 3 (.step 8 (.close 13))))) (.step 3 (.step 4 (.step 9 (.close 13)))))) (.step 7 (.step 13 (.close 3)))) (.step 7 (.step 13 (.close 4)))) (.step 7 (.step 13 (.step 4 (.close 13))))) (.step 7 (.step 13 (.step 4 (.close 13))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1152921505680588800, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212878226864120116422613877573107580928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 10 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 58 (.close 7))) (.step 28 (.step 48 (.close 7)))) (.split 36 0 (.split 51 0 (.step 9 (.step 3 (.close 16))) (.step 7 (.close 9))) (.step 29 (.step 38 (.step 3 (.step 7 (.close 9))))))) (.step 7 (.step 16 (.close 21)))) (.step 28 (.step 29 (.close 3)))) (.step 7 (.step 48 (.close 3)))) (.step 7 (.split 25 0 (.step 48 (.step 4 (.close 7))) (.step 4 (.step 28 (.step 3 (.close 7))))))) (.split 17 0 (.split 22 0 (.split 25 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 51 0 (.step 9 (.step 3 (.close 15))) (.step 43 (.step 9 (.close 3)))) (.step 29 (.step 37 (.step 3 (.step 7 (.close 9)))))) (.step 7 (.step 37 (.close 3)))) (.step 29 (.step 37 (.split 36 0 (.split 51 0 (.step 9 (.close 3)) (.step 7 (.close 9))) (.step 37 (.step 38 (.close 3))))))) (.step 29 (.step 3 (.close 9)))) (.step 7 (.step 29 (.step 48 (.close 7))))) (.step 7 (.step 29 (.step 48 (.close 7)))))) (.step 7 (.step 29 (.step 15 (.step 3 (.step 7 (.close 21))))))) (.step 7 (.split 12 0 (.step 38 (.step 4 (.step 38 (.step 4 (.step 3 (.step 5 (.close 16))))))) (.split 35 0 (.split 25 0 (.step 48 (.close 7)) (.step 4 (.step 21 (.step 5 (.step 16 (.step 9 (.close 21))))))) (.step 21 (.step 29 (.close 38))))))))
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
def root : Box := ⟨1125900980584448, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750128369214592489881600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 10 0 (.split 12 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 3 (.close 7))) (.step 28 (.step 5 (.step 16 (.step 3 (.close 4)))))) (.step 4 (.step 48 (.close 7)))) (.step 7 (.close 3))) (.step 7 (.step 28 (.step 4 (.close 3))))) (.step 43 (.split 25 0 (.step 37 (.step 4 (.step 3 (.step 5 (.close 9))))) (.step 4 (.step 9 (.step 3 (.close 16))))))) (.step 7 (.step 4 (.close 7)))) (.step 7 (.step 4 (.close 7)))) (.step 7 (.step 4 (.step 7 (.close 3))))) (.step 7 (.step 40 (.step 4 (.close 7))))) (.split 10 0 (.split 12 0 (.step 7 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 7 (.split 49 0 (.step 8 (.step 3 (.close 4))) (.step 4 (.step 7 (.close 8))))) (.step 7 (.step 4 (.close 7)))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.split 16 0 (.step 7 (.step 4 (.step 7 (.close 8)))) (.step 7 (.close 8))))) (.split 16 0 (.split 17 0 (.step 4 (.split 22 0 (.step 4 (.close 7)) (.step 4 (.close 3)))) (.step 4 (.step 3 (.close 5)))) (.step 4 (.step 3 (.close 5))))) (.step 7 (.close 3)))))
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
def root : Box := ⟨1125900980584448, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129522136097096728576⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.reuse 0) (.run (.split 10 0 (.split 11 0 (.split 12 0 (.step 7 (.split 16 0 (.split 25 0 (.split 38 0 (.split 43 0 (.split 17 0 (.step 43 (.close 48)) (.step 4 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 7 (.step 9 (.close 16)))))) (.step 4 (.step 9 (.step 3 (.close 16))))) (.step 7 (.close 4)))) (.split 25 0 (.split 30 0 (.split 34 0 (.split 38 0 (.split 43 0 (.split 36 0 (.step 4 (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.close 9)))) (.step 7 (.step 37 (.close 3)))) (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 9 (.close 16))))) (.split 12 0 (.split 16 0 (.split 17 0 (.step 4 (.split 22 0 (.step 4 (.close 7)) (.step 4 (.close 3)))) (.step 4 (.step 3 (.close 5)))) (.step 4 (.step 3 (.close 5)))) (.step 4 (.close 7)))) (.step 7 (.step 3 (.close 4))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129522136097096728576⟩
def references : Fin 3 → Box := ![Part6.root, Part7.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 5 0 (.split 6 0 (.reuse 0) (.split 11 0 (.reuse 1) (.run (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.split 25 0 (.split 38 0 (.split 43 0 (.split 17 0 (.step 43 (.close 48)) (.step 4 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 7 (.step 15 (.close 16)))))) (.step 4 (.step 16 (.step 5 (.step 9 (.close 15)))))) (.step 7 (.close 4)))) (.split 25 0 (.split 30 0 (.split 34 0 (.split 38 0 (.split 43 0 (.split 36 0 (.step 4 (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 3 (.close 4))))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 9 (.step 3 (.close 15)))))) (.step 7 (.step 15 (.close 4)))) (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 15 (.step 3 (.close 16)))))) (.step 3 (.step 4 (.close 7))))))) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part10.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case24

namespace FiveColour.Packed.EnumerationChunks.Projected.Case24
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 268 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 268 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 268 0).upper i := by decide +kernel
lemma budget_model : (⟨32908127039438343431061, 5783586103091952671645525683118855883637551141936173497392551503491581408797949995482171711615842564202850511802448845755556307643640324931011181750967616418607933381130575579083625450524929735347627775953700440625201021953, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 268), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908127039438343431061, 5783586103091952671645525683118855883637551141936173497392551503491581408797949995482171711615842564202850511802448845755556307643640324931011181750967616418607933381130575579083625450524929735347627775953700440625201021953, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 268) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 268 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 268 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 268) (Archive.root 268) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 268 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 268 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case24

namespace FiveColour.Packed.EnumerationChunks.Case24
def root : Box := Archive.root 268
def families : Fin 78 → List Cut := Enumeration.families 268
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case24.original_covered points
end FiveColour.Packed.EnumerationChunks.Case24
