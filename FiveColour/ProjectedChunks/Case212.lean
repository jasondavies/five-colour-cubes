module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case212
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129522136097096728576⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908127039438343431061, 5783586103091952671645525683118855883637551141936173497392551503491581408797949995482171711615842564202850511802448845755556307643640324931011181750967616418607933381130575579083625450524929735347627775953700440625201021953, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925211548997600684600320327747511517184000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 51 0 (.step 28 (.step 5 (.step 3 (.step 16 (.close 21))))) (.step 58 (.step 3 (.step 7 (.close 16))))) (.split 34 0 (.step 7 (.step 33 (.step 38 (.step 3 (.step 4 (.close 28)))))) (.step 37 (.step 7 (.step 33 (.close 3)))))) (.split 30 0 (.split 34 0 (.step 5 (.step 4 (.close 7))) (.step 37 (.step 5 (.step 4 (.close 7))))) (.step 7 (.step 33 (.close 4))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 5 (.step 4 (.close 7))) (.step 37 (.step 5 (.step 4 (.close 7))))) (.step 7 (.step 33 (.close 4)))) (.step 39 (.step 7 (.split 35 0 (.step 4 (.step 23 (.close 8))) (.step 4 (.close 9))))))) (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 33 (.close 4))) (.step 7 (.close 16))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 4 (.close 7)) (.step 7 (.step 4 (.close 20)))) (.step 7 (.step 45 (.close 4)))) (.step 7 (.step 33 (.step 24 (.step 25 (.step 23 (.step 19 (.step 4 (.close 9)))))))))) (.split 22 0 (.step 39 (.step 7 (.split 35 0 (.step 4 (.step 19 (.close 4))) (.step 4 (.close 9))))) (.split 30 0 (.step 39 (.step 19 (.step 7 (.step 4 (.step 19 (.close 4)))))) (.step 7 (.step 19 (.step 20 (.step 3 (.close 4))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750128368088692583038976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 12 0 (.split 34 0 (.step 7 (.close 58)) (.step 37 (.step 7 (.step 15 (.step 3 (.close 4)))))) (.step 37 (.step 7 (.step 13 (.close 3))))) (.step 7 (.step 33 (.step 13 (.step 3 (.step 15 (.close 4))))))) (.step 7 (.split 12 0 (.split 35 0 (.step 13 (.step 45 (.close 4))) (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 4 (.step 9 (.close 13)))))) (.step 7 (.split 22 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))))))) (.step 7 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 13 (.step 55 (.step 4 (.close 9)))) (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 4 (.step 9 (.close 13)))) (.step 13 (.split 30 0 (.split 34 0 (.step 24 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 17 (.step 8 (.close 14))))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))))) (.split 12 0 (.split 22 0 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))) (.step 19 (.step 13 (.step 20 (.step 3 (.close 4)))))) (.step 13 (.close 3)))))) (.step 7 (.split 12 0 (.split 35 0 (.step 13 (.close 3)) (.step 3 (.step 4 (.close 13)))) (.step 3 (.step 4 (.close 13)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750128368088692583038976⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 11 0 (.split 12 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 25 0 (.step 43 (.step 37 (.step 3 (.step 9 (.step 3 (.close 16)))))) (.step 28 (.step 3 (.close 7)))) (.step 29 (.step 37 (.close 3)))) (.step 37 (.step 7 (.step 18 (.close 9))))) (.step 4 (.step 37 (.step 7 (.step 4 (.step 9 (.step 4 (.close 3)))))))) (.step 4 (.step 37 (.step 43 (.step 3 (.close 16)))))) (.step 4 (.step 43 (.step 37 (.step 18 (.step 37 (.step 4 (.close 3)))))))))) (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 25 0 (.step 48 (.step 13 (.close 4))) (.step 28 (.close 3))) (.step 7 (.step 37 (.close 4)))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.close 14))))))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))))) (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 48 (.step 8 (.close 13))) (.step 3 (.step 4 (.step 8 (.step 13 (.close 19)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.close 19)))))) (.step 3 (.step 4 (.close 3)))) (.step 4 (.step 13 (.step 14 (.step 4 (.close 15)))))) (.step 3 (.step 4 (.close 7))))) (.split 16 0 (.step 4 (.step 43 (.step 3 (.close 15)))) (.step 4 (.close 3)))))) (.reuse 1))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129521010197189885952⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.reuse 0) (.run (.split 11 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 35 0 (.step 28 (.step 3 (.step 7 (.close 9)))) (.step 29 (.step 38 (.step 7 (.close 9))))) (.step 7 (.close 16))) (.step 28 (.close 7))) (.step 4 (.step 7 (.step 9 (.close 16))))) (.step 4 (.step 7 (.step 9 (.close 16))))) (.step 4 (.step 7 (.step 38 (.step 3 (.close 4)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 35 0 (.split 36 0 (.step 7 (.step 9 (.close 3))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 29 (.step 37 (.step 7 (.close 9))))) (.step 28 (.step 9 (.close 3)))) (.step 7 (.step 29 (.step 26 (.step 5 (.step 7 (.close 9))))))) (.step 7 (.step 29 (.step 48 (.close 7))))) (.step 7 (.step 29 (.step 38 (.step 4 (.close 3))))))) (.step 7 (.step 9 (.step 3 (.close 15))))) (.step 7 (.split 25 0 (.split 38 0 (.split 43 0 (.split 12 0 (.step 4 (.step 3 (.close 7))) (.step 48 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 7 (.step 9 (.close 15)))))) (.step 4 (.step 9 (.step 3 (.close 15)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517724792462873185107796416129422175664925212879524938334750129522136097096728576⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.reuse 0) (.run (.split 6 0 (.split 11 0 (.split 16 0 (.split 12 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 25 0 (.step 48 (.close 7)) (.step 28 (.close 3))) (.step 7 (.close 3))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 7 (.close 3))) (.split 17 0 (.step 4 (.step 43 (.step 3 (.close 9)))) (.step 3 (.step 4 (.close 3))))) (.step 7 (.step 4 (.close 7)))) (.step 7 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 7 (.step 48 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 7 (.step 4 (.close 7)))))) (.split 10 0 (.split 11 0 (.step 7 (.split 25 0 (.split 38 0 (.split 43 0 (.split 12 0 (.step 4 (.step 3 (.close 7))) (.step 48 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 7 (.close 9))))) (.step 4 (.close 9)))) (.split 12 0 (.step 4 (.step 3 (.close 5))) (.step 4 (.close 7)))) (.step 3 (.step 4 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part4.excludes
end FiveColour.Packed.ProjectedChunks.Case212
