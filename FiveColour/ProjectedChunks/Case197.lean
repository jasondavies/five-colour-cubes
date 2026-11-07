module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case197
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381450866263806682595328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908127039438276322181, 5783586103086692535743977309611614893754671013270623157589728329632083127894878141579324314801497516069343130184916114188557464454776446341801372575365668838217161194177556863441337178995616664966848005260749859088158950401, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634173919708781221482814905465700352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 4 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 11 0 (.split 22 0 (.split 26 0 (.step 58 (.close 7)) (.split 25 0 (.step 7 (.step 28 (.close 7))) (.step 28 (.close 7)))) (.step 45 (.step 4 (.close 3)))) (.split 22 0 (.split 26 0 (.split 25 0 (.step 37 (.close 48)) (.step 7 (.step 5 (.close 37)))) (.step 4 (.step 7 (.close 16)))) (.step 4 (.close 23)))) (.split 11 0 (.step 39 (.step 7 (.step 4 (.step 37 (.close 4))))) (.step 4 (.step 13 (.close 23))))) (.split 11 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 7 (.step 38 (.close 55))) (.step 7 (.close 16))) (.step 7 (.step 24 (.close 25)))) (.split 26 0 (.step 39 (.step 7 (.step 19 (.step 4 (.close 8))))) (.step 4 (.close 7)))) (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))))) (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 25 0 (.step 37 (.close 58)) (.step 29 (.close 28))) (.step 29 (.close 3))) (.step 37 (.step 7 (.close 4)))) (.step 4 (.step 37 (.step 7 (.close 43))))) (.step 4 (.step 37 (.step 38 (.step 7 (.close 43)))))) (.step 4 (.step 43 (.close 48))))) (.split 11 0 (.split 16 0 (.split 25 0 (.split 12 0 (.step 7 (.close 58)) (.step 29 (.step 13 (.step 7 (.close 3))))) (.step 7 (.close 28))) (.step 7 (.step 4 (.close 7)))) (.step 7 (.step 13 (.step 7 (.close 3)))))))
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381450865137906775752704⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.split 10 0 (.reuse 0) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 7 (.close 58)) (.step 37 (.close 16))) (.step 7 (.step 13 (.close 58)))) (.step 7 (.close 15))) (.step 7 (.close 3))) (.step 7 (.step 13 (.step 4 (.close 39))))) (.step 7 (.step 13 (.step 39 (.close 4))))) (.step 7 (.split 17 0 (.step 13 (.split 35 0 (.step 55 (.close 17)) (.step 4 (.close 38)))) (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.close 39))))))) (.step 7 (.step 13 (.close 3)))))) (.run (.split 11 0 (.split 16 0 (.split 4 0 (.split 12 0 (.split 22 0 (.split 26 0 (.split 25 0 (.step 7 (.step 28 (.step 7 (.close 9)))) (.step 28 (.close 7))) (.step 28 (.close 7))) (.step 4 (.step 7 (.close 28)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 7 (.close 9)) (.step 29 (.step 7 (.close 9)))) (.step 29 (.step 15 (.step 7 (.close 9))))) (.step 28 (.close 7))) (.step 7 (.close 48))) (.step 7 (.step 29 (.close 48))))) (.step 7 (.close 48))) (.step 7 (.step 38 (.close 48)))) (.step 7 (.split 38 0 (.split 34 0 (.step 4 (.close 9)) (.step 7 (.close 15))) (.step 4 (.close 48)))))))
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381450866263806682595328⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.reuse 0) (.run (.split 6 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 26 0 (.split 12 0 (.step 7 (.step 5 (.step 7 (.close 9)))) (.step 4 (.step 43 (.step 3 (.close 9))))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 4))) (.step 7 (.close 4))) (.step 7 (.step 4 (.step 7 (.close 4))))) (.step 7 (.split 25 0 (.split 38 0 (.split 43 0 (.split 11 0 (.step 48 (.close 7)) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 9))) (.step 4 (.close 9)))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case197
