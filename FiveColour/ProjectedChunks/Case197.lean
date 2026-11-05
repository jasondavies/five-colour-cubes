module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634173919708781221482813805954072576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 11 0 (.split 22 0 (.split 26 0 (.step 58 (.step 3 (.step 4 (.close 7)))) (.split 25 0 (.step 7 (.step 28 (.close 7))) (.step 28 (.close 7)))) (.step 45 (.step 4 (.close 3)))) (.split 22 0 (.split 26 0 (.split 25 0 (.step 37 (.step 4 (.close 3))) (.step 7 (.step 5 (.step 7 (.close 4))))) (.step 4 (.step 7 (.step 3 (.close 15))))) (.step 4 (.step 7 (.step 8 (.close 13)))))) (.split 11 0 (.step 39 (.step 7 (.step 4 (.step 37 (.close 4))))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.close 14)))))))) (.split 11 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 7 (.step 38 (.step 4 (.close 8)))) (.step 7 (.close 16))) (.step 7 (.step 24 (.step 3 (.step 8 (.close 16)))))) (.step 39 (.split 26 0 (.step 39 (.step 7 (.step 19 (.step 4 (.close 8))))) (.step 4 (.close 7))))) (.step 4 (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))))) (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 25 0 (.step 37 (.step 18 (.step 9 (.step 3 (.step 13 (.close 16)))))) (.step 29 (.step 3 (.step 7 (.step 3 (.close 15)))))) (.step 29 (.close 3))) (.step 4 (.step 37 (.step 7 (.close 4))))) (.step 4 (.step 37 (.step 7 (.step 4 (.close 9)))))) (.step 4 (.step 37 (.step 38 (.step 7 (.step 4 (.step 9 (.step 4 (.close 3))))))))) (.step 4 (.step 43 (.step 3 (.close 15)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381449712216402168905728⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 4 0 (.reuse 0) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 25 0 (.split 12 0 (.step 7 (.step 28 (.step 4 (.step 3 (.close 7))))) (.step 29 (.step 13 (.step 7 (.close 3))))) (.step 7 (.step 15 (.close 16)))) (.step 7 (.close 3))) (.step 7 (.step 4 (.close 7)))) (.step 7 (.step 13 (.step 7 (.close 3))))))) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 7 (.step 13 (.step 4 (.step 3 (.step 9 (.close 13)))))) (.step 37 (.step 4 (.step 7 (.step 3 (.close 9)))))) (.step 7 (.step 13 (.step 33 (.close 3))))) (.step 7 (.close 15))) (.step 7 (.close 3))) (.step 7 (.step 13 (.step 4 (.step 20 (.step 4 (.close 9))))))) (.step 7 (.step 13 (.step 39 (.step 3 (.close 4)))))) (.step 7 (.step 13 (.split 17 0 (.step 13 (.split 35 0 (.step 55 (.step 4 (.close 9))) (.step 4 (.step 9 (.close 15))))) (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))))))) (.step 7 (.step 13 (.close 3))))))
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381450865137906775752704⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.reuse 0) (.run (.split 11 0 (.split 16 0 (.split 4 0 (.split 10 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 25 0 (.step 7 (.step 28 (.step 3 (.step 7 (.close 9))))) (.step 28 (.close 7))) (.step 28 (.close 7))) (.step 4 (.step 7 (.step 9 (.step 10 (.close 16)))))) (.step 4 (.step 7 (.step 9 (.step 10 (.close 16)))))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 7 (.step 3 (.close 9))) (.step 29 (.step 7 (.close 9)))) (.step 29 (.step 15 (.step 7 (.close 9))))) (.step 28 (.close 7))) (.step 7 (.step 26 (.step 7 (.close 9))))) (.step 7 (.step 29 (.step 4 (.step 3 (.step 5 (.close 9)))))))) (.step 7 (.step 9 (.step 10 (.close 15))))) (.step 7 (.step 9 (.close 16)))) (.step 7 (.step 38 (.step 4 (.step 3 (.step 5 (.close 9))))))) (.step 7 (.split 25 0 (.split 38 0 (.split 34 0 (.step 4 (.step 3 (.close 7))) (.step 7 (.step 4 (.close 9)))) (.step 3 (.step 4 (.step 7 (.step 9 (.close 10)))))) (.step 4 (.step 7 (.step 9 (.close 15)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519577465890670244234573551889561182190577532634175187359381450866263806682595328⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.reuse 0) (.run (.split 6 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.split 26 0 (.split 10 0 (.split 12 0 (.step 7 (.step 5 (.step 7 (.step 3 (.close 4))))) (.step 4 (.step 43 (.step 3 (.close 9))))) (.step 7 (.close 3))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 3))) (.step 4 (.close 7))) (.step 7 (.close 4))) (.step 7 (.close 4))) (.step 7 (.step 4 (.step 7 (.close 4))))) (.step 7 (.split 25 0 (.split 38 0 (.split 43 0 (.split 11 0 (.step 48 (.close 7)) (.step 4 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.close 9))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case197
