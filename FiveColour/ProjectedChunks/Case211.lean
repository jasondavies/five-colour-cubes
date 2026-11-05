module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case211
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519575656639275911169020058592920421442017325290664786725568333187465179014627328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908127039438309876725, 5783586103091957813513448549065477704101332453097102403927030543402094319394105471139001457519683735055563446735996945722220748621036873120632536151717721108831365180663724494250117897918544598836570003200200417898320102401, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519575656639275911169020058592920421442017323960137449075418525147123997948772352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.step 58 (.step 37 (.step 39 (.close 3)))) (.split 30 0 (.split 34 0 (.step 28 (.close 7)) (.step 37 (.step 7 (.close 21)))) (.step 7 (.close 16)))) (.split 26 0 (.step 45 (.step 4 (.close 3))) (.step 4 (.step 7 (.close 16))))) (.step 39 (.split 22 0 (.step 7 (.step 48 (.step 25 (.step 4 (.close 9))))) (.split 26 0 (.step 24 (.split 35 0 (.step 4 (.step 23 (.close 8))) (.step 4 (.close 9)))) (.step 4 (.close 7)))))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 33 (.close 4))) (.step 4 (.step 7 (.close 16)))) (.split 26 0 (.split 34 0 (.step 24 (.split 35 0 (.step 4 (.step 19 (.close 4))) (.step 4 (.close 9)))) (.step 45 (.step 4 (.close 20)))) (.step 4 (.close 7)))) (.split 22 0 (.step 39 (.split 26 0 (.step 24 (.split 35 0 (.step 4 (.step 19 (.close 4))) (.step 4 (.close 9)))) (.step 4 (.close 7)))) (.split 26 0 (.step 19 (.step 20 (.step 4 (.close 9)))) (.step 4 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519575656639275911169020058592920421442017325290663519074968104958063682311421952⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 11 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 48 (.step 13 (.close 4))) (.step 37 (.close 4))) (.step 4 (.step 7 (.step 28 (.close 7))))) (.step 4 (.step 13 (.step 4 (.step 8 (.close 14)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 48 (.step 7 (.step 3 (.step 8 (.close 13))))) (.step 4 (.step 8 (.step 13 (.close 19))))) (.step 4 (.step 13 (.step 4 (.step 8 (.close 19)))))) (.step 4 (.step 13 (.step 14 (.step 4 (.close 15))))))))) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 43 (.step 37 (.step 3 (.step 9 (.step 3 (.close 16)))))) (.step 29 (.step 37 (.close 3)))) (.step 37 (.step 18 (.close 9)))) (.step 29 (.step 7 (.step 3 (.step 15 (.step 3 (.close 16))))))) (.step 37 (.step 4 (.step 37 (.step 7 (.step 4 (.step 9 (.step 4 (.close 3))))))))) (.step 43 (.split 30 0 (.step 48 (.close 7)) (.step 4 (.step 7 (.close 13)))))) (.split 17 0 (.step 43 (.step 38 (.step 3 (.close 4)))) (.step 4 (.step 7 (.step 13 (.step 23 (.step 9 (.step 15 (.close 19))))))))) (.split 16 0 (.split 30 0 (.split 38 0 (.split 34 0 (.step 4 (.step 3 (.step 7 (.close 9)))) (.step 37 (.step 3 (.close 4)))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 13 (.close 15))))))) (.step 4 (.step 17 (.close 4)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560519575656639275911169020058592920421442017325290664786725568333187465179014627328⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 26 0 (.split 30 0 (.step 58 (.step 37 (.step 15 (.step 3 (.close 4))))) (.step 33 (.step 13 (.close 3)))) (.step 7 (.close 15))) (.step 37 (.split 26 0 (.step 13 (.close 3)) (.step 7 (.close 15))))) (.step 7 (.split 12 0 (.split 35 0 (.step 13 (.step 45 (.close 4))) (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 4 (.step 9 (.close 13)))))) (.step 7 (.split 22 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))))))) (.step 7 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 13 (.step 55 (.step 4 (.close 9)))) (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 4 (.step 9 (.close 13)))) (.step 13 (.split 30 0 (.split 34 0 (.step 24 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 17 (.step 8 (.close 14))))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))))) (.split 12 0 (.split 22 0 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 9)))))) (.step 19 (.step 13 (.step 20 (.step 3 (.close 4)))))) (.step 13 (.close 3)))))) (.step 7 (.split 12 0 (.split 35 0 (.step 13 (.close 3)) (.step 3 (.step 4 (.close 13)))) (.step 3 (.step 4 (.close 13))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case211
