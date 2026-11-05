module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case230
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005536014537700937011843338568940388352⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908127039438376985589, 5783586103091957813513448549065477704101332453097102403927030543402094319394108592887551773511915116652793239902302694320363413592187732277592161523456540874451485486766787986221277724849666005459465451175879706183626392577, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832779953414727673302568996365954487519977731941990400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 58 (.close 3)) (.split 35 0 (.step 58 (.step 3 (.step 5 (.close 8)))) (.split 36 0 (.step 38 (.step 3 (.step 9 (.step 3 (.close 16))))) (.step 37 (.step 38 (.close 3)))))) (.split 34 0 (.step 58 (.step 33 (.step 39 (.step 3 (.close 28))))) (.split 35 0 (.split 36 0 (.step 33 (.step 48 (.close 9))) (.step 37 (.step 33 (.close 3)))) (.step 37 (.step 33 (.close 3)))))) (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 45 (.step 4 (.close 3)))) (.step 33 (.split 34 0 (.split 35 0 (.step 4 (.step 33 (.close 4))) (.step 4 (.step 9 (.close 33)))) (.step 33 (.step 45 (.close 4))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.step 39 (.step 5 (.step 4 (.close 8))))) (.step 33 (.step 39 (.step 4 (.step 33 (.step 3 (.close 4))))))) (.split 30 0 (.step 39 (.split 34 0 (.step 4 (.step 23 (.step 4 (.step 19 (.step 4 (.close 8)))))) (.step 39 (.close 4)))) (.step 33 (.split 34 0 (.step 24 (.step 25 (.step 23 (.step 24 (.close 8))))) (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004205488467701387432032398884577738752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 34 0 (.split 35 0 (.step 4 (.step 13 (.close 4))) (.step 4 (.step 9 (.close 13)))) (.split 35 0 (.step 13 (.step 4 (.step 20 (.step 4 (.close 9))))) (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 13 (.step 5 (.step 8 (.close 14)))))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 25 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.split 38 0 (.step 23 (.step 19 (.step 3 (.close 4)))) (.step 4 (.step 5 (.step 8 (.close 13)))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9))))))) (.step 19 (.step 20 (.step 19 (.step 13 (.step 4 (.close 9)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365004205488467701387432032398884577738752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 58 (.step 39 (.step 28 (.step 3 (.close 13))))) (.split 35 0 (.split 36 0 (.step 16 (.step 9 (.step 5 (.close 13)))) (.step 37 (.step 16 (.close 9)))) (.step 37 (.step 15 (.close 3))))) (.step 33 (.split 57 0 (.step 13 (.step 33 (.step 3 (.close 9)))) (.step 45 (.step 4 (.step 3 (.step 9 (.close 13)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.close 8))) (.step 4 (.step 9 (.close 13)))) (.step 45 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9)))))))) (.split 22 0 (.split 30 0 (.step 39 (.step 13 (.step 4 (.close 8)))) (.step 13 (.step 33 (.step 4 (.step 20 (.step 4 (.close 9))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 25 (.step 4 (.step 13 (.close 4))))) (.step 13 (.step 20 (.step 4 (.close 9))))) (.step 13 (.step 17 (.step 14 (.close 9))))) (.step 13 (.step 33 (.step 23 (.step 17 (.step 4 (.close 9)))))))))) (.reuse 0))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005534716463486303304936205944858083328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 37 (.step 3 (.step 9 (.step 3 (.close 16)))))) (.step 48 (.step 9 (.step 13 (.close 15))))) (.step 37 (.split 36 0 (.step 43 (.step 9 (.step 16 (.close 3)))) (.step 29 (.step 37 (.step 3 (.step 18 (.close 21)))))))) (.step 37 (.split 35 0 (.step 13 (.step 18 (.step 3 (.close 9)))) (.step 29 (.step 37 (.step 18 (.close 33))))))) (.step 43 (.step 37 (.step 4 (.step 3 (.step 5 (.close 16))))))) (.split 22 0 (.step 43 (.step 37 (.step 4 (.step 3 (.step 5 (.close 16)))))) (.step 4 (.step 13 (.step 23 (.step 9 (.step 15 (.step 19 (.close 20))))))))) (.split 17 0 (.split 22 0 (.step 43 (.step 37 (.step 4 (.step 3 (.step 5 (.close 16)))))) (.step 4 (.step 13 (.step 23 (.step 9 (.step 15 (.step 19 (.close 20)))))))) (.step 23 (.step 13 (.step 23 (.close 24)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 37 (.split 35 0 (.step 13 (.step 16 (.close 9))) (.step 29 (.step 37 (.step 15 (.close 3)))))) (.step 13 (.close 3))) (.step 4 (.close 13))) (.step 13 (.step 4 (.close 13)))) (.step 13 (.step 4 (.close 13))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1298074214633706907132625156046848, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005536013270050336783613937072237182976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 43 (.step 3 (.close 8))) (.step 28 (.step 5 (.step 16 (.step 3 (.close 4)))))) (.step 4 (.step 37 (.close 3)))) (.step 37 (.step 58 (.step 3 (.step 8 (.close 13)))))) (.step 4 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.split 35 0 (.split 43 0 (.step 4 (.step 13 (.step 4 (.step 14 (.step 19 (.close 20)))))) (.step 13 (.step 4 (.step 20 (.step 8 (.close 4)))))) (.step 3 (.step 4 (.close 3))))) (.split 17 0 (.split 35 0 (.split 43 0 (.step 4 (.step 13 (.step 4 (.step 14 (.close 19))))) (.step 13 (.step 4 (.step 23 (.step 8 (.step 4 (.close 15))))))) (.step 3 (.step 4 (.close 3)))) (.split 22 0 (.split 34 0 (.step 19 (.step 4 (.step 8 (.step 4 (.step 13 (.close 19)))))) (.step 4 (.step 13 (.step 14 (.close 15))))) (.step 19 (.step 20 (.step 4 (.step 8 (.step 4 (.close 13))))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 43 (.step 37 (.step 4 (.step 3 (.step 5 (.close 15)))))) (.step 3 (.step 4 (.close 13)))) (.step 4 (.step 17 (.close 4)))) (.step 4 (.step 17 (.step 4 (.step 3 (.step 4 (.close 14)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566775890763708859824992825912014103891681060109809979571385239010516626682269424289192307814560517722983211478852042242922832781414916365005536014537700937011843338568940388352⟩
def references : Fin 4 → Box := ![Part0.root, Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 11 0 (.split 12 0 (.split 10 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 48 (.step 20 (.step 4 (.close 9)))) (.split 35 0 (.step 55 (.step 4 (.step 37 (.step 4 (.close 3))))) (.step 4 (.step 37 (.step 33 (.step 4 (.step 9 (.step 3 (.close 4))))))))) (.step 33 (.step 38 (.step 33 (.step 4 (.close 8)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 23 (.step 4 (.step 19 (.step 4 (.close 9))))) (.step 4 (.step 9 (.close 19)))) (.step 45 (.step 4 (.close 20)))) (.step 33 (.step 38 (.step 23 (.step 25 (.close 4))))))) (.split 22 0 (.split 30 0 (.step 39 (.split 34 0 (.step 4 (.step 23 (.step 4 (.step 19 (.close 3))))) (.step 39 (.close 4)))) (.step 33 (.step 38 (.step 20 (.step 23 (.step 19 (.close 4))))))) (.split 34 0 (.step 19 (.step 20 (.step 4 (.close 9)))) (.step 39 (.step 19 (.step 20 (.close 4))))))))) (.reuse 1)) (.reuse 2)) (.split 10 0 (.reuse 3) (.run (.split 12 0 (.split 30 0 (.split 34 0 (.split 16 0 (.split 35 0 (.step 13 (.step 4 (.close 8))) (.step 3 (.step 4 (.step 9 (.close 13))))) (.step 13 (.step 4 (.close 13)))) (.split 46 0 (.split 50 0 (.split 53 0 (.step 37 (.close 4)) (.step 4 (.step 8 (.close 13)))) (.step 13 (.close 3))) (.step 3 (.close 13)))) (.step 13 (.close 3))) (.step 3 (.step 4 (.close 13)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case230
