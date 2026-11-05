module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case264
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641797180371812443276444673⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨21538636103459468986140, 5521043902401074386362392456757739655324866357227326980489905586346335907600418523628357544714134311863337951056905395996126579243889540305263442953960819436615573256560637215511283362977896775063387268244380479127553, 0⟩]
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
def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472491382203178564488389654144423496821479356109174671723725825⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 1 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.step 31 (.step 40 (.step 13 (.step 16 (.close 33))))) (.step 4 (.step 19 (.close 13)))) (.split 34 0 (.step 40 (.step 4 (.close 21))) (.step 4 (.step 14 (.step 16 (.close 19)))))) (.step 4 (.split 27 0 (.step 4 (.step 63 (.close 15))) (.step 4 (.close 19))))) (.split 26 0 (.step 28 (.split 32 0 (.split 35 0 (.split 62 0 (.step 31 (.step 23 (.step 4 (.close 13)))) (.step 41 (.step 23 (.step 31 (.step 4 (.close 13)))))) (.step 4 (.step 38 (.step 18 (.close 13))))) (.step 41 (.step 4 (.step 13 (.step 14 (.close 16))))))) (.step 4 (.close 28)))) (.step 4 (.step 40 (.step 28 (.close 35))))) (.split 26 0 (.split 27 0 (.split 25 0 (.split 32 0 (.step 31 (.step 18 (.step 31 (.close 4)))) (.step 4 (.step 19 (.step 13 (.step 14 (.close 16)))))) (.step 58 (.split 32 0 (.split 35 0 (.split 62 0 (.step 31 (.close 4)) (.step 41 (.step 18 (.step 24 (.step 31 (.close 4)))))) (.step 4 (.step 18 (.step 16 (.close 21))))) (.step 4 (.step 23 (.close 21)))))) (.step 4 (.step 28 (.step 23 (.close 21))))) (.step 4 (.step 28 (.step 18 (.step 16 (.close 21))))))) (.step 4 (.step 23 (.step 21 (.close 6))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1361129467683753853853498429727072845825, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641409826986824881972522333421832716540675592597343974024535447962625⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 25 0 (.split 1 0 (.split 32 0 (.split 35 0 (.split 53 0 (.step 37 (.step 71 (.step 16 (.step 4 (.close 13))))) (.step 23 (.step 40 (.step 16 (.step 4 (.close 13)))))) (.step 4 (.step 37 (.step 4 (.step 18 (.close 33)))))) (.step 40 (.step 41 (.step 4 (.step 13 (.close 16)))))) (.step 4 (.step 16 (.step 4 (.close 14))))) (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 62 0 (.step 71 (.split 53 0 (.step 16 (.step 4 (.close 12))) (.step 4 (.step 13 (.close 16))))) (.step 16 (.step 4 (.step 40 (.step 41 (.step 4 (.step 12 (.close 18)))))))) (.step 4 (.step 37 (.step 4 (.step 18 (.close 33)))))) (.step 40 (.step 41 (.step 4 (.step 13 (.close 16)))))) (.step 28 (.close 4))) (.step 4 (.step 28 (.close 4))))) (.split 25 0 (.split 1 0 (.step 16 (.split 42 0 (.split 57 0 (.step 40 (.step 43 (.step 4 (.step 13 (.close 18))))) (.step 23 (.step 24 (.step 26 (.step 4 (.close 12)))))) (.step 18 (.step 26 (.step 18 (.step 14 (.close 19))))))) (.step 4 (.step 12 (.close 16)))) (.split 27 0 (.split 26 0 (.split 32 0 (.split 35 0 (.step 16 (.step 58 (.split 37 0 (.step 48 (.step 43 (.step 18 (.step 4 (.close 13))))) (.step 4 (.step 14 (.step 19 (.close 20))))))) (.step 4 (.step 16 (.step 15 (.step 18 (.close 21)))))) (.step 4 (.step 16 (.step 21 (.step 13 (.close 20)))))) (.step 18 (.step 28 (.close 4)))) (.step 4 (.step 16 (.step 4 (.step 24 (.close 7)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492951478612411158581974221246982491937235196465514805199873⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 13 0 (.split 19 0 (.reuse 0) (.run (.split 21 0 (.split 23 0 (.split 26 0 (.step 59 (.split 27 0 (.step 31 (.step 18 (.step 31 (.close 4)))) (.step 4 (.step 23 (.close 7))))) (.step 4 (.step 28 (.step 18 (.step 16 (.close 21)))))) (.split 26 0 (.split 27 0 (.step 59 (.split 25 0 (.step 71 (.step 26 (.step 4 (.close 12)))) (.step 18 (.step 59 (.step 31 (.close 4)))))) (.step 4 (.step 18 (.step 6 (.step 12 (.close 21)))))) (.step 18 (.step 71 (.step 59 (.step 4 (.step 18 (.step 6 (.step 16 (.close 21)))))))))) (.step 4 (.step 18 (.step 24 (.step 43 (.step 4 (.close 7))))))))) (.split 19 0 (.split 21 0 (.reuse 1) (.run (.step 4 (.step 23 (.split 32 0 (.step 49 (.step 4 (.step 23 (.close 6)))) (.step 4 (.step 14 (.step 16 (.step 21 (.step 6 (.step 7 (.close 18)))))))))))) (.run (.split 21 0 (.split 25 0 (.split 23 0 (.split 34 0 (.split 36 0 (.step 4 (.step 16 (.step 72 (.split 26 0 (.step 40 (.step 24 (.step 4 (.step 12 (.close 18))))) (.step 4 (.step 12 (.close 18))))))) (.step 18 (.step 16 (.step 22 (.step 18 (.step 14 (.close 19))))))) (.step 16 (.close 4))) (.step 16 (.step 22 (.step 4 (.step 12 (.step 18 (.step 4 (.close 18)))))))) (.step 59 (.step 16 (.step 4 (.step 18 (.step 31 (.step 4 (.close 6)))))))) (.step 4 (.step 16 (.step 18 (.step 4 (.step 12 (.step 21 (.close 6)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1532495540865888858358347027150309183618739122183602177, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472491383735674105354278512502770523971788539727913793907328001⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 32 0 (.step 41 (.step 4 (.step 18 (.step 23 (.step 18 (.step 4 (.close 13))))))) (.step 4 (.step 19 (.close 21)))) (.step 4 (.step 18 (.step 16 (.close 21))))) (.step 41 (.step 4 (.step 58 (.step 28 (.step 31 (.close 4))))))) (.split 26 0 (.split 27 0 (.split 25 0 (.split 32 0 (.step 18 (.step 41 (.step 4 (.step 18 (.step 4 (.close 16)))))) (.step 4 (.step 18 (.close 12)))) (.step 18 (.step 41 (.split 1 0 (.split 32 0 (.step 26 (.step 4 (.close 12))) (.step 4 (.close 18))) (.step 4 (.close 12)))))) (.step 4 (.step 18 (.step 6 (.step 12 (.close 21)))))) (.step 18 (.step 71 (.split 1 0 (.step 18 (.step 6 (.close 21))) (.step 4 (.close 6))))))) (.step 4 (.step 18 (.step 24 (.step 41 (.step 4 (.step 18 (.close 6)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470832579594009642246418815204636988802049⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 18 0 (.reuse 0) (.split 19 0 (.split 13 0 (.reuse 1) (.run (.split 21 0 (.split 25 0 (.split 23 0 (.split 32 0 (.split 34 0 (.split 42 0 (.step 4 (.step 16 (.split 26 0 (.step 40 (.step 41 (.step 4 (.close 12)))) (.step 4 (.step 15 (.close 18)))))) (.step 18 (.step 16 (.step 26 (.close 31))))) (.step 16 (.close 4))) (.step 4 (.step 16 (.step 19 (.step 14 (.close 13)))))) (.step 16 (.step 21 (.step 4 (.step 12 (.step 4 (.close 18))))))) (.step 41 (.split 23 0 (.step 58 (.split 26 0 (.step 16 (.step 4 (.step 24 (.step 28 (.step 18 (.step 4 (.close 13))))))) (.step 4 (.step 6 (.close 7))))) (.step 16 (.step 4 (.step 18 (.step 21 (.step 6 (.step 4 (.close 12)))))))))) (.step 4 (.step 16 (.step 18 (.step 4 (.step 12 (.close 21))))))))) (.run (.split 13 0 (.split 1 0 (.split 21 0 (.split 23 0 (.split 25 0 (.split 26 0 (.step 59 (.step 21 (.step 18 (.close 4)))) (.step 4 (.step 18 (.close 21)))) (.step 18 (.step 41 (.step 59 (.step 6 (.step 4 (.close 12))))))) (.split 25 0 (.step 21 (.step 22 (.step 18 (.step 4 (.close 16))))) (.step 18 (.step 41 (.step 26 (.step 21 (.step 6 (.step 18 (.close 4))))))))) (.step 4 (.step 18 (.step 4 (.step 21 (.close 6)))))) (.step 4 (.step 18 (.step 4 (.close 12))))) (.step 16 (.step 21 (.step 22 (.step 4 (.step 21 (.step 4 (.step 6 (.close 4))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1329227995784915872903807060280344577, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492951478612411158581975550474978276853108100272575085544449⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 26 0 (.step 4 (.split 27 0 (.split 13 0 (.split 25 0 (.step 4 (.step 16 (.close 18))) (.step 58 (.split 32 0 (.step 4 (.step 31 (.close 15))) (.step 4 (.close 14))))) (.step 16 (.step 4 (.step 12 (.close 15))))) (.step 4 (.step 14 (.close 16))))) (.split 45 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 61 0 (.split 62 0 (.split 68 0 (.step 4 (.step 6 (.close 7))) (.step 4 (.step 7 (.close 13)))) (.step 4 (.step 7 (.step 13 (.close 15))))) (.step 4 (.step 7 (.step 13 (.close 15))))) (.step 4 (.step 16 (.step 7 (.step 15 (.close 18)))))) (.step 4 (.step 21 (.step 7 (.step 13 (.close 15)))))) (.step 4 (.step 13 (.step 16 (.close 28))))) (.step 4 (.step 28 (.step 31 (.close 15)))))) (.split 26 0 (.split 35 0 (.step 4 (.step 16 (.step 15 (.close 18)))) (.step 18 (.step 16 (.step 4 (.step 15 (.step 18 (.close 21))))))) (.step 18 (.step 71 (.split 1 0 (.step 16 (.step 18 (.step 6 (.step 15 (.close 21))))) (.step 4 (.step 6 (.close 12)))))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 4 (.step 16 (.step 18 (.step 15 (.step 18 (.close 21)))))) (.step 18 (.step 16 (.step 4 (.step 15 (.step 18 (.step 21 (.close 22)))))))) (.step 16 (.step 18 (.close 15)))) (.step 18 (.step 71 (.split 45 0 (.split 46 0 (.step 31 (.step 16 (.step 71 (.step 6 (.close 15))))) (.step 4 (.step 6 (.step 12 (.step 13 (.close 15)))))) (.step 4 (.step 6 (.step 12 (.step 15 (.step 18 (.step 21 (.close 22)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1180591620717411303425, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641409826986824881972522333420471587072991838744671067215525786420225⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 25 0 (.split 1 0 (.split 32 0 (.split 35 0 (.split 53 0 (.step 71 (.split 26 0 (.step 10 (.step 31 (.step 23 (.close 13)))) (.step 4 (.close 10)))) (.step 23 (.step 40 (.step 55 (.step 4 (.close 13)))))) (.step 4 (.step 41 (.step 4 (.step 10 (.step 18 (.close 13))))))) (.step 40 (.step 41 (.step 4 (.step 10 (.close 13)))))) (.step 4 (.step 30 (.step 4 (.step 13 (.close 35)))))) (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 62 0 (.step 7 (.step 8 (.step 29 (.step 7 (.step 4 (.close 6)))))) (.step 41 (.step 7 (.close 4)))) (.step 4 (.step 7 (.step 41 (.step 4 (.step 6 (.close 7))))))) (.step 40 (.step 8 (.close 4)))) (.step 28 (.close 4))) (.step 4 (.step 28 (.close 4))))) (.split 25 0 (.split 26 0 (.split 42 0 (.split 45 0 (.split 54 0 (.step 40 (.step 43 (.step 18 (.close 13)))) (.step 4 (.close 18))) (.step 4 (.step 18 (.close 16)))) (.step 18 (.step 26 (.step 10 (.step 18 (.step 23 (.close 13))))))) (.step 4 (.close 10))) (.split 26 0 (.split 32 0 (.step 6 (.split 27 0 (.split 35 0 (.split 62 0 (.split 53 0 (.step 6 (.step 7 (.step 4 (.close 6)))) (.step 4 (.step 7 (.close 8)))) (.step 30 (.close 7))) (.step 4 (.step 6 (.close 7)))) (.step 4 (.step 8 (.close 7))))) (.step 4 (.step 8 (.close 7)))) (.step 6 (.step 7 (.step 6 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1180591620717411303425, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492951478612411158580613091779298738084562289656505143657473⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 19 0 (.split 21 0 (.reuse 0) (.run (.step 4 (.step 23 (.split 32 0 (.split 26 0 (.step 4 (.step 8 (.step 10 (.step 23 (.close 12))))) (.step 4 (.close 7))) (.step 4 (.step 8 (.step 10 (.step 21 (.step 18 (.step 13 (.step 14 (.close 16))))))))))))) (.run (.split 21 0 (.split 23 0 (.split 25 0 (.split 34 0 (.split 36 0 (.step 4 (.step 10 (.step 58 (.step 24 (.step 48 (.step 31 (.step 4 (.close 19)))))))) (.step 18 (.step 10 (.step 22 (.step 18 (.step 19 (.close 13))))))) (.step 16 (.step 18 (.step 10 (.step 31 (.step 18 (.close 14))))))) (.step 59 (.step 6 (.step 31 (.step 6 (.step 7 (.step 4 (.close 8)))))))) (.step 10 (.split 42 0 (.split 57 0 (.step 22 (.step 4 (.step 6 (.step 18 (.close 4))))) (.step 6 (.step 18 (.step 22 (.step 4 (.step 23 (.step 18 (.close 4)))))))) (.step 18 (.step 6 (.step 4 (.step 22 (.close 16)))))))) (.step 4 (.step 10 (.step 18 (.step 4 (.step 22 (.step 6 (.step 18 (.close 12)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1361129467683753855034090050444484149249, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492951478612411158581974221246982491938415788086232216503297⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 35 0 (.step 16 (.step 10 (.split 62 0 (.step 4 (.step 55 (.step 4 (.close 6)))) (.step 41 (.step 4 (.step 46 (.step 4 (.step 12 (.close 18))))))))) (.step 37 (.step 4 (.step 10 (.step 4 (.step 29 (.step 18 (.close 33)))))))) (.step 10 (.step 16 (.step 4 (.step 8 (.step 13 (.close 19))))))) (.step 10 (.step 16 (.step 40 (.step 41 (.step 4 (.close 7))))))) (.step 10 (.step 4 (.close 16)))) (.step 10 (.step 16 (.split 42 0 (.split 57 0 (.step 4 (.split 70 0 (.step 58 (.split 32 0 (.step 18 (.step 6 (.close 7))) (.step 4 (.step 7 (.step 8 (.close 13)))))) (.step 4 (.step 19 (.step 8 (.close 7)))))) (.step 24 (.step 26 (.step 23 (.step 18 (.step 4 (.close 8))))))) (.step 18 (.step 26 (.step 18 (.step 23 (.close 7))))))))) (.step 10 (.step 16 (.step 4 (.step 8 (.step 14 (.step 23 (.close 21)))))))) (.step 10 (.step 16 (.split 42 0 (.split 57 0 (.split 70 0 (.split 72 0 (.step 59 (.step 4 (.step 18 (.step 24 (.step 4 (.close 6)))))) (.step 4 (.step 9 (.step 15 (.close 18))))) (.step 4 (.step 24 (.step 6 (.step 7 (.close 12)))))) (.step 26 (.step 24 (.step 48 (.step 43 (.step 6 (.step 12 (.close 18)))))))) (.step 18 (.step 26 (.step 31 (.step 18 (.step 19 (.close 7)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1180591620717411303425, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470832579594009642247599406825354400105473⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 13 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 25 0 (.split 32 0 (.split 34 0 (.split 42 0 (.step 4 (.step 10 (.step 41 (.step 4 (.step 12 (.close 18)))))) (.step 18 (.step 10 (.step 26 (.step 21 (.step 4 (.close 13))))))) (.step 16 (.step 18 (.step 10 (.step 31 (.close 15)))))) (.step 4 (.step 10 (.step 19 (.close 21))))) (.step 41 (.step 6 (.step 58 (.split 26 0 (.step 6 (.step 24 (.step 7 (.step 6 (.step 7 (.close 8)))))) (.step 4 (.step 6 (.close 7)))))))) (.step 10 (.split 42 0 (.step 21 (.step 18 (.step 26 (.step 4 (.step 6 (.step 4 (.close 12))))))) (.step 18 (.step 6 (.step 4 (.close 21))))))) (.step 4 (.step 10 (.step 18 (.step 4 (.step 21 (.step 6 (.close 18)))))))) (.step 10 (.split 25 0 (.step 21 (.step 22 (.step 4 (.step 18 (.step 21 (.step 4 (.close 12))))))) (.step 6 (.step 9 (.step 18 (.close 6))))))))) (.split 18 0 (.reuse 1) (.run (.step 10 (.step 16 (.split 42 0 (.split 57 0 (.split 70 0 (.split 72 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 4 (.step 41 (.step 4 (.close 6)))) (.step 21 (.close 4))) (.step 4 (.step 6 (.step 12 (.close 18))))) (.step 21 (.step 4 (.step 6 (.close 4))))) (.step 18 (.step 26 (.step 4 (.step 9 (.step 15 (.close 18))))))) (.step 26 (.step 4 (.step 21 (.step 6 (.close 7)))))) (.step 26 (.step 24 (.step 41 (.step 4 (.step 6 (.step 4 (.step 12 (.close 18))))))))) (.step 18 (.step 26 (.step 18 (.step 31 (.step 37 (.step 21 (.close 4)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833908822005427163472310632414680450049⟩
def references : Fin 3 → Box := ![Part4.root, Part5.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 7 0 (.split 12 0 (.reuse 0) (.split 18 0 (.reuse 1) (.run (.split 26 0 (.split 34 0 (.split 35 0 (.step 16 (.step 4 (.step 18 (.step 21 (.step 15 (.close 18)))))) (.step 18 (.step 16 (.step 21 (.close 4))))) (.step 16 (.step 18 (.step 31 (.step 15 (.close 18)))))) (.step 18 (.step 71 (.split 45 0 (.split 46 0 (.split 47 0 (.step 16 (.step 31 (.step 21 (.step 38 (.step 15 (.step 4 (.step 6 (.close 7)))))))) (.step 4 (.step 6 (.step 12 (.step 15 (.step 18 (.close 21))))))) (.step 4 (.step 6 (.step 12 (.step 13 (.step 15 (.close 16))))))) (.step 4 (.step 6 (.step 12 (.step 15 (.step 18 (.close 21))))))))))))) (.split 12 0 (.reuse 2) (.run (.split 1 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 32 0 (.split 13 0 (.step 71 (.split 35 0 (.step 16 (.step 4 (.step 29 (.step 15 (.close 18))))) (.step 31 (.step 37 (.step 4 (.step 9 (.step 10 (.close 18)))))))) (.step 10 (.close 16))) (.step 4 (.step 10 (.step 16 (.step 4 (.close 8)))))) (.step 4 (.step 10 (.close 4)))) (.step 10 (.step 16 (.step 26 (.step 4 (.step 7 (.step 15 (.close 18)))))))) (.step 4 (.step 16 (.step 4 (.step 7 (.close 10)))))) (.step 10 (.step 16 (.step 22 (.step 4 (.step 9 (.step 15 (.close 18)))))))) (.step 16 (.step 21 (.split 19 0 (.step 10 (.step 9 (.step 18 (.step 21 (.step 4 (.close 15)))))) (.step 9 (.step 21 (.step 10 (.step 4 (.step 15 (.close 18)))))))))) (.step 4 (.step 31 (.step 6 (.step 4 (.close 10)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1298074214633706907132624082305025, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492951478612411158581974222545056706572122695218856298808321⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 1 0 (.split 7 0 (.split 23 0 (.split 27 0 (.split 32 0 (.split 13 0 (.split 34 0 (.split 36 0 (.split 37 0 (.step 4 (.close 14)) (.step 4 (.step 13 (.close 14)))) (.step 4 (.step 14 (.step 13 (.close 19))))) (.step 4 (.close 14))) (.step 23 (.step 40 (.step 49 (.step 4 (.close 13)))))) (.step 40 (.step 41 (.step 43 (.step 14 (.step 4 (.close 13))))))) (.step 40 (.step 28 (.step 43 (.split 13 0 (.step 37 (.step 40 (.close 14))) (.step 14 (.close 4))))))) (.step 4 (.step 23 (.step 43 (.step 4 (.step 7 (.step 4 (.close 13)))))))) (.split 23 0 (.split 13 0 (.step 40 (.split 26 0 (.split 32 0 (.split 35 0 (.step 16 (.split 27 0 (.step 55 (.step 4 (.step 7 (.close 14)))) (.step 8 (.step 10 (.close 4))))) (.step 4 (.step 8 (.step 10 (.close 14))))) (.step 8 (.step 16 (.step 23 (.step 10 (.step 4 (.close 14))))))) (.step 4 (.step 8 (.close 10))))) (.step 16 (.close 4))) (.step 4 (.step 16 (.step 23 (.step 24 (.step 10 (.step 4 (.step 7 (.close 14)))))))))) (.step 4 (.step 55 (.split 27 0 (.step 4 (.step 7 (.close 8))) (.step 4 (.step 8 (.step 10 (.close 14)))))))) (.step 4 (.step 14 (.step 16 (.step 14 (.step 23 (.step 21 (.close 6)))))))) (.step 4 (.step 59 (.step 23 (.split 7 0 (.step 24 (.step 43 (.step 59 (.step 4 (.step 13 (.close 6)))))) (.step 16 (.step 24 (.step 10 (.step 4 (.step 6 (.step 7 (.close 14)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1329227995784915874056728564887191553, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833908822005427162292871933201875993601⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 21 0 (.split 25 0 (.split 38 0 (.split 45 0 (.split 46 0 (.split 47 0 (.step 10 (.split 57 0 (.split 61 0 (.split 62 0 (.step 71 (.step 4 (.close 15))) (.step 4 (.step 15 (.close 18)))) (.step 4 (.close 15))) (.step 4 (.step 15 (.close 18))))) (.step 48 (.step 10 (.step 4 (.step 15 (.close 18)))))) (.step 16 (.step 24 (.step 16 (.step 6 (.close 4)))))) (.step 48 (.step 10 (.step 4 (.step 15 (.close 18)))))) (.step 48 (.split 18 0 (.split 46 0 (.split 47 0 (.step 48 (.step 10 (.step 18 (.step 15 (.step 4 (.close 18)))))) (.step 4 (.step 10 (.step 15 (.step 18 (.close 21)))))) (.step 4 (.step 13 (.step 15 (.step 6 (.step 12 (.close 13))))))) (.step 10 (.step 16 (.step 18 (.step 21 (.close 4)))))))) (.step 48 (.split 18 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 48 (.step 9 (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 9 (.step 6 (.step 9 (.close 15)))))) (.step 4 (.step 9 (.step 13 (.step 6 (.step 9 (.close 28))))))) (.step 10 (.step 16 (.step 9 (.step 4 (.close 9)))))))) (.step 48 (.step 4 (.step 6 (.close 7))))) (.step 10 (.step 16 (.split 1 0 (.step 16 (.step 9 (.step 12 (.close 15)))) (.step 4 (.step 9 (.close 12))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1152921504606846977, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833908822005427162292871933201875993601⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.step 4 (.step 28 (.split 13 0 (.step 4 (.step 18 (.step 15 (.close 16)))) (.step 58 (.split 32 0 (.step 4 (.step 16 (.step 12 (.close 18)))) (.step 4 (.close 14))))))) (.step 28 (.close 4))) (.split 26 0 (.split 35 0 (.step 4 (.step 18 (.step 26 (.step 16 (.close 9))))) (.step 18 (.step 71 (.step 31 (.step 10 (.step 9 (.step 4 (.step 13 (.step 15 (.close 16)))))))))) (.step 10 (.step 4 (.close 6))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 4 (.step 22 (.step 9 (.close 18)))) (.step 18 (.step 21 (.step 10 (.step 71 (.step 9 (.step 4 (.step 16 (.close 22))))))))) (.step 16 (.step 18 (.step 9 (.step 4 (.step 21 (.close 22))))))) (.step 10 (.step 4 (.close 6))))) (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 4 (.step 21 (.step 9 (.close 18)))) (.step 18 (.step 10 (.step 21 (.step 18 (.step 21 (.step 4 (.step 9 (.close 16))))))))) (.step 18 (.step 21 (.step 4 (.close 9))))) (.step 16 (.step 18 (.step 31 (.step 10 (.step 15 (.step 18 (.close 9)))))))) (.step 10 (.step 4 (.close 6)))))) (.reuse 0))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1152921504606846977, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641797180370686543369602049⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 7 0 (.split 11 0 (.reuse 0) (.run (.split 12 0 (.step 4 (.split 18 0 (.split 19 0 (.step 28 (.step 4 (.close 14))) (.step 4 (.step 6 (.step 9 (.close 15))))) (.step 4 (.step 6 (.step 9 (.close 15)))))) (.step 48 (.split 13 0 (.split 25 0 (.split 38 0 (.split 56 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 15)))) (.step 4 (.step 6 (.close 15)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.step 9 (.close 12))))))))) (.run (.split 1 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 28 (.step 4 (.step 7 (.close 6)))) (.step 10 (.step 4 (.close 6)))) (.step 10 (.step 4 (.close 6)))) (.step 10 (.step 4 (.close 6)))) (.step 4 (.step 10 (.close 9)))) (.step 4 (.step 10 (.close 4)))) (.step 4 (.step 10 (.close 4)))) (.step 10 (.step 4 (.close 6)))) (.step 4 (.step 10 (.close 4)))) (.step 10 (.step 16 (.step 9 (.close 4))))) (.step 4 (.step 16 (.step 63 (.step 4 (.close 8)))))) (.step 4 (.split 12 0 (.step 31 (.step 6 (.close 4))) (.step 4 (.close 6)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1298074214633706908258523989147649, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641795998627270221258294273⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 37 0 (.split 38 0 (.split 42 0 (.split 45 0 (.step 28 (.step 4 (.close 14))) (.step 14 (.step 4 (.close 10)))) (.step 14 (.step 4 (.close 10)))) (.step 28 (.step 14 (.step 4 (.close 16))))) (.split 38 0 (.step 40 (.step 23 (.split 1 0 (.step 14 (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 4 (.step 10 (.step 14 (.step 13 (.step 16 (.close 19)))))))) (.step 28 (.step 4 (.step 14 (.step 16 (.close 19)))))) (.step 14 (.step 4 (.close 7)))) (.step 28 (.step 4 (.close 8)))) (.step 24 (.step 28 (.step 4 (.step 14 (.step 16 (.close 19))))))) (.step 24 (.step 8 (.step 14 (.step 4 (.step 10 (.step 16 (.close 19)))))))) (.step 24 (.split 23 0 (.step 24 (.step 28 (.step 4 (.step 14 (.step 16 (.close 19)))))) (.step 4 (.step 10 (.step 14 (.step 8 (.step 12 (.step 18 (.close 21)))))))))) (.step 24 (.split 19 0 (.split 23 0 (.step 24 (.step 28 (.step 4 (.step 14 (.step 16 (.close 19)))))) (.step 4 (.step 10 (.step 14 (.step 8 (.step 12 (.step 18 (.close 21)))))))) (.step 4 (.step 10 (.step 16 (.step 23 (.step 8 (.step 14 (.close 21)))))))))) (.step 24 (.split 18 0 (.split 19 0 (.split 23 0 (.step 24 (.step 28 (.step 14 (.close 4)))) (.step 4 (.step 10 (.close 14)))) (.step 4 (.step 10 (.step 14 (.close 12))))) (.step 4 (.step 10 (.close 16)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1125899906842625, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641795998627270221258294273⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.run (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 32 0 (.split 13 0 (.step 28 (.step 4 (.close 23))) (.step 23 (.step 28 (.step 40 (.step 49 (.close 4)))))) (.step 40 (.step 28 (.step 41 (.step 4 (.step 13 (.close 16))))))) (.step 28 (.close 4))) (.step 4 (.step 23 (.step 28 (.step 4 (.step 10 (.step 23 (.step 14 (.step 16 (.close 21)))))))))) (.step 4 (.step 10 (.step 23 (.step 8 (.step 21 (.close 12))))))) (.step 4 (.step 23 (.step 24 (.step 43 (.step 28 (.step 4 (.step 16 (.close 18))))))))) (.step 4 (.split 19 0 (.step 23 (.step 24 (.step 41 (.step 28 (.step 4 (.step 10 (.step 23 (.close 12)))))))) (.step 10 (.step 18 (.step 4 (.step 21 (.step 8 (.close 12))))))))) (.step 4 (.split 18 0 (.split 19 0 (.step 43 (.step 28 (.close 4))) (.step 4 (.step 9 (.step 10 (.close 12))))) (.step 4 (.step 9 (.step 10 (.step 12 (.close 15))))))))) (.reuse 0))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1125899906842625, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641797180371812443276444673⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.split 7 0 (.reuse 0) (.run (.split 1 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 54 0 (.split 18 0 (.split 35 0 (.step 28 (.step 10 (.close 4))) (.step 4 (.step 23 (.step 28 (.step 4 (.close 8)))))) (.step 10 (.close 4))) (.step 4 (.step 10 (.close 4)))) (.step 4 (.close 10))) (.step 4 (.step 10 (.close 7)))) (.step 10 (.step 4 (.close 7)))) (.step 4 (.step 10 (.close 4)))) (.step 4 (.close 10))) (.step 4 (.step 10 (.close 4)))) (.step 24 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 24 (.step 8 (.step 4 (.close 7)))) (.step 4 (.step 8 (.close 6)))) (.step 4 (.step 8 (.close 10)))) (.step 10 (.step 4 (.close 7)))) (.step 4 (.close 8))))) (.step 4 (.split 11 0 (.step 23 (.step 6 (.close 8))) (.step 4 (.close 8))))))) (.run (.split 7 0 (.split 11 0 (.split 12 0 (.step 4 (.split 18 0 (.split 19 0 (.step 28 (.step 4 (.close 8))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9))))) (.step 48 (.split 13 0 (.split 25 0 (.split 38 0 (.split 56 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9)))))) (.step 24 (.split 12 0 (.split 13 0 (.split 25 0 (.split 38 0 (.split 56 0 (.step 4 (.step 6 (.step 7 (.close 8)))) (.step 4 (.close 8))) (.step 4 (.close 8))) (.step 4 (.close 8))) (.step 4 (.close 8))) (.step 4 (.step 24 (.close 4)))))) (.step 4 (.step 10 (.close 4))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1, 5653543574944814750668185866479501342491296860785564065134253357073623595727984150162368607673009714926975102533120616287266248613882174090570548807059641411472492953011107952024470833910120079641797180371812443276444673⟩
def references : Fin 4 → Box := ![Part10.root, Part11.root, Part14.root, Part17.root]
def proof : Chunks.Proof 4 := (.split 5 0 (.split 6 0 (.split 11 0 (.reuse 0) (.split 12 0 (.split 18 0 (.reuse 1) (.run (.split 1 0 (.split 7 0 (.step 4 (.split 19 0 (.step 23 (.step 24 (.step 41 (.step 43 (.step 50 (.step 4 (.step 6 (.step 7 (.close 12))))))))) (.step 16 (.step 18 (.step 4 (.step 23 (.step 18 (.step 21 (.close 6))))))))) (.step 16 (.step 4 (.step 43 (.split 19 0 (.step 24 (.step 10 (.step 18 (.step 4 (.step 18 (.step 7 (.close 14))))))) (.step 10 (.step 18 (.step 4 (.step 6 (.step 14 (.close 21))))))))))) (.step 4 (.close 6))))) (.run (.step 4 (.split 18 0 (.split 19 0 (.split 23 0 (.step 43 (.step 4 (.step 13 (.step 4 (.close 6))))) (.step 4 (.step 12 (.step 6 (.close 10))))) (.step 4 (.step 12 (.close 15)))) (.step 4 (.step 16 (.step 4 (.close 15))))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part14.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part18.excludes
end FiveColour.Packed.ProjectedChunks.Case264
