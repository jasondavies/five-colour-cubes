module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case209
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨22571190701410872216439, 5789234131009374248502447883439234072895253849199626685338508381339181628505080547818749522630756644042204098520475869185331332910304952449450745393175339988701253498074825736872568855088801993637825559197145607680347340801, 0⟩]
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
def root : Box := ⟨1532495540865888858358347027150309183618739123257344000, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507426074276820325333098308417799348661358297062834176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 34 0 (.split 19 0 (.split 35 0 (.split 38 0 (.split 56 0 (.split 72 0 (.split 22 0 (.step 9 (.step 18 (.close 21))) (.step 4 (.step 9 (.close 10)))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.close 21))) (.step 21 (.step 22 (.step 9 (.step 4 (.step 13 (.close 18))))))) (.split 35 0 (.step 18 (.step 21 (.split 36 0 (.step 18 (.step 9 (.step 15 (.close 16)))) (.step 18 (.step 15 (.step 16 (.close 18))))))) (.step 15 (.step 29 (.step 21 (.close 18)))))) (.split 34 0 (.split 35 0 (.step 18 (.step 21 (.step 9 (.step 7 (.step 13 (.close 22)))))) (.step 9 (.step 21 (.close 7)))) (.step 15 (.step 28 (.step 7 (.step 9 (.step 18 (.step 21 (.close 7))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508922651953447169921338881686500822473485971986841600⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 18 0 (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 54 (.close 18))) (.step 71 (.step 7 (.close 16)))) (.split 26 0 (.step 70 (.step 18 (.step 26 (.step 9 (.step 13 (.step 15 (.close 16))))))) (.step 18 (.step 26 (.step 7 (.close 9)))))) (.split 23 0 (.step 70 (.step 7 (.step 18 (.step 33 (.step 4 (.close 5)))))) (.step 18 (.close 4)))) (.split 26 0 (.split 34 0 (.step 54 (.split 42 0 (.step 22 (.step 4 (.step 9 (.step 13 (.close 18))))) (.step 18 (.step 9 (.step 18 (.step 21 (.close 18))))))) (.step 18 (.step 22 (.step 9 (.step 15 (.step 16 (.close 18))))))) (.split 34 0 (.step 18 (.step 22 (.step 9 (.step 7 (.close 21))))) (.step 15 (.step 28 (.step 7 (.step 9 (.step 7 (.close 16)))))))))) (.reuse 0)) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 54 (.step 7 (.step 18 (.step 33 (.step 4 (.close 5)))))) (.step 18 (.close 4))) (.step 7 (.step 54 (.step 18 (.step 45 (.step 18 (.step 20 (.step 18 (.step 9 (.close 13)))))))))) (.step 22 (.step 18 (.step 7 (.step 18 (.close 20)))))) (.step 22 (.step 18 (.split 22 0 (.step 18 (.close 4)) (.step 7 (.step 18 (.step 19 (.close 4))))))))))
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
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084500824257085371333538756505627919384576⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 26 0 (.step 18 (.close 39)) (.step 7 (.close 4))) (.step 7 (.step 33 (.close 18)))) (.step 18 (.close 4))) (.step 7 (.step 70 (.step 18 (.step 70 (.step 18 (.step 9 (.close 13)))))))) (.split 22 0 (.step 18 (.step 21 (.close 18))) (.step 7 (.step 18 (.close 20))))) (.split 19 0 (.split 22 0 (.step 18 (.step 21 (.close 7))) (.step 7 (.step 18 (.step 19 (.close 4))))) (.step 18 (.close 21)))) (.split 22 0 (.step 7 (.split 18 0 (.split 19 0 (.step 54 (.step 18 (.step 54 (.step 18 (.step 10 (.close 13)))))) (.step 18 (.close 20))) (.step 18 (.step 19 (.close 4))))) (.split 18 0 (.step 7 (.step 23 (.step 24 (.step 13 (.step 14 (.close 19)))))) (.step 18 (.step 7 (.step 19 (.close 13)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507426074276821686462565992171653202159788024135680000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.step 52 (.step 18 (.step 10 (.step 13 (.close 15))))) (.step 18 (.step 16 (.step 10 (.step 13 (.close 18)))))) (.step 18 (.split 34 0 (.step 71 (.step 9 (.step 15 (.step 16 (.close 7))))) (.step 18 (.step 15 (.close 16)))))) (.split 26 0 (.split 34 0 (.step 70 (.split 36 0 (.step 10 (.step 15 (.step 16 (.close 18)))) (.step 18 (.step 10 (.step 15 (.step 16 (.close 18))))))) (.step 16 (.step 9 (.close 18)))) (.step 10 (.step 15 (.step 26 (.close 7)))))) (.split 23 0 (.step 18 (.step 55 (.step 4 (.close 5)))) (.step 18 (.step 26 (.close 10))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 54 (.step 22 (.step 54 (.step 10 (.step 4 (.step 13 (.step 16 (.close 18)))))))) (.step 15 (.step 18 (.step 21 (.step 9 (.step 16 (.close 18))))))) (.step 16 (.step 4 (.step 9 (.close 18))))) (.step 10 (.step 15 (.step 22 (.step 7 (.step 16 (.close 7)))))))) (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 19 0 (.step 65 (.step 4 (.step 9 (.step 15 (.step 16 (.close 18)))))) (.step 10 (.step 21 (.step 18 (.step 4 (.close 15)))))) (.step 18 (.step 10 (.step 21 (.step 15 (.step 16 (.close 18))))))) (.step 15 (.step 21 (.close 4)))) (.step 16 (.step 5 (.step 9 (.close 18))))) (.step 15 (.split 19 0 (.step 10 (.step 21 (.step 7 (.close 16)))) (.step 9 (.step 21 (.step 22 (.step 5 (.close 7))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901697974930533410931468303979277052406037946426235159576576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.step 64 (.step 18 (.step 9 (.step 13 (.close 15))))) (.step 18 (.step 15 (.step 9 (.step 13 (.close 18)))))) (.split 30 0 (.split 36 0 (.step 15 (.step 9 (.step 7 (.step 13 (.close 16))))) (.step 29 (.step 7 (.close 13)))) (.step 7 (.step 9 (.close 13))))) (.split 26 0 (.split 34 0 (.step 26 (.step 9 (.step 13 (.step 15 (.close 18))))) (.step 15 (.step 10 (.close 18)))) (.step 9 (.step 15 (.step 18 (.step 26 (.close 7))))))) (.split 23 0 (.step 18 (.step 62 (.step 4 (.step 7 (.close 9))))) (.step 18 (.close 26)))) (.split 26 0 (.split 34 0 (.split 38 0 (.step 54 (.split 42 0 (.step 9 (.step 15 (.step 18 (.close 16)))) (.step 18 (.step 9 (.step 15 (.step 16 (.close 18))))))) (.step 16 (.step 18 (.step 21 (.step 9 (.step 15 (.close 18))))))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 9 (.step 15 (.split 42 0 (.step 18 (.step 22 (.step 7 (.close 16)))) (.step 26 (.step 7 (.close 16)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084502153485081156249411660312688199729152⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 18 0 (.reuse 0) (.run (.split 26 0 (.split 34 0 (.split 19 0 (.split 38 0 (.split 42 0 (.step 53 (.step 4 (.step 9 (.step 15 (.step 13 (.close 18)))))) (.step 18 (.step 9 (.step 15 (.step 18 (.close 16)))))) (.step 16 (.step 18 (.close 21)))) (.step 9 (.step 21 (.step 18 (.step 4 (.close 15)))))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 9 (.step 15 (.split 42 0 (.split 59 0 (.step 21 (.close 7)) (.step 26 (.step 16 (.step 7 (.close 18))))) (.step 26 (.step 7 (.step 16 (.step 7 (.close 21))))))))))) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.step 13 (.step 4 (.step 7 (.close 9)))))) (.step 18 (.step 22 (.step 9 (.step 5 (.close 7)))))) (.step 7 (.step 13 (.step 18 (.step 23 (.step 9 (.step 15 (.close 19)))))))) (.step 18 (.step 22 (.step 7 (.close 9))))) (.step 18 (.step 22 (.step 9 (.step 15 (.step 5 (.close 7))))))))) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 53 (.step 4 (.close 7)))) (.step 18 (.step 21 (.step 4 (.step 5 (.step 7 (.close 9))))))) (.step 7 (.step 13 (.step 18 (.step 23 (.step 9 (.step 15 (.close 19)))))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 18 (.step 21 (.step 7 (.close 9))))) (.step 18 (.step 7 (.step 13 (.step 24 (.step 18 (.step 9 (.close 15))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282952764910103265158742415272574976⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.reuse 0) (.run (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 72 0 (.step 52 (.step 4 (.step 9 (.close 15)))) (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 13 (.step 9 (.close 15)))) (.step 13 (.step 9 (.close 15)))) (.step 21 (.step 13 (.step 9 (.close 15))))) (.step 22 (.step 13 (.step 9 (.close 15))))) (.step 21 (.step 15 (.step 4 (.close 10))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 13 (.step 15 (.step 9 (.close 13)))) (.step 16 (.step 4 (.close 9)))) (.step 22 (.step 13 (.close 15)))) (.step 15 (.step 4 (.step 10 (.close 13)))))) (.split 18 0 (.split 34 0 (.split 16 0 (.step 15 (.step 4 (.close 7))) (.step 4 (.step 5 (.close 15)))) (.step 15 (.step 4 (.close 7)))) (.step 15 (.step 4 (.step 9 (.step 7 (.close 13)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508922651953447169921340149337101050702887468690046976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 26 0 (.step 18 (.step 13 (.step 15 (.close 10)))) (.step 7 (.close 9))) (.step 7 (.step 13 (.step 18 (.step 33 (.step 9 (.close 10))))))) (.step 18 (.close 9))) (.step 7 (.step 70 (.step 18 (.step 13 (.step 18 (.step 33 (.close 4)))))))) (.split 22 0 (.step 18 (.split 26 0 (.step 18 (.step 9 (.close 22))) (.step 15 (.step 7 (.step 9 (.step 13 (.close 18))))))) (.step 7 (.step 18 (.step 13 (.close 4)))))) (.split 19 0 (.split 22 0 (.step 18 (.split 26 0 (.step 18 (.step 9 (.close 21))) (.step 15 (.step 7 (.step 9 (.step 13 (.close 18))))))) (.step 7 (.step 18 (.step 13 (.close 4))))) (.step 18 (.step 21 (.step 18 (.close 9)))))) (.step 7 (.split 35 0 (.split 19 0 (.split 36 0 (.split 43 0 (.step 18 (.step 13 (.step 18 (.close 14)))) (.step 54 (.step 13 (.step 10 (.step 4 (.close 9)))))) (.step 54 (.close 4))) (.step 18 (.step 13 (.step 18 (.step 14 (.close 9)))))) (.step 33 (.step 18 (.step 4 (.step 9 (.step 13 (.close 15))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560703493388143911975780352⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 13 0 (.split 16 0 (.reuse 0) (.run (.step 7 (.split 35 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 19 0 (.split 36 0 (.step 18 (.step 13 (.close 18))) (.step 13 (.step 18 (.step 33 (.step 4 (.close 5)))))) (.step 18 (.step 13 (.close 4)))) (.step 18 (.step 13 (.step 5 (.step 10 (.close 16)))))) (.step 13 (.step 23 (.step 9 (.close 15))))) (.step 24 (.step 13 (.step 23 (.close 15))))) (.step 33 (.split 49 0 (.step 24 (.step 18 (.close 9))) (.step 4 (.step 13 (.close 18))))))))) (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 16 (.close 9))) (.step 15 (.step 10 (.close 13)))) (.step 7 (.step 13 (.step 18 (.step 10 (.close 13)))))) (.step 15 (.step 10 (.close 13)))) (.step 15 (.step 10 (.step 13 (.close 16))))) (.step 18 (.step 7 (.close 13)))) (.split 26 0 (.step 13 (.step 18 (.close 13))) (.step 4 (.step 5 (.close 7))))))) (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 15 (.step 7 (.close 10)))) (.step 15 (.step 10 (.close 13)))) (.step 7 (.step 13 (.step 18 (.step 9 (.close 13)))))) (.step 15 (.step 4 (.step 10 (.close 13))))) (.step 15 (.step 4 (.step 10 (.step 13 (.close 16)))))) (.step 18 (.step 7 (.close 13)))) (.split 26 0 (.step 13 (.step 18 (.close 13))) (.step 4 (.step 7 (.close 15))))) (.split 16 0 (.step 18 (.step 15 (.step 10 (.close 13)))) (.step 4 (.step 5 (.close 13)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1180591620718485045248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084500824257085371334719348126345330688000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.split 38 0 (.step 71 (.close 9)) (.step 58 (.close 10))) (.step 7 (.close 9))) (.step 7 (.split 34 0 (.step 10 (.close 7)) (.step 7 (.step 9 (.close 10)))))) (.split 26 0 (.split 34 0 (.step 70 (.step 10 (.close 7))) (.step 7 (.step 16 (.step 10 (.close 7))))) (.step 9 (.close 7)))) (.step 7 (.split 23 0 (.step 7 (.close 4)) (.step 26 (.close 7))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 54 (.step 10 (.close 4))) (.step 7 (.step 9 (.close 7)))) (.step 16 (.split 35 0 (.step 7 (.close 10)) (.step 9 (.step 4 (.close 7)))))) (.step 9 (.step 4 (.close 7))))) (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 19 0 (.step 10 (.close 4)) (.step 9 (.step 7 (.close 10)))) (.step 7 (.step 10 (.close 7)))) (.step 9 (.step 4 (.close 7)))) (.step 16 (.split 35 0 (.split 36 0 (.step 7 (.close 10)) (.step 22 (.step 7 (.close 9)))) (.step 9 (.step 4 (.close 7)))))) (.step 9 (.step 4 (.close 7))))) (.step 7 (.step 22 (.split 18 0 (.split 23 0 (.step 7 (.close 4)) (.step 22 (.step 4 (.close 5)))) (.step 22 (.step 4 (.close 5))))))) (.step 7 (.split 17 0 (.step 7 (.split 18 0 (.split 19 0 (.split 23 0 (.step 7 (.close 4)) (.step 21 (.step 4 (.step 5 (.step 4 (.close 7)))))) (.step 21 (.step 5 (.step 4 (.close 7))))) (.step 21 (.close 7)))) (.step 7 (.close 18))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1329227995784917053495427778765389824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282952764910104445750363132683878400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 17 0 (.step 46 (.step 64 (.step 5 (.close 7)))) (.step 4 (.close 5))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 16 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 7)))) (.split 35 0 (.step 7 (.step 64 (.close 9))) (.step 29 (.step 21 (.step 9 (.step 4 (.close 7))))))) (.split 34 0 (.split 16 0 (.split 30 0 (.split 36 0 (.step 7 (.step 9 (.close 7))) (.step 9 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 28 (.step 7 (.close 9))))) (.step 26 (.step 16 (.step 7 (.step 9 (.close 7)))))) (.step 22 (.step 9 (.step 4 (.close 7))))) (.split 13 0 (.split 19 0 (.split 26 0 (.split 34 0 (.step 21 (.step 9 (.step 4 (.close 7)))) (.step 16 (.step 48 (.step 9 (.close 7))))) (.step 9 (.close 4))) (.step 9 (.step 7 (.close 9)))) (.step 16 (.step 9 (.close 4))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1180591620718485045248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 12 0 (.split 13 0 (.reuse 0) (.run (.split 16 0 (.split 18 0 (.split 19 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 23 0 (.split 17 0 (.split 36 0 (.step 10 (.close 4)) (.step 7 (.step 9 (.close 10)))) (.step 5 (.close 7))) (.step 10 (.step 4 (.close 7)))) (.step 7 (.step 10 (.close 7)))) (.step 16 (.step 5 (.close 7)))) (.step 10 (.step 5 (.close 7)))) (.step 10 (.step 5 (.step 7 (.close 9))))) (.step 10 (.step 9 (.close 7)))) (.split 17 0 (.split 18 0 (.step 7 (.split 26 0 (.split 19 0 (.split 23 0 (.step 7 (.step 4 (.close 5))) (.step 10 (.step 4 (.close 5)))) (.step 10 (.step 4 (.close 5)))) (.step 5 (.close 10)))) (.step 10 (.step 5 (.step 7 (.close 9))))) (.step 5 (.step 7 (.close 10))))))) (.reuse 1)) (.run (.split 12 0 (.split 13 0 (.step 7 (.split 18 0 (.split 19 0 (.split 23 0 (.step 7 (.close 9)) (.step 16 (.step 7 (.close 9)))) (.step 16 (.step 22 (.step 7 (.close 9))))) (.step 16 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.split 16 0 (.split 18 0 (.step 7 (.step 16 (.close 7))) (.step 16 (.step 4 (.step 7 (.close 9))))) (.step 5 (.step 7 (.close 10))))) (.split 13 0 (.split 16 0 (.step 18 (.step 16 (.close 7))) (.step 4 (.step 5 (.close 7)))) (.step 5 (.step 15 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part6.root, Part8.root, Part11.root]
def proof : Chunks.Proof 5 := (.split 7 0 (.split 10 0 (.split 12 0 (.split 13 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 54 (.step 5 (.close 10)))) (.step 18 (.step 22 (.step 4 (.close 5))))) (.step 7 (.step 13 (.step 18 (.step 23 (.close 5)))))) (.step 18 (.close 22))) (.step 18 (.step 22 (.step 4 (.close 5))))))) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.step 55 (.step 4 (.close 5)))) (.step 18 (.step 21 (.step 4 (.step 5 (.step 4 (.close 10))))))) (.step 7 (.step 13 (.step 18 (.step 23 (.close 5)))))) (.step 18 (.step 21 (.step 5 (.step 4 (.step 10 (.close 13))))))) (.step 18 (.step 21 (.close 10)))) (.step 18 (.step 7 (.step 13 (.step 23 (.step 18 (.step 10 (.close 16))))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case209
