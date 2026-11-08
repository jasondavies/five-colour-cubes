module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case21
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨22571190701410872216439, 5789234131009374248502447883439234072895253849199626685338508381339181628505080547818749522630756644042204098520475869185331332910304952449450745393175339988701253498074825736872568855088801993637825559197145607680347340801, 0⟩]
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
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574900128699496686740740508027395479350886139453758058870603776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.split 36 0 (.split 54 0 (.step 18 (.step 9 (.close 10))) (.step 54 (.step 9 (.close 18)))) (.split 34 0 (.step 18 (.close 9)) (.step 18 (.split 35 0 (.step 18 (.step 10 (.close 13))) (.step 18 (.step 9 (.step 15 (.step 18 (.close 16))))))))) (.split 36 0 (.step 18 (.step 54 (.step 18 (.close 13)))) (.step 54 (.step 18 (.step 9 (.close 13)))))) (.split 30 0 (.split 34 0 (.step 71 (.step 9 (.step 21 (.step 7 (.step 13 (.close 22)))))) (.step 71 (.step 7 (.step 16 (.close 21))))) (.step 7 (.step 9 (.close 13))))) (.split 26 0 (.split 34 0 (.step 70 (.split 36 0 (.step 26 (.step 9 (.step 13 (.close 18)))) (.step 18 (.step 22 (.step 9 (.close 18)))))) (.step 18 (.split 35 0 (.step 70 (.step 16 (.step 10 (.step 15 (.close 18))))) (.step 15 (.step 18 (.step 16 (.step 18 (.step 21 (.close 18))))))))) (.split 34 0 (.step 18 (.step 26 (.step 9 (.step 7 (.close 13))))) (.step 15 (.step 28 (.step 7 (.step 9 (.step 7 (.close 16))))))))) (.split 23 0 (.split 30 0 (.split 26 0 (.step 70 (.step 18 (.close 39))) (.step 7 (.close 4))) (.step 7 (.step 70 (.step 18 (.step 9 (.close 13)))))) (.split 26 0 (.step 18 (.step 26 (.step 4 (.step 18 (.step 28 (.close 9)))))) (.step 7 (.step 18 (.close 22)))))))
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
def root : Box := ⟨1532495540865888858358347027150309183618739123257344000, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507426074276820325333098308417799348661358297062834176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 56 0 (.step 9 (.step 21 (.step 13 (.close 18)))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 9 (.close 21)))) (.step 18 (.step 21 (.step 18 (.step 9 (.close 21)))))) (.step 18 (.close 21))) (.split 35 0 (.step 18 (.split 36 0 (.step 21 (.step 18 (.step 9 (.step 15 (.close 16))))) (.step 18 (.step 15 (.step 16 (.step 18 (.close 21))))))) (.step 15 (.step 29 (.step 21 (.close 18)))))) (.split 34 0 (.split 35 0 (.step 18 (.split 42 0 (.step 21 (.step 9 (.step 7 (.step 13 (.close 22))))) (.step 18 (.step 21 (.close 7))))) (.step 9 (.step 21 (.close 7)))) (.step 15 (.step 28 (.step 7 (.step 9 (.step 18 (.step 21 (.close 7))))))))) (.step 26 (.split 26 0 (.step 18 (.step 55 (.step 4 (.close 13)))) (.step 7 (.step 18 (.close 21)))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 34 0 (.step 54 (.split 42 0 (.step 54 (.step 10 (.step 4 (.step 18 (.close 21))))) (.step 18 (.step 21 (.step 9 (.close 18)))))) (.step 18 (.step 21 (.step 22 (.step 9 (.close 13)))))) (.step 10 (.step 21 (.step 4 (.close 18))))) (.step 22 (.step 9 (.step 18 (.close 21))))) (.split 38 0 (.step 9 (.step 22 (.step 21 (.close 7)))) (.step 21 (.step 4 (.close 7)))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508922651953447169921338881686500822473485971986841600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 26 0 (.step 54 (.step 18 (.step 39 (.step 4 (.step 5 (.close 13)))))) (.step 7 (.close 4))) (.step 7 (.step 54 (.step 18 (.step 10 (.close 13)))))) (.step 22 (.step 18 (.step 70 (.step 5 (.step 7 (.step 9 (.close 18)))))))) (.step 7 (.split 23 0 (.step 54 (.step 70 (.split 35 0 (.step 54 (.step 18 (.step 10 (.close 13)))) (.step 18 (.step 4 (.step 9 (.close 17))))))) (.step 18 (.step 23 (.step 18 (.close 20))))))) (.split 22 0 (.step 22 (.step 18 (.step 22 (.step 7 (.step 18 (.step 28 (.close 9))))))) (.step 7 (.step 18 (.step 23 (.step 18 (.close 20))))))) (.split 19 0 (.split 22 0 (.step 22 (.split 23 0 (.step 18 (.split 26 0 (.step 18 (.step 54 (.close 4))) (.step 7 (.close 4)))) (.step 18 (.step 22 (.step 9 (.close 18)))))) (.step 7 (.step 18 (.step 23 (.step 18 (.step 19 (.close 4))))))) (.step 18 (.close 22)))))
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507427535778457656236016512102632064944377952995377152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 26 0 (.split 36 0 (.step 18 (.step 54 (.step 18 (.close 13)))) (.step 54 (.step 18 (.step 9 (.close 13))))) (.step 7 (.close 4))) (.step 7 (.step 53 (.step 33 (.step 5 (.step 10 (.close 4))))))) (.split 26 0 (.step 18 (.step 55 (.step 4 (.close 13)))) (.step 7 (.step 18 (.close 21))))) (.step 7 (.split 23 0 (.step 70 (.split 35 0 (.step 70 (.step 24 (.step 13 (.step 10 (.step 4 (.close 14)))))) (.step 18 (.step 24 (.step 18 (.step 4 (.step 9 (.close 17)))))))) (.step 18 (.step 23 (.step 18 (.close 20))))))) (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 54 (.close 4))) (.step 7 (.step 18 (.close 21)))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 7 (.step 18 (.step 23 (.step 18 (.close 20))))))) (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 55 (.step 4 (.close 13)))) (.step 7 (.step 18 (.close 21)))) (.step 18 (.close 21))) (.step 7 (.step 18 (.step 23 (.step 18 (.step 19 (.close 4))))))) (.step 18 (.close 21)))))
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
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084500824257085371333538756505627919384576⟩
def references : Fin 4 → Box := ![Part0.root, Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 4 := (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 22 (.step 54 (.step 9 (.close 18)))) (.step 18 (.step 21 (.step 22 (.step 9 (.close 13)))))) (.split 35 0 (.step 18 (.step 22 (.split 36 0 (.step 9 (.step 15 (.step 16 (.close 18)))) (.step 18 (.step 15 (.step 16 (.close 18))))))) (.step 15 (.step 29 (.step 21 (.step 22 (.step 16 (.close 18)))))))) (.split 34 0 (.split 35 0 (.step 18 (.step 22 (.step 9 (.step 7 (.step 13 (.close 26)))))) (.step 9 (.step 21 (.step 22 (.close 7))))) (.step 15 (.step 28 (.step 7 (.step 9 (.step 18 (.step 22 (.step 7 (.close 16)))))))))) (.step 26 (.split 26 0 (.step 18 (.step 54 (.close 4))) (.step 7 (.step 18 (.close 22)))))))) (.reuse 1)) (.reuse 2)) (.split 17 0 (.reuse 3) (.run (.split 26 0 (.split 35 0 (.split 18 0 (.split 19 0 (.split 36 0 (.split 43 0 (.split 49 0 (.split 22 0 (.step 18 (.step 23 (.close 5))) (.step 23 (.close 19))) (.step 13 (.step 24 (.close 18)))) (.step 54 (.split 38 0 (.split 49 0 (.step 23 (.close 4)) (.step 13 (.step 23 (.step 24 (.close 4))))) (.step 18 (.step 23 (.close 5)))))) (.step 54 (.close 4))) (.step 24 (.step 18 (.close 20)))) (.split 38 0 (.split 49 0 (.step 24 (.step 18 (.close 10))) (.step 18 (.step 19 (.close 9)))) (.step 18 (.step 10 (.close 19))))) (.split 18 0 (.split 19 0 (.step 24 (.step 18 (.step 33 (.step 18 (.step 4 (.step 9 (.step 17 (.close 19)))))))) (.step 18 (.step 9 (.close 19)))) (.step 18 (.step 9 (.close 19))))) (.step 7 (.close 18))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574900128699496686740741869156863163104739992952187785943449600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 18 (.close 9))) (.split 42 0 (.step 18 (.step 10 (.step 15 (.close 16)))) (.step 18 (.step 10 (.step 16 (.step 18 (.close 15))))))) (.step 52 (.step 10 (.close 16)))) (.step 18 (.step 65 (.step 13 (.step 16 (.step 10 (.close 18))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 10 (.step 15 (.step 16 (.step 7 (.close 18))))) (.step 18 (.step 15 (.step 7 (.close 16))))) (.step 15 (.step 21 (.step 7 (.step 9 (.step 7 (.close 16))))))) (.split 49 0 (.step 28 (.step 18 (.close 15))) (.step 15 (.step 16 (.close 7))))) (.step 18 (.close 16)))) (.split 26 0 (.split 34 0 (.split 30 0 (.split 42 0 (.split 36 0 (.step 10 (.step 15 (.step 16 (.step 18 (.step 21 (.close 18)))))) (.step 22 (.step 9 (.step 15 (.step 16 (.close 18)))))) (.step 26 (.close 10))) (.step 18 (.step 9 (.step 15 (.close 16))))) (.step 16 (.step 9 (.close 18)))) (.step 10 (.step 15 (.step 26 (.step 7 (.step 16 (.close 7)))))))) (.split 23 0 (.split 26 0 (.step 18 (.step 70 (.split 30 0 (.step 16 (.step 5 (.close 10))) (.step 13 (.step 18 (.step 10 (.close 16))))))) (.step 7 (.step 18 (.close 16)))) (.step 18 (.step 26 (.step 10 (.close 13)))))))
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
def root : Box := ⟨1361129467683753853853498429728146587648, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508922651953448531050806565440354675971915699059687424⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 54 (.step 72 (.split 22 0 (.step 22 (.step 9 (.step 13 (.step 16 (.close 18))))) (.step 5 (.step 4 (.step 10 (.close 13))))))) (.step 15 (.step 18 (.step 21 (.step 18 (.step 9 (.close 16))))))) (.step 16 (.step 4 (.step 9 (.close 18))))) (.step 10 (.step 15 (.step 22 (.step 7 (.step 16 (.close 7))))))) (.step 22 (.step 26 (.step 9 (.step 7 (.step 13 (.close 16))))))))) (.run (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 65 (.step 4 (.step 9 (.step 15 (.step 16 (.close 18)))))) (.step 18 (.step 22 (.step 10 (.step 15 (.step 16 (.close 18))))))) (.step 15 (.step 18 (.close 21)))) (.step 16 (.step 4 (.step 9 (.close 18))))) (.step 10 (.step 15 (.step 63 (.step 21 (.step 7 (.close 16))))))) (.step 26 (.step 10 (.step 16 (.step 18 (.step 15 (.step 18 (.close 21)))))))) (.step 22 (.step 21 (.step 10 (.step 15 (.step 5 (.step 16 (.close 7)))))))))) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 54 (.step 5 (.step 10 (.close 13))))) (.step 7 (.step 18 (.close 16)))) (.step 18 (.step 22 (.step 4 (.close 5))))) (.step 7 (.step 13 (.step 18 (.step 23 (.step 18 (.step 23 (.close 5)))))))) (.step 18 (.close 22))) (.step 18 (.step 22 (.step 5 (.step 4 (.step 10 (.step 4 (.close 16))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574900128699496686740740509356623475135802012357565119150948352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 64 (.step 58 (.close 9))) (.split 36 0 (.step 64 (.step 53 (.step 9 (.step 13 (.step 15 (.close 18)))))) (.step 57 (.step 13 (.step 15 (.step 9 (.close 18))))))) (.step 18 (.step 53 (.step 13 (.step 15 (.step 9 (.close 18))))))) (.split 35 0 (.split 30 0 (.split 36 0 (.step 64 (.step 58 (.step 9 (.step 7 (.step 13 (.close 16)))))) (.step 57 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 13 (.close 15))))) (.step 9 (.step 15 (.step 7 (.step 29 (.close 16))))))) (.split 26 0 (.split 34 0 (.split 30 0 (.step 26 (.step 9 (.step 15 (.step 13 (.close 18))))) (.step 18 (.step 9 (.step 15 (.close 16))))) (.step 15 (.step 10 (.close 18)))) (.step 9 (.step 15 (.step 75 (.step 18 (.step 26 (.step 7 (.close 13))))))))) (.split 23 0 (.split 26 0 (.step 18 (.step 62 (.step 13 (.step 4 (.step 15 (.step 4 (.close 33))))))) (.step 7 (.step 18 (.step 7 (.close 15))))) (.step 18 (.step 26 (.close 7))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507426074276820326662326304202715221565165357343178752⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 54 (.split 42 0 (.step 54 (.step 4 (.step 9 (.step 15 (.step 13 (.close 18)))))) (.step 18 (.step 16 (.step 10 (.step 15 (.close 18))))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 16 (.close 18))))))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 9 (.step 15 (.split 36 0 (.step 18 (.split 35 0 (.step 16 (.step 18 (.close 22))) (.step 21 (.step 7 (.close 16))))) (.step 22 (.close 7)))))) (.step 9 (.step 22 (.step 15 (.step 26 (.close 7)))))))) (.run (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 38 0 (.split 36 0 (.step 53 (.step 4 (.step 9 (.step 15 (.step 13 (.close 18)))))) (.step 18 (.step 9 (.step 15 (.close 16))))) (.step 16 (.step 18 (.close 21)))) (.step 9 (.step 15 (.step 18 (.close 21))))) (.step 15 (.step 4 (.step 10 (.close 18))))) (.step 9 (.step 15 (.split 36 0 (.step 18 (.step 21 (.close 7))) (.step 22 (.step 7 (.step 18 (.step 16 (.step 7 (.close 21)))))))))) (.step 9 (.step 21 (.step 26 (.step 7 (.step 13 (.close 15))))))) (.step 22 (.step 9 (.step 21 (.step 15 (.step 7 (.step 4 (.close 13))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084502153485081156249411660312688199729152⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 54 (.split 30 0 (.step 15 (.step 4 (.close 9))) (.step 13 (.step 18 (.step 9 (.close 15))))))) (.step 7 (.step 18 (.step 7 (.close 15))))) (.step 18 (.step 22 (.step 9 (.step 15 (.step 5 (.close 7))))))) (.step 7 (.step 13 (.step 18 (.step 24 (.step 18 (.step 24 (.close 4)))))))) (.step 18 (.step 22 (.step 7 (.step 9 (.close 13)))))) (.step 18 (.step 22 (.step 9 (.step 15 (.step 18 (.close 21))))))))) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 53 (.step 4 (.step 13 (.step 4 (.close 5)))))) (.step 7 (.step 18 (.step 7 (.close 15))))) (.step 18 (.step 21 (.step 18 (.close 4))))) (.step 7 (.step 13 (.step 18 (.step 24 (.step 18 (.step 24 (.close 4)))))))) (.step 18 (.step 21 (.split 26 0 (.step 18 (.close 4)) (.step 9 (.step 15 (.step 7 (.close 4)))))))) (.step 18 (.step 21 (.step 7 (.step 9 (.close 13)))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 34 0 (.step 18 (.step 24 (.close 4))) (.step 24 (.step 4 (.close 15)))) (.step 13 (.step 4 (.close 17)))) (.step 4 (.step 5 (.step 13 (.step 4 (.step 5 (.step 14 (.close 5)))))))) (.step 4 (.step 18 (.step 13 (.step 19 (.step 9 (.step 15 (.close 20)))))))) (.step 4 (.step 18 (.close 7)))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282952764910103265158742415272574976⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.reuse 0) (.run (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 17 0 (.step 52 (.split 38 0 (.step 13 (.step 4 (.close 9))) (.step 5 (.step 13 (.step 9 (.close 15)))))) (.step 13 (.close 4))) (.step 13 (.step 16 (.close 9)))) (.step 13 (.step 15 (.step 10 (.close 13))))) (.split 35 0 (.step 13 (.step 52 (.close 15))) (.step 15 (.step 4 (.step 10 (.close 13)))))) (.split 34 0 (.split 17 0 (.step 15 (.step 4 (.close 7))) (.step 4 (.step 5 (.step 7 (.close 15))))) (.step 15 (.step 4 (.close 7))))) (.step 26 (.step 15 (.step 4 (.step 10 (.close 13)))))) (.step 22 (.step 15 (.step 4 (.close 9))))) (.split 19 0 (.split 26 0 (.split 23 0 (.split 34 0 (.split 36 0 (.split 35 0 (.split 38 0 (.split 56 0 (.step 4 (.close 15)) (.step 13 (.step 9 (.close 15)))) (.step 13 (.step 10 (.close 15)))) (.step 13 (.step 9 (.close 15)))) (.step 15 (.step 4 (.step 10 (.close 13))))) (.step 15 (.step 4 (.step 10 (.close 13))))) (.step 21 (.step 9 (.step 15 (.step 4 (.close 13)))))) (.step 15 (.close 4))) (.step 21 (.step 15 (.step 4 (.step 9 (.close 13))))))) (.split 17 0 (.split 26 0 (.split 34 0 (.step 21 (.step 13 (.close 4))) (.step 13 (.step 21 (.step 4 (.step 5 (.close 15)))))) (.step 4 (.close 15))) (.step 18 (.step 4 (.step 5 (.close 13))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699507426074276820325333099576068399576890759793766039552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 26 0 (.split 36 0 (.step 18 (.step 52 (.step 18 (.close 10)))) (.step 54 (.step 18 (.step 9 (.close 13))))) (.step 7 (.step 9 (.close 13)))) (.step 7 (.split 36 0 (.split 54 0 (.step 13 (.step 18 (.close 10))) (.step 18 (.step 9 (.close 13)))) (.step 33 (.step 13 (.close 18)))))) (.split 26 0 (.step 18 (.step 70 (.step 9 (.close 13)))) (.step 7 (.step 15 (.step 7 (.step 9 (.step 13 (.close 18)))))))) (.step 7 (.split 23 0 (.step 70 (.split 35 0 (.step 13 (.step 40 (.step 4 (.step 9 (.close 5))))) (.step 18 (.step 13 (.step 33 (.step 4 (.close 9))))))) (.step 18 (.step 13 (.step 18 (.step 15 (.close 10)))))))) (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 54 (.step 10 (.close 13)))) (.step 7 (.step 15 (.step 7 (.step 9 (.step 13 (.close 18))))))) (.step 18 (.step 22 (.step 9 (.step 15 (.close 18)))))) (.step 7 (.step 18 (.step 13 (.step 18 (.step 15 (.close 10)))))))) (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.split 30 0 (.step 18 (.step 9 (.close 21))) (.step 18 (.step 13 (.step 9 (.close 10)))))) (.step 7 (.step 15 (.step 7 (.step 9 (.step 13 (.close 18))))))) (.step 18 (.step 26 (.step 18 (.close 9))))) (.step 7 (.step 18 (.step 13 (.step 18 (.step 15 (.close 10))))))) (.step 18 (.step 22 (.step 21 (.step 9 (.step 7 (.close 13)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084500824258353021933766985907124622589952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 35 0 (.split 38 0 (.split 17 0 (.split 22 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 56 0 (.step 40 (.step 4 (.step 10 (.close 13)))) (.step 18 (.step 10 (.step 13 (.close 16))))) (.step 18 (.step 13 (.step 4 (.step 15 (.close 16)))))) (.step 33 (.step 18 (.step 9 (.close 13))))) (.step 13 (.step 43 (.step 4 (.close 9))))) (.step 13 (.step 23 (.step 15 (.step 9 (.close 20)))))) (.split 22 0 (.step 13 (.step 23 (.step 15 (.step 9 (.close 20))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.step 70 (.step 13 (.close 18))) (.step 18 (.step 13 (.step 18 (.close 9))))) (.step 13 (.step 23 (.step 9 (.close 19))))) (.step 13 (.step 23 (.step 19 (.step 9 (.close 20)))))) (.step 13 (.step 23 (.step 15 (.close 17))))))) (.split 49 0 (.split 50 0 (.split 56 0 (.step 33 (.split 18 0 (.step 23 (.step 18 (.step 10 (.close 13)))) (.step 4 (.step 16 (.step 10 (.close 18)))))) (.step 5 (.step 16 (.step 40 (.step 23 (.step 10 (.close 18))))))) (.step 18 (.step 19 (.step 5 (.close 15))))) (.step 18 (.close 13)))) (.split 38 0 (.split 49 0 (.step 33 (.split 18 0 (.step 24 (.step 18 (.step 4 (.step 9 (.close 15))))) (.step 4 (.step 15 (.step 9 (.close 18)))))) (.step 18 (.close 13))) (.step 4 (.step 5 (.step 13 (.step 18 (.step 14 (.close 19)))))))) (.step 7 (.step 4 (.close 18)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084500824258353021933766985907124622589952⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 26 0 (.split 35 0 (.split 38 0 (.split 19 0 (.split 36 0 (.split 43 0 (.split 49 0 (.split 50 0 (.step 23 (.step 18 (.close 13))) (.step 18 (.step 13 (.step 4 (.step 14 (.close 15)))))) (.step 13 (.close 4))) (.step 54 (.split 22 0 (.step 18 (.step 13 (.close 5))) (.step 13 (.step 18 (.step 10 (.close 14))))))) (.step 54 (.close 4))) (.split 22 0 (.step 18 (.step 13 (.step 4 (.step 15 (.close 10))))) (.step 13 (.close 23)))) (.split 49 0 (.split 50 0 (.split 56 0 (.step 33 (.step 18 (.step 10 (.step 13 (.close 14))))) (.step 5 (.step 16 (.step 10 (.step 18 (.step 13 (.step 19 (.step 20 (.close 33))))))))) (.step 4 (.step 5 (.step 13 (.step 18 (.step 14 (.step 15 (.close 19)))))))) (.step 18 (.close 13)))) (.split 38 0 (.split 49 0 (.step 33 (.step 40 (.step 39 (.step 4 (.step 9 (.step 15 (.close 18))))))) (.step 18 (.close 13))) (.step 4 (.step 5 (.step 13 (.step 4 (.step 5 (.close 14)))))))) (.step 7 (.step 4 (.close 18)))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1329229263435516101133208558057291776, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560703493388143911975780352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 52 (.split 30 0 (.step 15 (.close 10)) (.step 13 (.step 9 (.close 15)))))) (.step 7 (.step 15 (.close 7)))) (.step 15 (.step 10 (.close 13)))) (.step 7 (.step 13 (.step 18 (.step 13 (.close 4)))))) (.step 18 (.step 15 (.step 10 (.step 13 (.close 16)))))) (.step 18 (.step 15 (.step 10 (.close 16))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.step 24 (.step 18 (.close 13))) (.step 4 (.step 13 (.step 4 (.close 9))))) (.step 13 (.close 4))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 13 (.step 4 (.step 9 (.close 15)))))) (.step 4 (.step 18 (.close 7))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 50 0 (.split 17 0 (.step 24 (.step 18 (.close 13))) (.step 13 (.close 4))) (.step 13 (.step 4 (.step 18 (.close 9))))) (.step 13 (.close 4))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 18 (.close 13)))) (.step 4 (.step 18 (.close 7))))) (.split 16 0 (.split 17 0 (.split 18 0 (.step 18 (.step 15 (.step 10 (.close 13)))) (.step 4 (.close 15))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 5 (.close 13))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1267650600228229401497776947200, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560703493388143911975780352⟩
def references : Fin 2 → Box := ![Part13.root, Part14.root]
def proof : Chunks.Proof 2 := (.split 12 0 (.split 13 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 64 (.split 30 0 (.step 16 (.close 9)) (.step 13 (.step 9 (.step 10 (.close 15))))))) (.step 7 (.step 15 (.close 7)))) (.step 15 (.step 10 (.close 13)))) (.step 7 (.step 13 (.step 18 (.step 13 (.close 5)))))) (.step 18 (.step 15 (.step 10 (.step 13 (.close 16)))))) (.step 18 (.step 15 (.step 10 (.close 16))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.step 18 (.step 10 (.close 13)))) (.step 18 (.close 13))) (.step 5 (.step 13 (.step 4 (.step 10 (.close 16)))))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 5 (.close 7))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.step 13 (.split 18 0 (.step 13 (.step 18 (.step 10 (.close 13)))) (.step 4 (.step 13 (.step 10 (.step 13 (.close 14))))))) (.step 18 (.close 13))) (.step 5 (.step 18 (.close 13)))) (.step 4 (.step 5 (.close 13)))) (.step 4 (.step 5 (.close 7))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560703493388143911975780352⟩
def references : Fin 4 → Box := ![Part4.root, Part6.root, Part10.root, Part15.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 12 0 (.split 13 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.step 18 (.step 65 (.step 5 (.step 13 (.step 5 (.close 4)))))) (.step 7 (.step 18 (.close 16)))) (.step 18 (.step 21 (.step 5 (.step 4 (.step 10 (.close 13))))))) (.step 7 (.step 13 (.step 18 (.step 23 (.step 18 (.step 23 (.close 5)))))))) (.step 18 (.step 21 (.step 22 (.step 4 (.close 5)))))) (.step 18 (.step 21 (.step 10 (.close 13))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 49 0 (.split 34 0 (.step 18 (.step 13 (.step 23 (.close 5)))) (.step 13 (.step 23 (.step 4 (.close 16))))) (.step 18 (.close 17))) (.step 5 (.step 18 (.step 13 (.step 19 (.step 10 (.step 16 (.close 20)))))))) (.step 5 (.step 4 (.step 13 (.step 5 (.step 4 (.step 17 (.close 4)))))))) (.step 18 (.step 4 (.close 7)))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part6.excludes
  · exact Part10.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1180591620718485045248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901697974930533410931466974751281267491345634239892290535424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 22 0 (.split 23 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 38 0 (.split 36 0 (.step 46 (.step 9 (.close 7))) (.step 7 (.step 9 (.close 10)))) (.split 42 0 (.step 7 (.close 10)) (.step 7 (.close 9)))) (.split 35 0 (.split 36 0 (.step 7 (.step 9 (.close 10))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 9 (.step 7 (.close 10)))))) (.step 7 (.step 9 (.close 10)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 10 (.close 7)) (.step 9 (.step 7 (.close 10)))) (.split 49 0 (.step 28 (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.split 26 0 (.split 34 0 (.split 30 0 (.split 42 0 (.step 10 (.close 7)) (.step 26 (.close 7))) (.step 7 (.close 9))) (.step 16 (.split 35 0 (.step 7 (.step 10 (.close 7))) (.step 9 (.step 7 (.close 10)))))) (.step 9 (.step 7 (.close 10))))) (.step 7 (.split 23 0 (.split 26 0 (.step 7 (.step 4 (.close 5))) (.step 7 (.close 9))) (.step 26 (.close 7))))) (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 54 (.step 72 (.split 22 0 (.step 10 (.close 7)) (.step 5 (.step 4 (.close 7)))))) (.step 7 (.step 9 (.close 7)))) (.step 16 (.split 35 0 (.step 7 (.step 10 (.close 7))) (.step 9 (.step 4 (.step 7 (.close 10))))))) (.step 9 (.step 10 (.close 4)))) (.step 9 (.step 7 (.close 10))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1361129467683753855034090050445557891072, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085861953724769125188572846556072403533824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 23 0 (.split 38 0 (.split 36 0 (.step 46 (.split 49 0 (.step 7 (.step 4 (.close 9))) (.step 5 (.step 10 (.close 7))))) (.step 7 (.close 10))) (.step 7 (.step 10 (.close 7)))) (.step 10 (.step 4 (.close 7)))) (.split 43 0 (.split 23 0 (.step 7 (.split 38 0 (.split 49 0 (.step 10 (.close 7)) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 10)))))) (.step 10 (.step 5 (.close 7)))) (.step 5 (.step 7 (.step 10 (.close 7)))))) (.step 16 (.step 5 (.close 7)))) (.step 10 (.step 5 (.step 7 (.close 9))))) (.step 10 (.close 9))) (.split 22 0 (.split 23 0 (.step 7 (.split 26 0 (.split 34 0 (.step 22 (.step 7 (.step 4 (.close 5)))) (.step 7 (.close 9))) (.step 5 (.close 10)))) (.step 10 (.step 4 (.step 5 (.close 9))))) (.step 5 (.step 7 (.close 10))))) (.split 17 0 (.split 22 0 (.split 19 0 (.step 7 (.split 26 0 (.split 34 0 (.split 23 0 (.step 7 (.step 4 (.close 5))) (.step 10 (.step 4 (.close 5)))) (.step 7 (.close 9))) (.step 5 (.close 10)))) (.step 10 (.step 4 (.step 5 (.close 9))))) (.step 5 (.step 7 (.close 10)))) (.step 7 (.close 10)))) (.split 19 0 (.split 16 0 (.split 23 0 (.split 30 0 (.split 26 0 (.step 16 (.step 10 (.step 4 (.close 7)))) (.step 10 (.close 4))) (.step 7 (.step 10 (.close 7)))) (.step 10 (.step 9 (.close 7)))) (.step 18 (.step 10 (.step 4 (.step 5 (.close 9)))))) (.step 10 (.step 9 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1180591620718485045248, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085861953724769125188572846556072403533824⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 65 (.step 4 (.close 9))) (.step 7 (.step 10 (.close 7)))) (.step 7 (.step 9 (.close 7)))) (.step 16 (.split 35 0 (.step 7 (.step 10 (.close 7))) (.step 9 (.step 4 (.step 7 (.close 10))))))) (.step 9 (.step 10 (.close 4)))) (.step 9 (.step 7 (.close 10)))) (.step 22 (.step 9 (.close 7)))))) (.run (.split 18 0 (.step 7 (.step 22 (.split 23 0 (.split 26 0 (.step 7 (.step 4 (.close 5))) (.step 7 (.close 9))) (.step 22 (.step 4 (.close 5)))))) (.step 18 (.step 22 (.step 5 (.step 4 (.step 7 (.close 9))))))))) (.run (.split 17 0 (.split 18 0 (.step 7 (.split 19 0 (.split 23 0 (.split 26 0 (.step 7 (.step 4 (.close 5))) (.step 7 (.close 9))) (.step 21 (.step 5 (.step 4 (.close 7))))) (.step 21 (.step 22 (.step 4 (.close 5)))))) (.step 18 (.step 21 (.close 7)))) (.step 7 (.close 18))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1329227995784917053495427778765389824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455084502153485081156250592251933405611032576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 17 0 (.step 64 (.step 46 (.step 5 (.step 7 (.close 9))))) (.step 7 (.close 4))) (.step 7 (.step 22 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 7)))) (.split 35 0 (.step 7 (.step 64 (.close 9))) (.step 29 (.step 48 (.step 9 (.step 7 (.close 10))))))) (.split 34 0 (.split 17 0 (.step 9 (.step 4 (.close 7))) (.step 4 (.step 5 (.step 7 (.close 9))))) (.step 28 (.step 7 (.close 9))))) (.step 26 (.step 9 (.step 4 (.close 7))))) (.step 22 (.step 9 (.step 4 (.close 7))))) (.split 19 0 (.split 26 0 (.split 23 0 (.split 34 0 (.split 30 0 (.step 16 (.step 21 (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 9 (.close 7)))) (.step 16 (.step 48 (.step 9 (.step 7 (.close 10)))))) (.step 9 (.step 4 (.close 5)))) (.step 9 (.close 4))) (.step 9 (.step 10 (.close 4))))) (.split 17 0 (.split 26 0 (.split 34 0 (.step 21 (.step 7 (.close 4))) (.step 18 (.step 21 (.step 4 (.step 5 (.close 9)))))) (.step 4 (.close 9))) (.step 18 (.step 4 (.step 5 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1267650601408821022215188250624, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.step 7 (.split 19 0 (.split 23 0 (.split 26 0 (.step 7 (.step 9 (.close 10))) (.step 7 (.close 9))) (.step 16 (.split 26 0 (.step 7 (.close 9)) (.step 7 (.close 9))))) (.step 16 (.split 26 0 (.step 72 (.step 22 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 7))))))) (.step 18 (.split 26 0 (.step 16 (.split 35 0 (.split 36 0 (.step 18 (.close 10)) (.step 7 (.step 9 (.step 7 (.close 10))))) (.step 9 (.close 7)))) (.step 7 (.step 9 (.close 7)))))) (.step 7 (.step 4 (.close 10)))) (.step 7 (.step 4 (.close 10)))) (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.step 7 (.step 16 (.close 7))) (.step 16 (.close 4))) (.step 16 (.step 4 (.step 7 (.close 9))))) (.step 5 (.step 18 (.close 7)))) (.step 5 (.step 18 (.close 7))))) (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.step 18 (.step 16 (.close 7))) (.step 4 (.step 9 (.close 7)))) (.step 4 (.step 5 (.close 7)))) (.step 4 (.step 5 (.close 7)))) (.step 5 (.step 15 (.close 10))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1073741824, 5653543569684673837562185556777198461960211613615342033889631149562026626581360202261800790553715226882453237351428327678243696286152072712648439851397607588574901699508924113455085863282954032560704673979764629387083776⟩
def references : Fin 4 → Box := ![Part16.root, Part19.root, Part20.root, Part21.root]
def proof : Chunks.Proof 4 := (.split 7 0 (.reuse 0) (.split 10 0 (.split 12 0 (.reuse 1) (.split 13 0 (.reuse 2) (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 54 0 (.step 5 (.step 10 (.close 7))) (.step 16 (.step 4 (.close 7)))) (.step 7 (.step 10 (.close 7)))) (.step 7 (.step 16 (.close 7)))) (.step 21 (.step 15 (.step 4 (.close 7))))) (.step 16 (.step 5 (.close 7)))) (.split 16 0 (.split 17 0 (.step 15 (.step 4 (.step 7 (.close 10)))) (.step 4 (.step 7 (.step 4 (.step 5 (.close 9)))))) (.step 4 (.step 7 (.step 4 (.step 5 (.close 9))))))) (.step 16 (.step 5 (.step 7 (.close 9))))) (.step 16 (.step 9 (.close 4)))) (.step 16 (.step 9 (.close 4))))))) (.reuse 3)))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part22.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case21

namespace FiveColour.Packed.EnumerationChunks.Projected.Case21
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 265 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 265 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 265 0).upper i := by decide +kernel
lemma budget_model : (⟨22571190701410872216439, 5789234131009374248502447883439234072895253849199626685338508381339181628505080547818749522630756644042204098520475869185331332910304952449450745393175339988701253498074825736872568855088801993637825559197145607680347340801, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 265), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨22571190701410872216439, 5789234131009374248502447883439234072895253849199626685338508381339181628505080547818749522630756644042204098520475869185331332910304952449450745393175339988701253498074825736872568855088801993637825559197145607680347340801, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 265) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 265 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 265 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 265) (Archive.root 265) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 265 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 265 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case21

namespace FiveColour.Packed.EnumerationChunks.Case21
def root : Box := Archive.root 265
def families : Fin 78 → List Cut := Enumeration.families 265
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case21.original_covered points
end FiveColour.Packed.EnumerationChunks.Case21
