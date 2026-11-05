module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case25
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342787806629724160⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593776385211095628519, 5789234131004114112605793609176917365993675384684502996126192153037828881438993460943296163574515770240361043816409628266588608613860165826510106852596731451962902910272861366847979792412103177558715516249647994149244240896, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284971109347745694313144495698113784064867572264212253099242730040848167805142015991150995061630097967242230628352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.step 3 (.step 17 (.close 29))))) (.step 7 (.step 3 (.close 19)))) (.step 7 (.step 3 (.close 19)))) (.step 11 (.step 3 (.step 7 (.step 3 (.step 11 (.step 3 (.close 29)))))))) (.step 29 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 11 (.step 3 (.step 17 (.step 3 (.close 19)))))))) (.step 69 (.step 3 (.close 11)))))) (.step 3 (.step 7 (.close 3)))) (.step 3 (.step 74 (.close 3)))) (.step 3 (.step 67 (.step 3 (.step 11 (.step 3 (.close 17))))))) (.step 66 (.step 3 (.step 66 (.step 3 (.step 11 (.step 3 (.close 19)))))))) (.step 3 (.step 55 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51)))))) (.step 3 (.step 55 (.split 51 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 7 (.close 3))))))) (.step 7 (.split 63 1 (.split 65 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 71 1 (.step 7 (.step 29 (.step 3 (.step 7 (.close 37))))) (.step 29 (.step 3 (.step 39 (.step 3 (.close 37)))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 17 (.step 37 (.close 39)))))))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.step 29 (.step 15 (.step 39 (.step 15 (.step 45 (.close 67)))))))) (.step 29 (.step 66 (.close 3)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460183827084136443896789531468703981888743326150587394561069408539401090006688079266830647035846070949117952⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 17 (.step 37 (.close 39)))))))) (.step 29 (.step 51 (.step 67 (.close 3))))) (.step 3 (.step 29 (.step 15 (.close 39))))) (.step 29 (.step 51 (.step 66 (.close 3))))) (.step 39 (.split 65 1 (.split 71 1 (.step 45 (.step 29 (.step 37 (.step 39 (.step 3 (.step 39 (.close 11))))))) (.step 29 (.step 39 (.step 11 (.step 37 (.step 11 (.close 66))))))) (.step 3 (.step 29 (.close 39))))))))) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 11 (.step 3 (.step 17 (.step 3 (.close 19)))))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 15 (.close 29)))) (.step 3 (.step 29 (.step 67 (.close 3))))) (.step 29 (.step 3 (.close 66))))) (.step 3 (.step 40 (.step 9 (.step 29 (.step 38 (.close 3))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065245470636601467136205462790262072702194438304434699708782157327676676048739631104⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.step 66 (.split 65 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 71 1 (.step 7 (.step 29 (.step 3 (.step 7 (.close 37))))) (.step 29 (.step 3 (.step 37 (.close 3))))) (.step 3 (.step 7 (.step 29 (.step 11 (.close 37)))))) (.step 3 (.step 7 (.step 11 (.step 17 (.step 29 (.close 37))))))) (.step 29 (.step 66 (.step 67 (.close 3))))) (.step 3 (.step 15 (.step 29 (.close 37)))))) (.step 37 (.split 63 1 (.step 45 (.step 29 (.step 39 (.step 66 (.step 3 (.step 37 (.step 3 (.step 37 (.close 11))))))))) (.step 15 (.step 29 (.step 37 (.step 11 (.close 66)))))))) (.step 37 (.split 63 1 (.step 39 (.step 3 (.step 29 (.step 37 (.close 11))))) (.step 15 (.step 29 (.step 37 (.step 11 (.close 66)))))))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 38 (.step 3 (.close 7)))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622937198875408533562916267060128315057806582727789510656⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.step 3 (.step 11 (.close 19)))) (.step 3 (.close 7))) (.step 3 (.step 15 (.close 29)))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 3 (.step 19 (.close 67)))))))) (.step 29 (.step 3 (.step 11 (.step 23 (.step 19 (.step 20 (.close 66)))))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 7 (.step 3 (.close 29)))))))) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.step 19 (.close 20))) (.step 25 (.step 3 (.step 7 (.close 19))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 67 (.close 3)))) (.step 3 (.step 11 (.step 19 (.step 20 (.step 19 (.close 67))))))) (.step 11 (.step 66 (.close 3)))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20)))))))))) (.step 3 (.step 29 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 19 (.step 20 (.step 19 (.close 67)))))))))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914586797738407425837081849247901730058646061056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 17 1 (.split 22 1 (.step 67 (.split 26 1 (.split 35 1 (.split 65 1 (.split 63 1 (.split 72 1 (.split 8 0 (.split 17 0 (.step 7 (.close 19)) (.step 19 (.step 7 (.close 19)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.step 25 (.close 29)))))))) (.step 11 (.step 66 (.close 3)))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 38 (.close 19))))))) (.step 3 (.step 29 (.step 11 (.step 23 (.step 29 (.step 3 (.step 19 (.step 20 (.close 66))))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 64 1 (.step 25 (.step 11 (.step 20 (.step 66 (.step 3 (.step 19 (.close 3))))))) (.step 11 (.step 19 (.step 29 (.close 66))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.close 66))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 64 1 (.step 20 (.step 3 (.step 11 (.step 19 (.step 20 (.close 29)))))) (.step 11 (.step 19 (.step 29 (.close 66))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.close 66)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982334001028195230293770581240184832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 77 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 11 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 17 (.step 3 (.close 29)))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 11 (.close 67)))) (.step 11 (.step 3 (.step 66 (.close 3)))))) (.step 3 (.step 23 (.step 11 (.step 17 (.close 3)))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 7 (.step 23 (.step 11 (.step 17 (.step 29 (.step 66 (.step 7 (.step 37 (.step 39 (.close 67)))))))))))) (.step 3 (.step 7 (.step 29 (.step 23 (.step 11 (.step 17 (.step 66 (.step 7 (.step 37 (.step 39 (.close 67)))))))))))) (.step 3 (.step 29 (.step 38 (.step 11 (.step 17 (.step 23 (.step 66 (.step 67 (.step 3 (.step 17 (.step 3 (.close 37))))))))))))) (.step 3 (.step 7 (.step 17 (.step 3 (.step 29 (.step 38 (.step 40 (.step 66 (.step 7 (.step 37 (.step 11 (.step 17 (.close 37)))))))))))))) (.step 3 (.step 7 (.step 67 (.step 7 (.step 3 (.close 11))))))) (.step 3 (.step 29 (.step 11 (.step 17 (.step 23 (.step 17 (.close 3)))))))) (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17))))))) (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17))))))) (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268678795458523172077943390208⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.step 19 (.close 20))) (.step 20 (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 51 (.close 67)))) (.step 3 (.step 11 (.step 19 (.close 20))))) (.step 11 (.step 51 (.step 66 (.close 3))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20)))))))))) (.step 3 (.step 29 (.step 11 (.step 23 (.step 29 (.step 3 (.step 20 (.step 66 (.step 19 (.step 20 (.close 67)))))))))))) (.step 25 (.split 26 1 (.split 35 1 (.split 65 1 (.split 71 1 (.step 25 (.step 11 (.step 19 (.step 20 (.step 3 (.step 20 (.step 25 (.close 29)))))))) (.step 11 (.step 20 (.step 19 (.step 29 (.step 19 (.step 29 (.close 66)))))))) (.step 3 (.step 11 (.close 20)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.step 25 (.step 29 (.close 38))))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 20 (.close 66)))))))))))) (.reuse 1)) (.reuse 2)) (.run (.step 3 (.step 7 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 66 (.step 7 (.step 3 (.close 29)))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 17 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342786707118096384⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.reuse 0) (.run (.step 11 (.split 10 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 3 (.split 42 1 (.step 11 (.close 3)) (.step 7 (.step 11 (.close 29))))) (.step 9 (.step 11 (.step 3 (.step 29 (.close 37)))))) (.step 11 (.step 3 (.step 29 (.step 37 (.close 39)))))) (.step 3 (.close 7))) (.step 3 (.close 11))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.close 39))))))) (.step 3 (.step 11 (.step 3 (.step 9 (.step 29 (.step 39 (.close 67)))))))) (.step 11 (.step 3 (.step 9 (.step 29 (.close 66)))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 11 (.close 7))))) (.step 3 (.step 9 (.step 29 (.step 38 (.step 11 (.step 37 (.close 38)))))))) (.step 3 (.step 7 (.step 29 (.step 38 (.step 40 (.step 66 (.step 7 (.step 37 (.step 11 (.step 37 (.step 39 (.close 67))))))))))))) (.step 3 (.step 7 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 29 (.close 11))))) (.step 3 (.step 7 (.step 3 (.close 11))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342787806629724160⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 8 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.split 63 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 29 (.close 38)))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.split 63 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.step 11 (.close 17)))))) (.step 3 (.step 11 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case25
