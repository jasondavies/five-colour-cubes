module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710573401894947946761161419113437331819700014167130599594458760628482735945262563328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.step 3 (.close 37)))) (.step 7 (.close 19))) (.step 7 (.step 3 (.close 19)))) (.step 11 (.step 3 (.step 7 (.step 3 (.step 11 (.close 29))))))) (.step 29 (.split 71 1 (.step 7 (.step 3 (.close 69))) (.step 69 (.close 74))))) (.step 7 (.close 3))) (.step 3 (.step 74 (.close 3)))) (.step 3 (.step 67 (.step 3 (.close 67))))) (.step 66 (.step 3 (.step 66 (.step 3 (.close 66)))))) (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51)))) (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 9 (.step 3 (.close 11))))) (.step 7 (.split 63 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 71 1 (.step 7 (.step 29 (.step 7 (.close 37)))) (.step 29 (.step 3 (.close 69)))) (.step 7 (.step 29 (.step 37 (.close 39))))) (.step 7 (.step 29 (.close 77)))) (.step 29 (.step 67 (.close 3)))) (.step 66 (.close 3))))) (.step 7 (.split 42 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.close 39)) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 29 (.step 37 (.close 39))))) (.step 7 (.step 11 (.step 29 (.step 37 (.close 39)))))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.close 39))) (.step 66 (.close 3))) (.split 71 1 (.step 45 (.step 37 (.step 39 (.step 3 (.step 39 (.close 11)))))) (.step 39 (.close 74)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029264195332239926022211708720090624189349957806788649020802658813870080⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 11 (.close 38))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 67 (.close 3))) (.step 29 (.step 3 (.close 66))))) (.step 40 (.step 29 (.step 38 (.close 3))))) (.step 9 (.close 7))) (.step 38 (.close 7))) (.step 38 (.close 7))))) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.step 66 (.split 65 1 (.split 64 1 (.split 74 1 (.split 8 0 (.split 71 1 (.step 7 (.step 29 (.step 7 (.close 37)))) (.step 37 (.close 3))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 11 (.step 29 (.close 37))))) (.step 66 (.step 67 (.close 3)))) (.step 3 (.step 29 (.close 37))))) (.split 63 1 (.step 45 (.step 29 (.step 39 (.step 66 (.step 3 (.step 37 (.step 3 (.close 77)))))))) (.step 37 (.close 66)))) (.split 63 1 (.step 39 (.step 3 (.step 37 (.close 11)))) (.step 37 (.close 66)))) (.step 38 (.close 7)))))) (.run (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 38 (.step 3 (.close 7)))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.step 3 (.close 74))) (.step 3 (.close 7))) (.step 29 (.close 67))) (.step 29 (.close 66))) (.step 29 (.step 3 (.close 7)))) (.step 9 (.close 7))) (.step 3 (.step 7 (.close 29)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938695453085160407504507633397016531618710402713518080⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.close 69)) (.step 25 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 75)))) (.step 67 (.close 3))) (.step 3 (.step 11 (.step 19 (.close 69))))) (.step 11 (.step 66 (.close 3)))) (.step 11 (.step 23 (.step 29 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20))))))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 19 (.close 69)))))))))))) (.run (.step 7 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 64 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.close 69)) (.step 20 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 11 (.step 29 (.step 19 (.close 20)))))) (.step 11 (.step 51 (.close 67)))) (.step 3 (.close 20))) (.step 11 (.step 66 (.close 3)))) (.step 11 (.step 23 (.step 29 (.step 38 (.step 66 (.step 7 (.step 19 (.close 20))))))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 66 (.step 20 (.close 67)))))))) (.split 26 1 (.split 35 1 (.split 71 1 (.step 25 (.step 19 (.step 20 (.step 25 (.close 29))))) (.step 20 (.close 74))) (.step 19 (.step 20 (.step 25 (.close 38))))) (.step 7 (.step 11 (.step 29 (.step 20 (.close 66))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982334001028195230293770581240184832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 77 (.split 63 1 (.split 64 1 (.split 67 1 (.step 11 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 17 (.close 29))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 11 (.close 67)))) (.step 66 (.close 3)))) (.step 23 (.step 11 (.step 17 (.close 3))))) (.step 11 (.close 7))) (.step 23 (.step 11 (.step 17 (.step 29 (.step 66 (.step 7 (.step 37 (.close 69))))))))) (.step 29 (.step 23 (.step 11 (.step 17 (.step 66 (.step 7 (.step 37 (.close 77))))))))) (.step 29 (.step 38 (.step 11 (.step 17 (.step 66 (.step 67 (.step 3 (.step 17 (.close 37)))))))))) (.step 17 (.step 29 (.step 38 (.step 66 (.step 7 (.step 37 (.step 17 (.close 37))))))))) (.step 3 (.step 67 (.step 7 (.close 17))))) (.step 29 (.step 23 (.step 17 (.close 3))))) (.step 17 (.step 7 (.close 17)))) (.step 17 (.step 7 (.close 17)))) (.step 17 (.step 7 (.close 17)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268678795458523172077943390208⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.split 17 1 (.split 22 1 (.step 67 (.split 26 1 (.split 35 1 (.split 65 1 (.split 63 1 (.split 72 1 (.split 8 0 (.split 17 0 (.step 7 (.close 19)) (.step 19 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 11 (.step 19 (.close 29))))) (.step 11 (.step 66 (.close 3)))) (.step 3 (.step 11 (.close 19)))) (.step 11 (.step 23 (.step 38 (.close 19))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 19 (.close 66)))))))) (.split 26 1 (.split 35 1 (.split 64 1 (.step 25 (.step 20 (.step 66 (.step 19 (.close 3))))) (.step 19 (.close 67))) (.step 19 (.close 38))) (.step 7 (.step 11 (.step 29 (.step 19 (.close 66))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 64 1 (.step 20 (.step 3 (.step 19 (.close 29)))) (.step 19 (.close 67))) (.step 19 (.close 38))) (.step 7 (.step 29 (.step 19 (.close 66)))))))))) (.reuse 1)) (.run (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.step 66 (.step 7 (.close 38))))) (.step 29 (.step 3 (.close 7)))) (.step 17 (.step 3 (.close 7))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342787806629724160⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 8 1 (.reuse 0) (.run (.step 11 (.split 10 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 42 1 (.step 11 (.close 3)) (.step 7 (.step 11 (.close 29)))) (.step 11 (.step 3 (.close 69)))) (.step 11 (.close 74))) (.step 3 (.close 7))) (.step 7 (.step 29 (.step 11 (.close 39))))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.close 7))) (.step 9 (.step 29 (.step 38 (.step 11 (.close 38)))))) (.step 29 (.step 38 (.step 66 (.step 7 (.step 37 (.step 11 (.step 37 (.close 67))))))))) (.step 3 (.step 7 (.close 11)))) (.step 9 (.step 29 (.close 11)))) (.step 3 (.step 7 (.close 11))))))) (.run (.split 8 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.split 63 1 (.step 7 (.close 38)) (.step 3 (.close 38))))) (.step 29 (.step 3 (.close 7)))) (.step 3 (.split 63 1 (.step 7 (.close 17)) (.step 3 (.close 17))))) (.step 11 (.step 3 (.close 7))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case25
