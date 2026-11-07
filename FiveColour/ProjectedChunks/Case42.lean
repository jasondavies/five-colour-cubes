module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case42
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342785607606468608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593776385211095628535, 5789234131009374248507341982684158355876555513350053335929015326897327162342062193097593244396629436776638632267636611235444786831573185258760290656459859266733554791122816590519108237010294841316599838966919287400980022272, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334835886793856427426709802302643992082965358552532362368993382342746809133121826109575667830136054917344259328025643470467104768000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 65 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.split 10 0 (.step 75 (.step 3 (.close 17))) (.step 3 (.close 7))))) (.step 7 (.close 19))) (.step 7 (.step 11 (.step 67 (.step 7 (.close 19)))))) (.step 11 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.step 3 (.close 37)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.close 11))) (.step 11 (.close 7))))) (.step 29 (.split 74 1 (.step 3 (.step 75 (.close 3))) (.step 11 (.close 69))))) (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 15 (.close 29))))) (.step 74 (.step 3 (.close 69)))) (.step 3 (.step 7 (.close 3)))) (.step 67 (.step 3 (.step 67 (.split 72 1 (.step 3 (.close 67)) (.step 29 (.step 3 (.close 67)))))))) (.step 66 (.step 3 (.step 66 (.split 72 1 (.step 3 (.close 66)) (.step 29 (.close 66))))))) (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51)))) (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 9 (.step 3 (.close 11)))) (.step 3 (.close 47)))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460183827084136443896789531468703981888743326150587394561069408539401090006688079266830647035844971437490176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 72 1 (.step 45 (.close 7)) (.step 29 (.step 45 (.close 3)))) (.step 7 (.step 29 (.step 37 (.close 39))))) (.step 7 (.step 29 (.close 77)))) (.step 29 (.step 69 (.close 74)))) (.step 3 (.step 45 (.close 69)))) (.step 29 (.step 67 (.close 45)))) (.step 29 (.step 66 (.close 3))))))) (.run (.step 7 (.split 42 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.close 39))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 29 (.step 37 (.close 39))))) (.step 7 (.step 29 (.step 11 (.step 37 (.close 39)))))) (.step 29 (.close 74))) (.step 3 (.close 39))) (.step 29 (.step 51 (.step 67 (.close 3))))) (.step 29 (.step 66 (.close 3)))) (.step 39 (.split 63 1 (.split 64 1 (.step 39 (.step 45 (.close 74))) (.step 67 (.step 74 (.step 45 (.close 3))))) (.step 29 (.step 66 (.close 3))))))))) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.split 71 1 (.split 74 1 (.step 3 (.split 8 0 (.step 7 (.close 38)) (.step 3 (.step 11 (.close 37))))) (.step 11 (.step 3 (.close 77)))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.close 38))) (.step 67 (.close 3))) (.step 66 (.close 3)))) (.step 40 (.step 29 (.step 38 (.close 3))))) (.step 9 (.close 7))) (.step 29 (.step 38 (.close 7)))) (.step 29 (.step 38 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029264195332239926022211708720090624189349957806788649020801559302242304⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.step 66 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 72 1 (.split 14 0 (.step 7 (.close 29)) (.step 7 (.close 37))) (.step 29 (.step 37 (.close 3)))) (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 29 (.step 11 (.close 37))))) (.step 66 (.step 74 (.close 3)))) (.step 3 (.step 29 (.close 37)))) (.step 29 (.step 67 (.step 3 (.close 37)))))) (.split 63 1 (.split 64 1 (.step 45 (.step 29 (.step 39 (.step 66 (.step 3 (.step 37 (.step 3 (.close 77)))))))) (.step 66 (.step 45 (.step 39 (.close 67))))) (.step 37 (.close 66)))) (.split 63 1 (.split 64 1 (.step 39 (.step 7 (.step 37 (.close 11)))) (.step 66 (.step 39 (.step 3 (.close 67))))) (.step 37 (.close 66)))) (.step 38 (.close 7)))))) (.run (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 38 (.step 3 (.close 7)))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.step 74 (.step 3 (.step 11 (.close 19))))) (.step 3 (.close 7))) (.step 29 (.close 67))) (.step 29 (.close 66))) (.step 29 (.step 3 (.close 7)))) (.step 9 (.close 7))) (.step 29 (.step 3 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938695453085160407504507633397016531618709303201890304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.close 69)) (.split 26 0 (.step 19 (.close 7)) (.step 7 (.step 19 (.close 20))))) (.step 11 (.close 7))) (.step 7 (.step 11 (.step 29 (.step 19 (.close 20)))))) (.step 11 (.close 74))) (.step 3 (.close 20))) (.step 11 (.step 67 (.close 3)))) (.step 11 (.step 51 (.step 66 (.close 3))))) (.step 66 (.step 67 (.step 74 (.step 7 (.step 11 (.step 19 (.close 38)))))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 66 (.step 67 (.step 20 (.close 74))))))))) (.step 25 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 25 (.close 74))) (.step 19 (.step 20 (.step 25 (.close 67))))) (.step 66 (.step 74 (.step 25 (.close 3))))) (.step 7 (.step 19 (.step 29 (.step 20 (.close 75)))))) (.step 7 (.step 11 (.step 29 (.step 66 (.step 20 (.close 67)))))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914586797738407425837081849247901728959134433280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 17 1 (.split 22 1 (.step 67 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 17 0 (.step 7 (.close 19)) (.step 19 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 11 (.step 19 (.close 29))))) (.step 67 (.step 74 (.close 3)))) (.step 3 (.step 11 (.close 19)))) (.step 11 (.step 66 (.step 3 (.close 19))))) (.step 38 (.step 11 (.step 23 (.step 38 (.step 19 (.close 66))))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 19 (.step 66 (.step 20 (.step 67 (.close 69))))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 25 (.step 11 (.step 20 (.step 67 (.step 3 (.step 19 (.step 25 (.close 29)))))))) (.step 19 (.close 67))) (.step 66 (.step 19 (.close 3)))) (.step 19 (.close 38))) (.step 7 (.step 11 (.step 29 (.step 66 (.step 19 (.close 67))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 7 (.step 19 (.close 29)))) (.step 19 (.close 67))) (.step 66 (.step 19 (.close 3)))) (.step 19 (.close 38))) (.step 7 (.step 11 (.step 29 (.step 20 (.close 67))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982334001028195230293769481728557056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.step 77 (.split 42 1 (.split 65 1 (.split 67 1 (.step 11 (.split 71 1 (.split 72 1 (.step 3 (.split 16 0 (.split 34 0 (.step 3 (.step 17 (.close 29))) (.step 17 (.close 29))) (.step 17 (.close 3)))) (.step 29 (.step 3 (.close 75)))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.close 17))) (.step 29 (.step 23 (.step 11 (.step 7 (.step 37 (.close 69)))))))) (.step 74 (.step 7 (.step 37 (.close 77))))) (.step 11 (.step 17 (.step 3 (.close 67))))) (.step 17 (.step 66 (.close 3)))) (.step 23 (.step 11 (.step 17 (.close 3))))) (.step 11 (.close 7))) (.step 66 (.step 67 (.step 74 (.step 77 (.step 29 (.step 38 (.step 11 (.step 3 (.step 17 (.close 37))))))))))) (.step 17 (.step 29 (.step 38 (.step 66 (.step 67 (.step 7 (.step 37 (.step 17 (.close 37)))))))))) (.step 3 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.close 17)))))) (.step 3 (.step 29 (.step 17 (.step 23 (.step 29 (.step 17 (.close 66)))))))) (.step 11 (.step 17 (.step 7 (.close 17))))) (.step 11 (.step 17 (.step 7 (.close 17))))) (.step 11 (.step 17 (.step 7 (.close 17))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268678795458523170978431762432⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.close 69)) (.step 25 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 75)))) (.step 11 (.step 69 (.close 74)))) (.step 3 (.step 25 (.close 69)))) (.step 11 (.step 67 (.close 3)))) (.step 11 (.step 66 (.close 25)))) (.step 66 (.step 67 (.step 69 (.step 40 (.step 29 (.step 11 (.step 38 (.step 3 (.step 19 (.close 20))))))))))) (.step 29 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 67 (.close 69)))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.run (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.close 38)))))) (.step 29 (.step 3 (.close 7)))) (.step 17 (.step 3 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342785607606468608⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.reuse 0) (.run (.step 11 (.split 10 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 11 (.step 3 (.step 29 (.close 37)))) (.step 7 (.step 11 (.close 3)))) (.step 29 (.step 11 (.step 3 (.close 69))))) (.step 11 (.close 74))) (.step 3 (.close 7))) (.step 29 (.step 74 (.step 7 (.step 45 (.step 11 (.close 37))))))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.close 7))) (.step 9 (.step 38 (.step 11 (.step 38 (.close 66)))))) (.step 29 (.step 38 (.step 66 (.step 67 (.step 7 (.step 37 (.step 11 (.step 39 (.close 69)))))))))) (.step 11 (.step 3 (.close 7)))) (.step 9 (.step 29 (.close 11)))) (.step 11 (.step 3 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case42
