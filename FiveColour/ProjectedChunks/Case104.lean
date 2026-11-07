module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case104
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175151605088600124308697821266628831145616211968⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994274389529170594214600340844417290219481249533063345943983763165234683153281204528362401811244280921566048311241553993099478810657589405737878932752871438809585316528128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 2 0 (.split 14 0 (.step 7 (.step 3 (.close 5))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 31 (.close 5)))) (.step 58 (.close 3))) (.split 55 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.step 23 (.close 77))))) (.step 18 (.close 3))) (.step 23 (.step 18 (.close 5)))) (.step 18 (.step 44 (.close 58))))) (.step 3 (.close 7))) (.step 44 (.split 55 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 62 (.close 3)) (.step 3 (.close 7))) (.step 7 (.close 62))) (.step 18 (.close 3))) (.step 18 (.step 31 (.close 3)))) (.step 3 (.step 5 (.close 21)))) (.step 3 (.close 70))) (.step 31 (.step 48 (.step 3 (.close 5))))))) (.step 27 (.split 59 1 (.split 74 1 (.step 3 (.split 55 1 (.split 2 0 (.split 14 0 (.step 31 (.close 61)) (.step 18 (.close 61))) (.step 61 (.close 3))) (.step 58 (.close 61)))) (.step 44 (.step 61 (.close 3)))) (.step 61 (.step 3 (.close 5)))))) (.step 3 (.step 58 (.step 61 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 2 0 (.step 3 (.step 31 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.close 3))) (.step 5 (.close 61))) (.step 3 (.step 31 (.close 5)))))))) (.step 3 (.step 62 (.split 67 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.close 54)))))))
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467936284493724473583117056525282074210510832900871347523504789218712772098002427319275472436679198849450308559074469572066779780349952⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 58 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 58 (.split 51 1 (.split 67 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 55 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 34 0 (.split 22 0 (.step 53 (.close 5)) (.step 3 (.close 7))) (.step 9 (.close 31))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 18)))) (.step 18 (.close 3))) (.step 18 (.step 31 (.close 3)))) (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 21 (.close 58)))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 27 (.step 44 (.step 48 (.step 23 (.step 55 (.close 53))))))) (.step 62 (.close 31))) (.step 53 (.step 61 (.step 3 (.close 5))))) (.step 3 (.step 7 (.close 53)))) (.step 3 (.step 53 (.close 7))))))) (.run (.step 58 (.split 50 1 (.split 51 1 (.split 67 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 55 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 9 (.close 31))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 18)))) (.step 18 (.close 3))) (.step 18 (.close 52))) (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 22 (.step 5 (.close 52))))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 27 (.step 34 (.step 44 (.step 31 (.step 48 (.step 23 (.step 18 (.close 3))))))))) (.step 62 (.close 31))) (.step 61 (.close 52))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 52 (.close 7)))) (.split 56 1 (.step 52 (.close 31)) (.step 3 (.step 21 (.close 52)))))))))
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381085765702923413214792439202891444488461839163624319767044644917417080517819473636602486757713895675117794117211389952⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 27 (.step 3 (.step 46 (.step 52 (.step 53 (.step 7 (.step 9 (.step 27 (.close 46)))))))))))) (.run (.step 44 (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 31 (.close 44))) (.step 31 (.close 52)))))) (.run (.step 3 (.step 31 (.step 58 (.step 61 (.split 49 1 (.split 50 1 (.step 43 (.split 59 1 (.split 74 1 (.split 14 0 (.step 43 (.close 3)) (.step 5 (.step 18 (.close 31)))) (.step 5 (.step 18 (.close 31)))) (.step 3 (.step 5 (.step 31 (.close 21)))))) (.step 5 (.step 31 (.close 53)))) (.step 3 (.step 5 (.step 31 (.step 52 (.step 5 (.close 21))))))))))))) (.run (.step 31 (.step 58 (.step 61 (.split 40 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.step 31 (.step 42 (.step 3 (.step 61 (.step 27 (.step 42 (.step 3 (.step 31 (.close 18))))))))) (.step 42 (.step 31 (.step 42 (.close 43))))) (.step 44 (.step 42 (.step 3 (.close 5))))) (.step 21 (.step 32 (.step 42 (.close 3))))) (.step 34 (.step 42 (.step 44 (.close 52))))) (.step 3 (.step 5 (.step 31 (.close 42))))))))))
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209940665804528986909199763415403267014153686953807647624092307355074560⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 43 (.step 3 (.split 39 1 (.split 42 1 (.split 49 1 (.split 56 1 (.step 42 (.step 58 (.split 59 1 (.split 74 1 (.step 21 (.split 58 1 (.step 43 (.split 2 0 (.step 3 (.step 31 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.close 3)))) (.step 5 (.close 42))) (.step 3 (.step 21 (.step 31 (.close 5))))))) (.step 21 (.step 43 (.step 58 (.split 59 1 (.split 74 1 (.split 14 0 (.split 49 0 (.step 28 (.split 16 0 (.step 59 (.close 3)) (.step 18 (.close 41)))) (.step 3 (.step 21 (.close 41)))) (.step 18 (.step 5 (.close 31)))) (.step 5 (.close 31))) (.step 3 (.step 5 (.close 41)))))))) (.step 3 (.step 21 (.step 31 (.step 42 (.close 58)))))) (.step 31 (.close 45))) (.step 31 (.step 41 (.step 5 (.close 42))))))))) (.run (.step 7 (.step 36 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.close 31)) (.step 22 (.close 31))) (.step 21 (.step 22 (.close 31)))) (.step 31 (.close 52))) (.step 31 (.close 39))) (.step 31 (.close 39)))))))) (.run (.step 7 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.close 31)) (.step 31 (.close 21))) (.step 31 (.close 34))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.step 37 (.close 3)))) (.step 31 (.close 37)))))))) (.run (.step 18 (.step 31 (.split 49 1 (.split 58 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 18 (.close 52)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175151605088600121773396620810170028152207704064⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 31 (.step 27 (.step 34 (.step 77 (.split 59 1 (.split 55 1 (.step 3 (.split 74 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.step 23 (.close 17))))) (.step 18 (.close 3))) (.step 23 (.step 17 (.close 5)))) (.step 11 (.step 17 (.close 3))))) (.step 18 (.step 17 (.step 34 (.close 58))))) (.step 3 (.step 27 (.step 34 (.step 44 (.step 23 (.step 18 (.close 48)))))))))))) (.step 17 (.step 31 (.step 34 (.step 61 (.close 3)))))) (.step 31 (.step 5 (.close 17)))) (.step 3 (.step 17 (.step 27 (.step 34 (.step 53 (.step 61 (.split 2 0 (.split 16 0 (.step 55 (.step 62 (.step 23 (.step 17 (.close 3))))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.close 23)))))))))) (.step 5 (.step 31 (.close 17)))) (.step 5 (.step 34 (.step 36 (.step 42 (.close 17)))))) (.step 31 (.step 5 (.step 17 (.close 42))))) (.step 5 (.step 17 (.step 18 (.close 3))))) (.step 18 (.step 3 (.close 20)))) (.step 18 (.step 17 (.step 3 (.close 19)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175151605088600124308697821266628831145616211968⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.step 18 (.close 7)) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.close 41))))) (.run (.step 7 (.split 22 1 (.split 38 1 (.step 61 (.split 39 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42)))) (.step 18 (.close 41))) (.step 18 (.close 20)))))) (.run (.step 7 (.split 17 1 (.split 22 1 (.split 38 1 (.step 18 (.step 42 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.step 42 (.close 52)))))) (.step 18 (.close 41))) (.step 18 (.close 19))) (.step 18 (.close 19)))))) (.reuse 1)) (.run (.step 18 (.step 31 (.split 14 1 (.split 39 1 (.step 3 (.step 7 (.close 52))) (.step 3 (.close 18))) (.step 3 (.close 17))))))) (.run (.step 3 (.step 18 (.split 14 1 (.step 58 (.split 38 1 (.split 39 1 (.step 31 (.step 5 (.step 61 (.split 49 1 (.step 5 (.step 3 (.split 50 1 (.step 77 (.split 59 1 (.step 18 (.step 3 (.close 61))) (.step 23 (.close 21)))) (.step 3 (.step 23 (.close 53)))))) (.step 3 (.step 23 (.step 34 (.step 52 (.step 5 (.close 21)))))))))) (.step 5 (.step 42 (.close 18)))) (.step 5 (.close 31)))) (.step 5 (.step 23 (.step 17 (.close 42)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case104
