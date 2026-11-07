module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case87
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120422023168⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18740915245514405755891, 5789228615357111146520048038021683988773733487122101869605338720869906159532568379226031634421092153180474991687746456288884260796616315754835057774399955913938411420916390258617521507017839600618566356805942290412597150720, 0⟩]
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994274389529170594214600340844417290219481249533063345943983763165234683153281204528362401811246091939807446155179376873037740302136312576732176442184946085165910251798528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 3 (.close 5)) (.step 3 (.close 7))) (.step 7 (.close 5))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.close 7))) (.step 31 (.step 27 (.step 3 (.close 5))))) (.step 31 (.step 27 (.close 58)))) (.split 55 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.close 31)))) (.step 18 (.close 3))) (.step 23 (.step 18 (.close 5)))) (.step 18 (.step 27 (.close 58))))) (.step 3 (.close 7))) (.step 44 (.split 67 1 (.split 55 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 62 (.step 3 (.close 5))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 3 (.close 18)))) (.step 18 (.step 27 (.close 31)))) (.step 3 (.step 5 (.close 21)))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 3 (.close 7))))) (.step 3 (.step 27 (.step 61 (.step 3 (.split 59 1 (.step 18 (.close 31)) (.step 44 (.step 31 (.close 58))))))))) (.step 58 (.step 61 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.close 58))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3)))))) (.step 5 (.close 3))) (.step 5 (.close 61))) (.step 3 (.step 31 (.close 5))))))) (.split 67 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.close 54)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941829833112715212836213353650360377917705775022099156656941196115399184555861450459813876970130299600800850928467025566762663936000⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.step 58 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 58 (.step 61 (.step 62 (.split 51 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 58 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.split 24 0 (.step 31 (.close 53)) (.step 3 (.step 5 (.close 27))))) (.step 18 (.close 3))) (.step 18 (.close 3))) (.step 27 (.step 18 (.step 31 (.close 3))))) (.step 3 (.step 21 (.step 5 (.close 23))))) (.step 3 (.step 31 (.close 5)))) (.step 61 (.close 53))) (.step 58 (.close 53))) (.step 27 (.step 44 (.step 48 (.step 23 (.step 53 (.close 18))))))) (.step 3 (.close 70))) (.step 3 (.close 54)))))))) (.run (.step 58 (.step 61 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 58 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 52 (.split 24 0 (.step 31 (.close 52)) (.step 3 (.step 5 (.close 27))))) (.step 18 (.close 3))) (.step 18 (.close 3))) (.step 27 (.step 18 (.close 52)))) (.step 3 (.step 27 (.step 5 (.close 21))))) (.step 3 (.step 31 (.close 5)))) (.step 27 (.step 34 (.step 52 (.step 3 (.close 61)))))) (.step 58 (.close 52))) (.step 27 (.step 34 (.step 44 (.step 23 (.step 18 (.step 31 (.close 52)))))))) (.step 3 (.close 70))) (.step 3 (.close 54))) (.split 56 1 (.step 52 (.close 23)) (.step 3 (.step 21 (.close 52))))))))))) (.run (.step 27 (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381085765702923413214792439202891444488461840974642561164888582740297018779310952359773481055223327749764150442146660352⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 31 (.step 44 (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 18 (.step 21 (.step 31 (.close 27))))) (.step 31 (.close 44))))))) (.run (.step 3 (.step 31 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.split 16 0 (.split 58 1 (.step 43 (.close 3)) (.step 5 (.step 3 (.close 31)))) (.step 3 (.close 43))) (.step 5 (.step 18 (.close 31)))) (.step 3 (.step 5 (.step 27 (.close 31))))) (.step 5 (.step 21 (.step 27 (.step 31 (.close 53)))))) (.step 3 (.step 5 (.step 27 (.step 31 (.step 52 (.close 5)))))))))))) (.run (.step 31 (.step 58 (.step 61 (.split 40 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.step 31 (.step 27 (.step 3 (.step 42 (.step 5 (.step 3 (.close 5))))))) (.step 27 (.step 42 (.close 31)))) (.step 27 (.step 42 (.close 62)))) (.step 21 (.step 32 (.step 42 (.close 3))))) (.step 34 (.step 42 (.step 44 (.close 52))))) (.step 3 (.step 5 (.step 31 (.close 42))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319683306228182063648466809789138024906881990185147984463239722270448632290344960⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 43 (.step 3 (.split 39 1 (.split 42 1 (.split 49 1 (.split 56 1 (.step 42 (.step 58 (.split 59 1 (.split 74 1 (.step 21 (.split 58 1 (.step 43 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.close 21))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3)))))) (.step 5 (.close 3)))) (.step 5 (.close 42))) (.step 3 (.step 21 (.step 31 (.close 5))))))) (.step 21 (.step 43 (.split 59 1 (.split 74 1 (.split 14 0 (.step 28 (.split 16 0 (.step 59 (.close 3)) (.step 3 (.close 5)))) (.step 18 (.step 5 (.close 28)))) (.step 5 (.close 28))) (.step 3 (.step 5 (.close 41))))))) (.step 21 (.step 31 (.step 42 (.close 58))))) (.step 31 (.close 45))) (.step 31 (.step 41 (.step 5 (.close 42))))))))) (.run (.step 36 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.close 31)) (.step 22 (.close 31))) (.step 21 (.step 22 (.close 31)))) (.step 31 (.close 36))) (.step 31 (.step 7 (.close 39)))) (.step 31 (.step 28 (.close 39)))))))) (.run (.step 7 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.close 31)) (.step 31 (.close 21))) (.step 18 (.step 21 (.step 31 (.close 27))))) (.step 31 (.close 34))) (.step 31 (.close 37))) (.step 31 (.step 28 (.close 37)))) (.step 31 (.close 37)))))))) (.run (.step 18 (.step 31 (.split 49 1 (.split 58 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.close 18)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264664859336342455549014547889839436527136579482103871563161282160885760⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 24 1 (.split 25 1 (.reuse 0) (.run (.step 43 (.split 34 1 (.split 36 1 (.split 38 1 (.step 3 (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 27 (.step 58 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.close 58))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3)))))) (.step 5 (.close 3))) (.step 5 (.close 27))) (.step 3 (.step 27 (.close 28)))))) (.step 43 (.split 59 1 (.split 74 1 (.split 49 0 (.step 28 (.close 3)) (.step 3 (.step 22 (.close 58)))) (.step 5 (.close 28))) (.step 5 (.close 28))))) (.step 3 (.step 21 (.step 27 (.step 29 (.step 27 (.close 58))))))) (.step 3 (.step 31 (.step 27 (.close 58))))) (.step 29 (.close 28))) (.step 29 (.step 27 (.step 5 (.close 28)))))) (.step 21 (.step 28 (.step 43 (.split 49 1 (.split 59 1 (.split 74 1 (.split 49 0 (.step 28 (.close 3)) (.step 3 (.step 21 (.close 28)))) (.step 5 (.close 28))) (.step 3 (.step 5 (.close 28)))) (.step 3 (.step 5 (.step 21 (.close 28))))))))) (.step 29 (.close 28))) (.step 29 (.close 28)))))) (.run (.step 27 (.step 29 (.split 25 1 (.split 38 1 (.split 56 1 (.split 34 1 (.step 27 (.step 31 (.step 27 (.close 3)))) (.step 3 (.close 34))) (.step 29 (.step 5 (.close 27)))) (.step 28 (.step 29 (.step 5 (.close 27))))) (.step 5 (.step 28 (.step 29 (.step 27 (.close 43))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113104665924917034109097127013515264⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 27 (.step 31 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 24 1 (.step 31 (.step 27 (.step 34 (.step 77 (.split 55 1 (.step 3 (.split 74 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.close 31)))) (.step 18 (.close 3))) (.step 23 (.step 18 (.close 5)))) (.step 11 (.step 17 (.close 3))))) (.step 18 (.step 17 (.step 27 (.close 58))))))))) (.step 27 (.close 5))) (.step 3 (.step 27 (.step 34 (.step 44 (.step 18 (.close 23))))))) (.step 17 (.step 27 (.step 31 (.step 61 (.close 3)))))) (.step 31 (.step 5 (.close 17)))) (.step 3 (.step 17 (.step 27 (.step 34 (.step 48 (.step 53 (.step 23 (.step 55 (.step 23 (.step 17 (.step 53 (.close 61))))))))))))) (.step 5 (.step 18 (.step 27 (.step 17 (.close 31)))))) (.step 27 (.step 34 (.step 36 (.step 42 (.close 17)))))) (.step 31 (.step 5 (.close 42)))) (.step 18 (.step 27 (.step 29 (.step 5 (.close 17)))))) (.step 17 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 17)))) (.step 18 (.step 3 (.close 19)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120419926016⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 27 (.split 25 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.close 7)) (.step 3 (.close 18))) (.step 18 (.close 61))) (.step 18 (.step 27 (.close 53)))) (.step 18 (.step 27 (.close 52)))) (.step 18 (.close 42))) (.step 18 (.close 28))) (.step 18 (.close 28)))))) (.run (.step 7 (.step 27 (.split 22 1 (.split 25 1 (.split 38 1 (.step 18 (.step 61 (.step 7 (.step 42 (.split 49 1 (.split 50 1 (.split 59 1 (.split 24 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 27)))) (.step 18 (.step 42 (.close 53)))) (.step 18 (.step 42 (.close 52)))))))) (.step 18 (.close 28))) (.step 18 (.close 28))) (.step 18 (.close 20))))))) (.run (.step 7 (.step 27 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.step 18 (.step 42 (.step 7 (.step 42 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.close 7)) (.step 3 (.close 18))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.step 42 (.close 52)))))))) (.step 18 (.close 28))) (.step 18 (.close 28))) (.step 18 (.close 19))) (.step 18 (.close 19))))))) (.reuse 1)) (.run (.step 18 (.split 14 1 (.split 24 1 (.step 31 (.split 39 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 18)))) (.step 3 (.close 18))) (.step 3 (.close 17))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120422023168⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 58 (.split 14 1 (.split 25 1 (.split 38 1 (.split 49 1 (.step 5 (.split 39 1 (.step 31 (.step 5 (.step 27 (.step 61 (.step 3 (.split 50 1 (.step 77 (.step 61 (.step 18 (.close 23)))) (.step 3 (.step 21 (.step 27 (.close 53)))))))))) (.step 5 (.step 42 (.close 18))))) (.step 3 (.step 5 (.step 23 (.step 27 (.step 34 (.step 42 (.step 52 (.step 5 (.close 21)))))))))) (.step 5 (.close 31))) (.step 5 (.close 28))) (.step 5 (.step 23 (.step 17 (.close 27)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case87
