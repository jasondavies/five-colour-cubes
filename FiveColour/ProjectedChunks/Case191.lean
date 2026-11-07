module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case191
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422783681451276125106174159757508608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨10699377823114678020775, 5789234131004114107589337099063798706207994136494267968630320216040438736791686334725463514473658914523947363325998255082438296860036168560471394733557376541140673600293513512804909734550378981589101974352375147282581947392, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857385551707953231615728050383372398325368190954110976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 39 0 (.step 68 (.close 18)) (.split 42 0 (.step 68 (.step 5 (.close 7))) (.step 24 (.step 38 (.step 7 (.step 4 (.close 20))))))) (.step 52 (.step 43 (.split 39 0 (.step 29 (.close 68)) (.step 31 (.close 43)))))) (.step 53 (.step 29 (.step 24 (.close 22))))) (.split 35 0 (.step 53 (.step 7 (.step 68 (.close 4)))) (.split 39 0 (.step 53 (.step 29 (.close 38))) (.step 38 (.close 5))))) (.split 30 0 (.split 39 0 (.split 35 0 (.split 34 0 (.split 42 0 (.step 27 (.close 29)) (.step 7 (.close 27))) (.step 9 (.step 24 (.step 29 (.close 5))))) (.step 53 (.close 29))) (.step 42 (.step 27 (.close 29)))) (.split 43 0 (.step 42 (.step 7 (.close 20))) (.step 7 (.step 9 (.close 7)))))) (.split 24 0 (.split 39 0 (.split 42 0 (.step 62 (.close 68)) (.split 17 0 (.step 24 (.close 70)) (.step 7 (.close 24)))) (.split 42 0 (.step 42 (.step 24 (.step 27 (.step 24 (.close 20))))) (.step 24 (.close 20)))) (.split 39 0 (.split 42 0 (.step 62 (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 42 (.step 7 (.close 27)))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984359093554418014551097000428369480777728⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 26 0 (.step 53 (.step 63 (.close 24))) (.step 7 (.close 27))) (.step 53 (.close 7))) (.step 67 (.close 53))) (.step 42 (.split 35 0 (.step 7 (.close 20)) (.step 42 (.close 53))))) (.split 22 0 (.split 24 0 (.split 26 0 (.step 42 (.step 24 (.step 42 (.close 61)))) (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 24 (.step 19 (.step 7 (.step 19 (.step 20 (.close 4)))))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.step 52 (.close 68)) (.split 30 0 (.step 15 (.step 27 (.close 29))) (.step 52 (.step 4 (.close 29))))) (.split 34 0 (.step 27 (.step 52 (.close 29))) (.step 5 (.step 17 (.close 7))))) (.split 24 0 (.split 26 0 (.step 52 (.step 24 (.step 13 (.close 68)))) (.split 30 0 (.step 27 (.close 7)) (.step 7 (.close 24)))) (.split 30 0 (.step 27 (.close 7)) (.step 7 (.close 24))))) (.split 22 0 (.split 24 0 (.split 26 0 (.step 52 (.step 24 (.step 13 (.close 68)))) (.step 11 (.step 61 (.step 24 (.step 4 (.close 29)))))) (.step 61 (.step 7 (.close 15)))) (.step 17 (.step 24 (.step 61 (.step 7 (.close 68))))))) (.split 17 0 (.split 22 0 (.step 42 (.split 24 0 (.split 26 0 (.step 42 (.close 68)) (.step 11 (.step 24 (.close 38)))) (.step 11 (.step 17 (.step 27 (.close 7)))))) (.step 17 (.step 24 (.step 19 (.close 68))))) (.step 24 (.split 22 0 (.step 11 (.step 17 (.step 19 (.close 20)))) (.step 19 (.step 7 (.step 13 (.close 20))))))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422782413799466969904235429761122304⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 9 (.split 26 0 (.split 35 0 (.split 36 0 (.split 51 0 (.step 15 (.close 68)) (.step 57 (.close 4))) (.step 15 (.close 57))) (.step 15 (.step 38 (.close 57)))) (.step 15 (.close 29)))) (.step 53 (.step 9 (.step 38 (.step 7 (.step 13 (.step 15 (.close 4)))))))) (.split 30 0 (.step 43 (.step 62 (.close 68))) (.step 24 (.close 43)))) (.split 26 0 (.split 22 0 (.step 43 (.split 61 0 (.split 63 0 (.step 54 (.close 24)) (.step 4 (.close 66))) (.step 4 (.close 5)))) (.step 23 (.close 24))) (.step 68 (.close 29)))) (.split 17 0 (.step 9 (.split 22 0 (.split 30 0 (.step 29 (.close 4)) (.step 43 (.step 42 (.step 4 (.close 27))))) (.step 24 (.step 27 (.close 7))))) (.step 24 (.step 27 (.close 7))))) (.split 24 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 43 (.step 53 (.step 17 (.step 11 (.close 24))))) (.step 53 (.close 15))) (.step 24 (.close 38))) (.step 68 (.close 29))) (.step 24 (.step 27 (.close 7))))) (.split 16 0 (.split 24 0 (.step 15 (.split 17 0 (.step 52 (.step 24 (.step 15 (.close 4)))) (.step 17 (.close 13)))) (.step 27 (.step 15 (.step 7 (.close 15))))) (.step 24 (.step 15 (.close 13)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013209590562518647521718805342837789343589859328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 52 (.split 26 0 (.step 52 (.step 68 (.close 33))) (.step 7 (.close 19)))) (.split 34 0 (.split 30 0 (.step 52 (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 7 (.close 15)))) (.split 24 0 (.split 34 0 (.step 62 (.step 70 (.step 66 (.step 7 (.step 13 (.close 24)))))) (.step 7 (.step 15 (.step 13 (.close 52))))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.step 52 (.step 7 (.step 54 (.close 20)))) (.step 42 (.close 68))) (.step 7 (.step 15 (.step 13 (.close 52))))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.step 13 (.step 20 (.close 24)))))))) (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.step 53 (.split 26 0 (.step 13 (.close 68)) (.step 7 (.close 19)))) (.step 7 (.step 15 (.step 13 (.close 52))))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.step 13 (.step 19 (.close 25))))))) (.step 7 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 19 (.close 20)))) (.step 17 (.step 19 (.close 4)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984359093554418015760022820042998655483904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 63 (.close 9)) (.step 42 (.close 9))) (.step 9 (.step 52 (.step 7 (.close 9))))) (.step 9 (.split 34 0 (.step 27 (.close 46)) (.step 9 (.close 7))))) (.split 35 0 (.step 53 (.close 7)) (.step 42 (.close 4)))) (.step 9 (.split 26 0 (.split 30 0 (.step 9 (.close 11)) (.step 42 (.close 7))) (.step 9 (.close 11))))) (.split 24 0 (.split 26 0 (.step 62 (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.split 24 0 (.split 26 0 (.step 61 (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.split 17 0 (.split 22 0 (.step 42 (.split 24 0 (.split 26 0 (.step 7 (.close 9)) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 11)))) (.split 16 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 49 0 (.split 17 0 (.step 52 (.step 9 (.step 11 (.close 4)))) (.step 11 (.close 4))) (.step 17 (.close 9))) (.step 11 (.close 27))) (.split 43 0 (.split 17 0 (.split 35 0 (.step 52 (.step 7 (.close 9))) (.step 5 (.step 17 (.close 11)))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 11 (.step 9 (.close 7)))) (.step 11 (.step 7 (.close 9)))) (.step 11 (.close 7)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422783681451276123953251555639033856⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.step 9 (.step 24 (.step 9 (.close 5)))) (.step 9 (.close 7))) (.step 23 (.step 17 (.step 9 (.close 7))))) (.step 24 (.step 9 (.close 5)))) (.split 16 0 (.split 17 0 (.step 9 (.step 17 (.step 9 (.close 5)))) (.step 17 (.close 4))) (.step 17 (.close 4)))))) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 17 (.step 9 (.close 5)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 9 (.step 46 (.close 11))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 46 (.close 29)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 17 (.step 15 (.step 17 (.split 24 0 (.step 17 (.close 7)) (.step 11 (.close 7)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422782413799466971057156934367969280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.split 51 0 (.step 9 (.close 4)) (.step 46 (.step 7 (.close 4)))) (.step 9 (.close 7)))) (.step 53 (.step 9 (.step 7 (.close 9))))) (.split 30 0 (.step 43 (.step 27 (.step 4 (.close 9)))) (.step 7 (.close 9)))) (.step 9 (.split 26 0 (.split 22 0 (.split 30 0 (.step 9 (.close 4)) (.step 42 (.close 7))) (.step 11 (.close 7))) (.step 9 (.close 11))))) (.split 22 0 (.split 26 0 (.step 43 (.step 27 (.split 61 0 (.step 4 (.close 11)) (.step 4 (.close 5))))) (.step 27 (.close 7))) (.step 7 (.close 9)))) (.split 26 0 (.split 30 0 (.split 35 0 (.step 43 (.step 27 (.step 11 (.close 4)))) (.step 53 (.close 7))) (.step 7 (.close 9))) (.step 68 (.close 11)))) (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.step 52 (.step 9 (.step 11 (.close 4)))) (.step 11 (.close 7)))) (.step 23 (.step 11 (.close 7)))) (.step 24 (.step 15 (.step 11 (.close 4)))))) (.split 14 0 (.split 24 0 (.split 26 0 (.split 30 0 (.step 15 (.step 9 (.close 11))) (.split 16 0 (.step 15 (.step 9 (.close 4))) (.step 7 (.close 9)))) (.step 9 (.close 29))) (.step 9 (.step 4 (.close 7)))) (.step 15 (.close 4)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422783681451276125106173060245880832⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.step 52 (.split 30 0 (.step 9 (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 52 (.step 24 (.step 9 (.step 4 (.close 29)))))) (.split 16 0 (.step 15 (.close 4)) (.step 7 (.close 11)))))) (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.step 9 (.step 7 (.step 9 (.close 5)))) (.step 9 (.close 7))) (.step 23 (.step 11 (.close 7)))) (.step 24 (.step 9 (.close 5)))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 4)) (.step 9 (.close 7))) (.step 5 (.close 11))) (.step 9 (.close 11))) (.step 5 (.step 9 (.close 11)))) (.step 11 (.close 7)))) (.step 9 (.step 7 (.close 11)))) (.split 26 0 (.split 14 0 (.split 16 0 (.step 24 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 5 (.step 11 (.close 7)))) (.step 4 (.step 9 (.close 7)))))))
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

namespace Part8
def root : Box := ⟨1100585369600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013209590562518646254068205114608388946398281728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 54 0 (.step 7 (.close 68)) (.step 9 (.step 43 (.close 57)))) (.step 9 (.step 43 (.close 7)))) (.step 53 (.step 7 (.step 9 (.step 18 (.close 24)))))) (.split 34 0 (.step 53 (.close 7)) (.step 7 (.close 19)))) (.split 30 0 (.split 39 0 (.split 35 0 (.step 7 (.close 20)) (.step 29 (.close 5))) (.step 27 (.close 4))) (.step 7 (.close 24)))) (.split 24 0 (.split 34 0 (.step 62 (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.step 7 (.close 24)) (.step 42 (.close 7))) (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 7 (.close 19)))) (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.step 53 (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 7 (.close 19))) (.step 7 (.close 19)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1100585369600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422782413799466969904236529272750080⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.step 52 (.step 68 (.close 42))) (.step 27 (.close 7))) (.step 27 (.close 7))) (.step 24 (.split 24 0 (.split 26 0 (.split 34 0 (.step 62 (.step 7 (.close 13))) (.step 7 (.close 17))) (.step 7 (.close 19))) (.step 7 (.close 24))))) (.step 11 (.step 24 (.split 24 0 (.split 26 0 (.split 22 0 (.step 61 (.close 7)) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 7 (.close 24)))))) (.step 11 (.split 24 0 (.step 24 (.split 26 0 (.split 17 0 (.step 42 (.step 7 (.close 13))) (.step 7 (.step 17 (.close 19)))) (.step 7 (.close 19)))) (.step 7 (.close 24))))))) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.split 22 0 (.split 24 0 (.split 30 0 (.split 26 0 (.split 35 0 (.split 61 0 (.step 43 (.step 7 (.close 13))) (.step 4 (.close 15))) (.step 15 (.step 37 (.step 18 (.close 24))))) (.step 27 (.close 7))) (.step 18 (.step 29 (.step 38 (.step 7 (.close 13)))))) (.split 26 0 (.step 43 (.step 27 (.close 7))) (.step 27 (.close 7)))) (.step 24 (.close 7)))) (.step 24 (.close 7))) (.step 24 (.close 7))) (.split 16 0 (.step 24 (.step 15 (.step 27 (.step 13 (.close 15))))) (.step 13 (.close 15))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1100585369600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422783681451276123953252655150661632⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 12 0 (.step 7 (.close 13)) (.step 13 (.close 15))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.step 33 (.step 15 (.step 7 (.close 19))))) (.step 7 (.close 24))) (.step 7 (.close 24))) (.step 7 (.close 19)))) (.step 7 (.close 24))) (.step 7 (.close 24))) (.split 24 0 (.split 26 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 7 (.close 15))) (.step 7 (.close 15)))))) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 9 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 10 0 (.step 9 (.close 7)) (.step 7 (.close 9)))) (.split 10 0 (.step 27 (.close 7)) (.step 7 (.close 9)))) (.split 24 0 (.split 26 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 11 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413343815423125496429219857387013210984360422783681451276125106174159757508608⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part5.root, Part7.root, Part10.root]
def proof : Chunks.Proof 5 := (.split 4 0 (.split 6 0 (.split 8 0 (.split 10 0 (.reuse 0) (.split 12 0 (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 24 0 (.split 34 0 (.split 39 0 (.step 15 (.step 11 (.close 13))) (.step 17 (.step 15 (.step 11 (.close 13))))) (.step 15 (.close 13))) (.split 43 0 (.step 17 (.step 66 (.step 7 (.close 15)))) (.step 7 (.close 9)))) (.step 17 (.split 26 0 (.step 13 (.close 15)) (.step 7 (.close 15)))))) (.step 17 (.step 15 (.split 26 0 (.step 13 (.close 15)) (.step 7 (.close 15)))))) (.step 17 (.step 24 (.step 42 (.step 17 (.close 13)))))))) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 26 0 (.split 22 0 (.step 15 (.step 52 (.step 13 (.close 17)))) (.step 17 (.step 13 (.close 15)))) (.step 15 (.close 7))) (.step 15 (.step 24 (.step 9 (.step 43 (.step 15 (.close 7))))))) (.step 24 (.close 13))) (.split 16 0 (.step 15 (.close 4)) (.step 13 (.close 15))))))) (.reuse 2)) (.reuse 3)) (.split 6 0 (.reuse 4) (.run (.split 8 0 (.split 14 0 (.split 24 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 9 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 10 0 (.split 26 0 (.step 24 (.step 9 (.step 11 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.close 9)))) (.split 10 0 (.split 16 0 (.step 24 (.step 9 (.step 11 (.close 7)))) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.split 10 0 (.step 9 (.close 7)) (.step 7 (.close 9)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part7.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case191
