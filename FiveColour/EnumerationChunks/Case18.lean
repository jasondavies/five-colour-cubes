module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case18
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978192852270710784⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592891989184984427175, 5789234131004114107589337099063798706207994136494267968630320216040438736791686334725463514473658914523947363325998255082438296860036168560471394733557376541140673600293513512804911129709412585432587090062323471997042951168, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740263991417851164129333279991059691165385259208543305728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 63 0 (.step 9 (.step 20 (.step 19 (.close 38)))) (.step 52 (.step 9 (.step 20 (.step 19 (.close 38)))))) (.step 52 (.step 9 (.step 15 (.step 20 (.step 19 (.close 38))))))) (.step 29 (.step 38 (.step 53 (.step 20 (.step 13 (.close 15))))))) (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 20 (.close 13))))) (.step 38 (.step 9 (.close 13))))) (.split 30 0 (.split 42 0 (.split 35 0 (.step 27 (.close 7)) (.step 29 (.step 7 (.close 9)))) (.step 62 (.step 29 (.close 7)))) (.step 42 (.step 43 (.step 11 (.step 24 (.step 20 (.close 27)))))))) (.split 24 0 (.split 34 0 (.split 36 0 (.split 30 0 (.step 9 (.step 27 (.step 7 (.close 29)))) (.step 38 (.step 9 (.step 27 (.close 7))))) (.step 29 (.close 7))) (.split 36 0 (.step 29 (.close 7)) (.step 7 (.close 29)))) (.split 30 0 (.step 29 (.step 7 (.close 9))) (.split 34 0 (.step 27 (.step 9 (.close 29))) (.step 7 (.step 24 (.close 27))))))) (.split 24 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 62 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.step 75 (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 19))))) (.step 7 (.step 19 (.close 20)))))) (.split 26 0 (.split 30 0 (.split 42 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 24 (.close 19)))) (.step 11 (.step 43 (.close 27)))))))
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457029428304824438768013225355480406539399856128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 42 (.step 13 (.close 19))))) (.step 42 (.step 38 (.close 11)))) (.step 38 (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 24))))) (.step 7 (.close 24))))) (.split 30 0 (.split 35 0 (.step 27 (.close 7)) (.step 43 (.step 11 (.close 27)))) (.step 7 (.step 24 (.close 27))))) (.split 24 0 (.split 26 0 (.step 24 (.step 42 (.split 34 0 (.step 25 (.step 11 (.step 19 (.close 13)))) (.step 17 (.step 24 (.close 19)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.close 27))))) (.split 22 0 (.split 24 0 (.split 26 0 (.step 24 (.step 42 (.split 34 0 (.step 42 (.step 19 (.step 9 (.step 13 (.close 20))))) (.step 17 (.step 24 (.close 19)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.close 27)))) (.split 24 0 (.step 24 (.step 19 (.step 7 (.step 20 (.step 9 (.close 13)))))) (.step 7 (.step 19 (.step 24 (.close 19))))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740263991417852557925908188155006037147777299731137429504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 57 (.close 19)))) (.step 43 (.step 9 (.step 15 (.close 17)))))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 27 (.step 15 (.close 29))) (.split 36 0 (.step 27 (.step 15 (.close 29))) (.step 7 (.step 27 (.step 15 (.close 17)))))) (.step 67 (.step 38 (.step 7 (.step 9 (.close 15))))))) (.split 26 0 (.split 30 0 (.split 35 0 (.step 27 (.close 7)) (.step 42 (.step 15 (.step 9 (.step 27 (.close 7)))))) (.step 42 (.step 52 (.step 43 (.step 11 (.step 24 (.step 15 (.close 7)))))))) (.step 11 (.split 30 0 (.step 27 (.step 7 (.step 15 (.close 17)))) (.step 27 (.close 7)))))) (.split 24 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 15 (.close 19)))))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 75 (.step 24 (.step 17 (.step 27 (.close 7))))))) (.step 11 (.step 17 (.split 42 0 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.close 27)))))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822101399346931959571337872447061993979904⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 61 (.step 24 (.close 11))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 20 (.step 9 (.close 13)))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 74 (.step 24 (.step 17 (.step 7 (.close 15))))))) (.step 11 (.step 17 (.step 61 (.step 43 (.step 27 (.close 7))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 74 (.step 24 (.step 74 (.step 43 (.step 7 (.close 15)))))) (.step 24 (.step 20 (.close 7)))) (.step 7 (.step 13 (.step 20 (.step 19 (.close 24))))))))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 42 (.step 24 (.step 11 (.close 15)))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.step 42 (.close 13)))) (.step 11 (.step 38 (.step 24 (.step 17 (.step 27 (.close 7))))))) (.step 11 (.step 17 (.step 42 (.step 24 (.close 27)))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 24 (.step 19 (.step 42 (.step 7 (.close 13)))))) (.step 24 (.step 19 (.close 7)))) (.step 7 (.step 13 (.step 19 (.step 20 (.close 24))))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 67 (.step 74 (.step 19 (.step 24 (.step 7 (.step 13 (.close 19))))))) (.step 19 (.step 7 (.step 13 (.close 20))))) (.step 24 (.step 19 (.step 7 (.close 13))))) (.step 19 (.step 7 (.step 13 (.close 20))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265487995527790975250748560113308512101193943747657728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 26 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.split 36 0 (.step 66 (.step 77 (.step 13 (.close 15)))) (.step 15 (.step 43 (.step 17 (.close 13))))) (.step 15 (.step 38 (.step 20 (.step 13 (.close 17))))))) (.split 35 0 (.step 9 (.step 38 (.step 37 (.step 53 (.step 13 (.step 15 (.close 20))))))) (.step 38 (.close 9)))) (.split 39 0 (.step 75 (.step 68 (.step 9 (.step 15 (.step 17 (.close 24)))))) (.step 17 (.step 9 (.step 24 (.step 38 (.step 15 (.close 19)))))))) (.split 22 0 (.split 30 0 (.split 39 0 (.step 29 (.step 66 (.step 20 (.close 19)))) (.step 9 (.step 17 (.step 24 (.step 38 (.step 15 (.close 19))))))) (.step 24 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33))))))) (.step 17 (.close 24)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.step 15 (.step 27 (.close 7))) (.step 38 (.step 15 (.step 29 (.close 7)))))) (.step 27 (.step 15 (.step 7 (.step 9 (.close 17)))))) (.step 29 (.close 7))) (.step 29 (.close 7))) (.step 15 (.step 7 (.close 27))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 29 (.close 7))) (.step 62 (.step 9 (.step 17 (.step 7 (.close 15)))))) (.step 43 (.step 52 (.step 24 (.step 9 (.step 15 (.close 7))))))) (.step 53 (.step 9 (.step 24 (.close 29))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.close 7)) (.step 9 (.close 29))) (.step 9 (.close 29))) (.step 9 (.step 27 (.step 24 (.step 15 (.step 27 (.close 7))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487210776254122274324480⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 22 0 (.step 9 (.step 38 (.step 17 (.step 15 (.step 19 (.close 7)))))) (.step 17 (.step 24 (.step 7 (.close 15))))) (.step 38 (.step 24 (.close 7)))) (.step 15 (.step 38 (.step 24 (.close 7))))) (.step 24 (.step 38 (.close 9)))) (.split 26 0 (.step 53 (.step 17 (.step 24 (.close 15)))) (.step 11 (.step 17 (.step 27 (.close 7)))))) (.step 17 (.split 22 0 (.step 24 (.step 7 (.step 15 (.step 19 (.close 27))))) (.step 24 (.close 7))))))) (.run (.split 16 0 (.split 24 0 (.step 15 (.split 26 0 (.split 17 0 (.split 34 0 (.split 22 0 (.step 52 (.step 9 (.step 15 (.close 17)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.close 17)))) (.split 26 0 (.step 52 (.split 30 0 (.split 34 0 (.step 52 (.step 27 (.step 15 (.step 7 (.close 15))))) (.step 17 (.step 9 (.step 15 (.close 17))))) (.step 17 (.step 7 (.step 9 (.close 15)))))) (.step 11 (.step 17 (.step 15 (.step 17 (.close 7))))))) (.step 17 (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780162777158844713765706750421196471353787155808891780869914560380796928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 34 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.step 9 (.step 19 (.close 38)))) (.step 9 (.step 24 (.step 39 (.close 7))))) (.step 29 (.step 53 (.step 24 (.close 7))))) (.split 35 0 (.step 53 (.step 7 (.step 9 (.close 13)))) (.step 42 (.step 7 (.step 9 (.close 13)))))) (.split 43 0 (.split 54 0 (.step 27 (.close 7)) (.step 29 (.close 7))) (.step 7 (.close 9)))) (.split 26 0 (.split 35 0 (.split 36 0 (.step 68 (.close 7)) (.step 7 (.step 15 (.step 17 (.step 19 (.close 20)))))) (.step 29 (.step 38 (.step 15 (.step 33 (.step 7 (.close 17))))))) (.step 7 (.step 15 (.step 17 (.close 19)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 52 (.close 24))) (.step 42 (.step 9 (.step 15 (.step 24 (.close 7)))))) (.step 43 (.step 11 (.step 17 (.close 7))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 27 (.step 24 (.step 17 (.step 7 (.close 13))))) (.step 7 (.step 13 (.step 17 (.step 19 (.close 20)))))) (.step 42 (.close 7))) (.step 7 (.step 13 (.close 17))))) (.split 30 0 (.split 43 0 (.step 43 (.step 29 (.close 15))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 24 (.close 19)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740263991417852557925908188155006037147777300830649057280⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.split 24 0 (.reuse 0) (.run (.split 26 0 (.split 14 0 (.split 34 0 (.split 49 0 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 19 (.close 20)))) (.step 27 (.step 7 (.close 19)))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 11 (.split 30 0 (.split 54 0 (.step 27 (.close 7)) (.step 15 (.step 24 (.step 17 (.close 27))))) (.step 7 (.step 24 (.step 17 (.step 19 (.close 15)))))))) (.split 14 0 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 27)))) (.step 11 (.step 27 (.close 7))))))) (.run (.split 24 0 (.split 26 0 (.split 14 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 7 (.step 13 (.close 19))))) (.step 42 (.step 43 (.step 7 (.step 19 (.close 13)))))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 11 (.step 24 (.split 30 0 (.split 34 0 (.split 39 0 (.step 43 (.step 7 (.close 13))) (.step 17 (.step 19 (.step 7 (.close 13))))) (.step 7 (.step 13 (.close 17)))) (.step 7 (.step 13 (.step 17 (.close 19)))))))) (.step 7 (.step 24 (.step 19 (.close 27))))) (.step 7 (.close 27)))))
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

namespace Part8
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822101399346931959571337872448161505607680⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 54 (.step 7 (.step 9 (.close 13)))) (.step 11 (.step 24 (.step 20 (.step 7 (.close 13)))))) (.step 42 (.step 43 (.step 7 (.step 19 (.close 13)))))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 11 (.step 24 (.split 30 0 (.step 74 (.step 24 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 17 (.close 19)))))))) (.step 7 (.step 24 (.step 19 (.close 27))))) (.step 7 (.close 27))) (.step 7 (.step 24 (.step 20 (.step 13 (.close 17)))))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 53 (.step 7 (.step 9 (.close 13)))) (.step 11 (.step 24 (.step 42 (.close 7))))) (.step 42 (.step 38 (.step 7 (.step 9 (.close 13)))))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 11 (.step 24 (.step 67 (.split 34 0 (.step 42 (.step 19 (.close 7))) (.step 7 (.step 13 (.close 17)))))))) (.step 7 (.step 24 (.step 19 (.close 27))))) (.step 7 (.close 27))) (.step 7 (.step 19 (.close 13)))) (.step 11 (.split 22 0 (.step 7 (.step 19 (.close 13))) (.step 19 (.step 7 (.step 13 (.close 17)))))))))
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
def root : Box := ⟨1329227995784915872903808160865714176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457029428306153666763798141228384214699191828480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 24 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.step 24 (.split 42 0 (.step 66 (.step 19 (.close 20))) (.step 15 (.step 24 (.close 7))))) (.step 53 (.step 24 (.close 7))))) (.step 24 (.close 7))) (.step 9 (.step 43 (.step 39 (.step 7 (.close 13)))))) (.step 9 (.split 17 0 (.split 22 0 (.step 38 (.split 30 0 (.step 15 (.step 38 (.step 37 (.step 7 (.close 19))))) (.step 37 (.step 33 (.close 19))))) (.step 24 (.step 15 (.step 7 (.close 13))))) (.step 24 (.step 15 (.step 7 (.close 13))))))) (.step 9 (.split 17 0 (.step 15 (.step 43 (.step 13 (.step 7 (.close 15))))) (.step 7 (.step 13 (.step 15 (.close 7))))))) (.step 9 (.step 29 (.close 7)))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 43 (.step 27 (.step 17 (.step 24 (.close 15))))) (.step 7 (.step 15 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 24 (.close 27)))) (.step 9 (.step 27 (.close 7))))) (.split 17 0 (.split 22 0 (.step 24 (.step 9 (.split 24 0 (.step 38 (.step 24 (.step 7 (.step 13 (.close 15))))) (.step 7 (.step 17 (.step 24 (.close 27))))))) (.step 7 (.step 13 (.close 19)))) (.step 7 (.step 13 (.step 19 (.close 15)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487210776255221785952256⟩
def references : Fin 6 → Box := ![Part0.root, Part1.root, Part3.root, Part5.root, Part8.root, Part9.root]
def proof : Chunks.Proof 6 := (.split 4 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 61 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 27 (.close 29)) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 24 (.close 27))))) (.split 26 0 (.split 30 0 (.split 39 0 (.step 43 (.step 11 (.close 27))) (.step 11 (.step 27 (.close 7)))) (.step 7 (.step 24 (.close 19)))) (.step 11 (.step 43 (.close 27))))) (.split 24 0 (.split 26 0 (.step 24 (.split 34 0 (.step 61 (.step 24 (.step 11 (.close 13)))) (.step 17 (.step 24 (.close 20))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.close 27))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 12 0 (.reuse 4) (.split 14 0 (.reuse 5) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 9 (.split 24 0 (.split 30 0 (.step 43 (.step 15 (.step 13 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 17 (.step 7 (.close 15)))))) (.step 11 (.step 17 (.close 7)))) (.step 11 (.step 17 (.close 7)))) (.step 11 (.step 17 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780162777158844713765706750421196471353788423459492009099316057084002304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 4 0 (.split 14 0 (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 24 (.step 33 (.close 19))))) (.step 15 (.step 43 (.step 13 (.step 9 (.close 15))))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 42 (.step 13 (.step 9 (.close 33))))) (.step 15 (.split 35 0 (.step 33 (.step 13 (.step 15 (.close 9)))) (.step 15 (.step 13 (.close 17))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 52 (.step 9 (.step 24 (.step 27 (.close 7))))) (.step 7 (.step 24 (.close 29)))) (.step 7 (.close 15))) (.step 7 (.step 24 (.close 29))))) (.step 15 (.split 26 0 (.split 30 0 (.step 66 (.step 15 (.close 11))) (.split 34 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15)))) (.step 15 (.step 7 (.close 17)))))) (.split 26 0 (.split 14 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 7 (.step 9 (.close 19)))) (.split 54 0 (.step 27 (.step 43 (.step 7 (.close 13)))) (.step 9 (.step 24 (.close 7))))) (.step 7 (.step 15 (.close 13)))) (.step 7 (.step 24 (.close 13)))) (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 66 (.step 7 (.close 15)))) (.step 15 (.step 7 (.close 13)))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 15 (.close 17))))))) (.step 7 (.step 24 (.step 19 (.close 29)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740263991417852557925908189422656637376006702327352262656⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.split 24 0 (.reuse 0) (.run (.split 26 0 (.split 4 0 (.split 14 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 52 (.step 27 (.close 7))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 24 (.close 19)))) (.step 15 (.step 17 (.close 7)))) (.step 7 (.step 24 (.step 17 (.step 19 (.close 20)))))) (.split 4 0 (.split 14 0 (.split 30 0 (.split 34 0 (.step 27 (.step 9 (.close 29))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 24 (.close 27)))) (.step 11 (.step 15 (.close 17)))) (.step 7 (.close 27)))))) (.run (.split 24 0 (.split 26 0 (.split 30 0 (.split 4 0 (.split 14 0 (.split 34 0 (.step 62 (.step 43 (.step 11 (.close 13)))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 7 (.step 17 (.step 24 (.close 13))))) (.step 7 (.split 14 0 (.split 34 0 (.split 35 0 (.step 62 (.step 33 (.step 13 (.step 11 (.step 20 (.close 19)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 15 (.step 17 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.close 27)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822101399348199610171566101849658208813056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 4 0 (.split 14 0 (.split 34 0 (.step 68 (.step 11 (.step 19 (.close 20)))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 7 (.step 17 (.close 19)))) (.step 7 (.split 14 0 (.split 34 0 (.step 42 (.step 33 (.step 13 (.step 24 (.step 9 (.close 33)))))) (.step 13 (.step 15 (.step 17 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.step 42 (.split 35 0 (.step 13 (.step 24 (.step 11 (.close 19)))) (.step 19 (.step 9 (.close 13))))))))) (.split 22 0 (.step 7 (.step 17 (.step 24 (.step 42 (.split 35 0 (.step 13 (.step 20 (.close 9))) (.step 19 (.step 9 (.close 13)))))))) (.step 19 (.step 7 (.step 13 (.step 17 (.step 13 (.step 20 (.close 9))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195395087439005656718489157632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 4 0 (.split 16 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 13 (.close 9)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.close 13))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 7 (.close 17)))) (.split 17 0 (.split 26 0 (.step 52 (.step 24 (.step 9 (.step 15 (.step 17 (.close 7)))))) (.step 9 (.step 15 (.close 17)))) (.step 7 (.step 15 (.close 17))))) (.step 17 (.step 15 (.step 17 (.step 7 (.step 9 (.close 13))))))) (.split 24 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 17 0 (.split 36 0 (.split 39 0 (.step 15 (.step 13 (.close 15))) (.step 17 (.close 7))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.close 9))) (.step 9 (.step 15 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 15 (.step 17 (.close 15)))))) (.step 17 (.close 15))))
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
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410680693917109639411409932253916542988379115219299860480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 30 0 (.step 9 (.split 34 0 (.split 35 0 (.step 9 (.close 11)) (.step 9 (.close 7))) (.step 29 (.step 9 (.step 7 (.step 9 (.close 11))))))) (.split 34 0 (.step 42 (.step 9 (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.split 43 0 (.split 30 0 (.split 39 0 (.step 75 (.step 9 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.split 43 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 36 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 57 (.step 17 (.step 9 (.close 7))))) (.step 9 (.step 11 (.close 7)))) (.split 34 0 (.split 39 0 (.step 67 (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 9 (.close 11))))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 9 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.close 11)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 9 (.step 7 (.close 11)))))) (.split 12 0 (.split 43 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 22 0 (.step 9 (.close 7)) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 29 (.step 7 (.close 9)))) (.step 29 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.step 9 (.step 11 (.step 7 (.close 15)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927745696136595868751449030656⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 24 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 12 0 (.split 14 0 (.step 9 (.split 51 0 (.step 11 (.close 7)) (.step 9 (.close 11)))) (.step 11 (.close 7))) (.step 9 (.close 11))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 9 (.close 11)) (.step 9 (.step 7 (.close 11)))) (.step 9 (.close 11))) (.step 9 (.close 11)))) (.split 12 0 (.step 42 (.step 9 (.split 14 0 (.split 22 0 (.step 46 (.step 9 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7))))) (.step 9 (.close 11)))) (.step 11 (.step 9 (.close 11)))))) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 12 0 (.step 74 (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 11 (.close 9))) (.step 11 (.close 7))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 12 0 (.step 67 (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 11 (.close 9))) (.step 11 (.close 7))) (.step 11 (.close 7)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296364825270248152236032⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 7 (.close 9))) (.step 9 (.step 42 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 17 (.close 7))) (.split 14 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 43 (.step 29 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7)))) (.split 26 0 (.split 35 0 (.split 49 0 (.split 50 0 (.step 17 (.split 39 0 (.step 7 (.close 9)) (.step 11 (.close 7)))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.step 11 (.close 7))))) (.step 17 (.step 7 (.step 9 (.close 11))))) (.step 17 (.step 7 (.close 11)))) (.step 17 (.step 9 (.step 15 (.step 9 (.step 7 (.close 9)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296364825271347663863808⟩
def references : Fin 5 → Box := ![Part10.root, Part12.root, Part13.root, Part14.root, Part17.root]
def proof : Chunks.Proof 5 := (.split 8 0 (.split 10 0 (.reuse 0) (.split 12 0 (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 4 0 (.split 14 0 (.split 34 0 (.step 68 (.step 11 (.step 19 (.close 20)))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 7 (.step 17 (.step 24 (.close 13))))) (.step 7 (.split 14 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 52 (.step 20 (.close 9)))) (.step 13 (.step 24 (.close 9)))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 15 (.step 17 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 25 (.step 11 (.step 13 (.close 19)))) (.step 19 (.step 13 (.step 20 (.close 9))))))))))) (.reuse 2)) (.reuse 3))) (.split 4 0 (.reuse 4) (.run (.split 12 0 (.split 16 0 (.split 10 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 17 0 (.step 9 (.split 22 0 (.split 30 0 (.split 34 0 (.step 27 (.step 68 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.step 11 (.step 9 (.close 7)))) (.split 24 0 (.step 7 (.step 9 (.step 11 (.close 9)))) (.step 11 (.step 7 (.close 9))))) (.step 11 (.close 7))) (.split 10 0 (.split 14 0 (.step 9 (.close 7)) (.step 11 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457029428304824438768013225356633328044006703104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 24 0 (.split 26 0 (.split 34 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 7)))) (.split 35 0 (.step 53 (.step 7 (.close 9))) (.step 38 (.close 7)))) (.split 17 0 (.step 62 (.split 39 0 (.step 29 (.step 24 (.close 9))) (.step 9 (.step 11 (.close 7))))) (.step 7 (.step 9 (.close 11))))) (.step 15 (.split 17 0 (.split 22 0 (.step 9 (.step 52 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.split 34 0 (.split 35 0 (.step 27 (.step 29 (.close 7))) (.step 29 (.close 7))) (.step 15 (.step 29 (.close 7))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 27 (.step 7 (.close 9)))) (.step 11 (.step 7 (.close 9)))) (.step 43 (.step 27 (.close 9)))) (.step 53 (.step 9 (.step 24 (.step 27 (.close 7)))))) (.step 11 (.step 9 (.close 11))))) (.split 17 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 22 0 (.step 9 (.close 11)) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 11 (.step 7 (.close 15))))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 7 (.close 9)))) (.step 7 (.close 11)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487211929175626881171456⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 24 0 (.split 26 0 (.split 43 0 (.split 16 0 (.step 15 (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.step 9 (.step 7 (.close 11))) (.step 42 (.step 9 (.close 7)))) (.step 52 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 11 (.close 7))) (.step 52 (.step 24 (.step 9 (.close 7))))) (.step 11 (.step 15 (.step 11 (.step 7 (.close 9)))))) (.step 11 (.close 9))))) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 49 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 11))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.split 34 0 (.step 9 (.split 35 0 (.split 16 0 (.step 15 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 9 (.close 7)))) (.step 7 (.step 9 (.close 7))))) (.step 9 (.step 29 (.close 7)))) (.split 30 0 (.split 16 0 (.step 9 (.step 7 (.close 11))) (.step 29 (.close 9))) (.step 9 (.close 7)))) (.split 24 0 (.step 15 (.step 7 (.close 11))) (.step 29 (.close 9))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1208926972536134855294976, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978191752759083008⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 12 0 (.split 43 0 (.step 11 (.close 7)) (.step 24 (.step 9 (.close 11)))) (.split 39 0 (.step 9 (.step 7 (.close 11))) (.step 9 (.close 11)))) (.step 29 (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 7 (.close 11))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 9 (.close 7))))) (.step 29 (.split 14 0 (.step 9 (.close 11)) (.step 11 (.close 9))))) (.split 12 0 (.split 14 0 (.split 16 0 (.step 9 (.step 24 (.step 9 (.step 11 (.close 7))))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 9 (.close 7)))) (.step 29 (.close 11))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 12 0 (.step 11 (.close 9)) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.step 7 (.close 11)))) (.step 9 (.step 7 (.step 9 (.close 11)))))) (.split 12 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 24 (.step 15 (.split 30 0 (.step 9 (.close 7)) (.step 7 (.close 9)))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.split 14 0 (.split 34 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 9 (.step 7 (.close 9)))))))
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
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978191752759083008⟩
def references : Fin 2 → Box := ![Part20.root, Part21.root]
def proof : Chunks.Proof 2 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 30 0 (.step 9 (.step 52 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.split 34 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 15)))) (.split 16 0 (.split 17 0 (.split 26 0 (.step 52 (.step 24 (.step 9 (.step 15 (.step 29 (.close 7)))))) (.step 9 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.split 30 0 (.step 15 (.close 7)) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.split 14 0 (.split 24 0 (.split 30 0 (.step 15 (.close 7)) (.step 15 (.close 7))) (.step 29 (.close 9))) (.step 15 (.close 7)))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978192852270710784⟩
def references : Fin 2 → Box := ![Part18.root, Part22.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.reuse 0) (.split 4 0 (.reuse 1) (.run (.split 8 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 10 0 (.split 16 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 11 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 29 (.close 7))) (.step 11 (.step 9 (.step 7 (.close 9))))) (.step 11 (.close 7))) (.split 10 0 (.split 14 0 (.step 9 (.close 7)) (.split 26 0 (.step 24 (.step 9 (.close 11))) (.step 9 (.close 7)))) (.split 14 0 (.split 24 0 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 11)))))) (.split 10 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 11))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part23

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part23.excludes
end FiveColour.Packed.EnumerationChunks.Case18
