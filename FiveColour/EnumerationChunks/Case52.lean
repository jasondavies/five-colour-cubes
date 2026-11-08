module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case52
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536717978825146751380943497166683183416463178149816793478034800068072767676743680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536717978825146751380943497166683183416463178149815525827434571838671270973538304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 17 0 (.split 22 0 (.split 51 0 (.step 38 (.step 29 (.step 3 (.step 15 (.step 3 (.close 37)))))) (.step 39 (.step 38 (.step 3 (.close 11))))) (.step 45 (.split 35 0 (.split 38 0 (.split 36 0 (.step 3 (.step 11 (.step 15 (.close 19)))) (.step 20 (.step 11 (.step 15 (.close 19))))) (.step 33 (.step 3 (.close 5)))) (.step 24 (.step 3 (.close 19)))))) (.split 22 0 (.split 34 0 (.split 35 0 (.split 38 0 (.step 20 (.close 11)) (.step 33 (.step 3 (.close 5)))) (.step 24 (.step 3 (.close 19)))) (.step 39 (.step 38 (.step 3 (.step 11 (.close 15)))))) (.split 34 0 (.split 35 0 (.step 20 (.step 19 (.step 11 (.close 20)))) (.step 24 (.step 4 (.close 19)))) (.step 45 (.step 39 (.step 4 (.step 11 (.close 19)))))))) (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 38 0 (.step 13 (.step 24 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.step 13 (.step 19 (.close 20))))) (.step 37 (.close 11))) (.step 13 (.step 45 (.split 35 0 (.step 19 (.step 25 (.step 3 (.step 5 (.close 11))))) (.step 3 (.step 11 (.step 17 (.close 19)))))))) (.split 22 0 (.step 13 (.split 35 0 (.step 20 (.step 19 (.step 11 (.step 17 (.close 20))))) (.step 3 (.step 11 (.step 17 (.close 19)))))) (.split 30 0 (.split 35 0 (.step 20 (.step 11 (.step 3 (.step 13 (.close 17))))) (.step 11 (.step 17 (.step 19 (.close 3))))) (.step 13 (.step 19 (.step 20 (.step 11 (.close 17))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536717978825146751380943497166683183415069381574908629531688817676032245082619904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 30 0 (.split 51 0 (.step 3 (.step 11 (.close 13))) (.step 13 (.step 5 (.step 11 (.close 19))))) (.step 13 (.step 33 (.step 20 (.step 24 (.close 38)))))) (.step 33 (.step 4 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.split 35 0 (.split 36 0 (.split 30 0 (.step 5 (.step 11 (.step 13 (.close 15)))) (.step 13 (.step 33 (.step 15 (.step 14 (.close 38)))))) (.step 39 (.step 37 (.split 38 0 (.step 15 (.step 3 (.step 14 (.close 38)))) (.step 5 (.step 14 (.step 16 (.close 33)))))))) (.step 33 (.step 17 (.step 15 (.step 3 (.step 4 (.close 39)))))))) (.step 13 (.step 45 (.split 35 0 (.split 38 0 (.split 64 0 (.step 45 (.step 3 (.step 11 (.close 14)))) (.step 17 (.step 19 (.step 3 (.step 11 (.close 20)))))) (.step 14 (.step 19 (.step 5 (.step 20 (.close 23)))))) (.step 24 (.step 4 (.step 17 (.close 19)))))))) (.split 22 0 (.step 13 (.split 35 0 (.split 38 0 (.split 64 0 (.step 39 (.step 17 (.step 3 (.close 11)))) (.step 17 (.step 19 (.close 20)))) (.step 14 (.step 19 (.close 23)))) (.step 24 (.step 33 (.step 3 (.close 17)))))) (.split 34 0 (.step 19 (.step 13 (.step 20 (.step 19 (.close 11))))) (.step 13 (.step 14 (.step 17 (.close 20))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536717978825146751380943497166683183416463178149816793478034800068072767676743680⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 51 0 (.split 63 0 (.split 30 0 (.step 29 (.step 3 (.step 15 (.step 3 (.close 38))))) (.step 33 (.step 38 (.step 3 (.step 11 (.close 15)))))) (.step 37 (.step 29 (.step 66 (.close 3))))) (.step 39 (.split 35 0 (.step 13 (.step 3 (.step 15 (.close 16)))) (.step 33 (.step 3 (.close 13)))))) (.step 45 (.split 35 0 (.split 30 0 (.step 45 (.step 3 (.close 11))) (.step 13 (.step 33 (.step 20 (.step 15 (.close 39)))))) (.step 33 (.step 4 (.step 13 (.step 11 (.close 15)))))))) (.split 34 0 (.split 22 0 (.split 35 0 (.split 30 0 (.step 39 (.step 3 (.close 11))) (.step 13 (.step 33 (.step 20 (.step 3 (.close 39)))))) (.step 33 (.step 4 (.step 13 (.step 11 (.close 20)))))) (.step 13 (.step 45 (.split 35 0 (.step 20 (.step 3 (.close 23))) (.step 19 (.step 24 (.close 3))))))) (.step 39 (.split 22 0 (.step 66 (.close 5)) (.step 13 (.step 14 (.close 17)))))))) (.reuse 0)) (.run (.split 16 0 (.split 34 0 (.split 36 0 (.step 13 (.step 3 (.step 11 (.close 13)))) (.split 63 0 (.split 17 0 (.split 22 0 (.step 39 (.step 13 (.close 3))) (.step 13 (.close 3))) (.step 13 (.close 3))) (.step 3 (.close 13)))) (.split 63 0 (.split 74 0 (.split 64 0 (.step 37 (.step 11 (.close 13))) (.step 3 (.step 13 (.step 11 (.step 15 (.close 17)))))) (.step 13 (.step 3 (.close 17)))) (.step 3 (.step 13 (.close 33))))) (.step 13 (.step 5 (.step 13 (.close 17)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536717978825146751380943497166683183416463178149816793478034800068072767676743680⟩
def references : Fin 2 → Box := ![Part0.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 14 0 (.split 30 0 (.step 29 (.split 63 0 (.step 3 (.step 33 (.close 38))) (.step 37 (.step 3 (.step 33 (.close 38)))))) (.step 38 (.step 3 (.step 24 (.step 15 (.close 29)))))) (.split 30 0 (.split 67 0 (.step 29 (.step 37 (.step 3 (.close 5)))) (.step 75 (.step 3 (.step 11 (.close 13))))) (.step 37 (.step 33 (.step 5 (.step 11 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 75 (.step 3 (.step 11 (.close 13)))) (.step 37 (.step 45 (.close 3)))) (.step 45 (.step 33 (.split 14 0 (.step 45 (.step 3 (.close 11))) (.step 13 (.step 33 (.step 5 (.step 11 (.close 17)))))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 74 (.step 3 (.step 11 (.step 13 (.close 19))))) (.step 37 (.step 39 (.step 3 (.close 11))))) (.split 34 0 (.step 33 (.split 14 0 (.step 39 (.step 3 (.close 11))) (.step 13 (.step 20 (.close 3))))) (.step 39 (.step 5 (.step 11 (.step 17 (.step 15 (.close 19)))))))) (.split 30 0 (.step 45 (.split 34 0 (.step 74 (.step 3 (.step 11 (.step 13 (.close 19))))) (.step 45 (.step 4 (.step 11 (.step 13 (.step 15 (.close 17)))))))) (.step 33 (.split 14 0 (.step 33 (.step 20 (.step 11 (.close 23)))) (.step 13 (.step 20 (.step 5 (.step 11 (.close 17))))))))))) (.reuse 0)) (.reuse 1))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part3.excludes
end FiveColour.Packed.EnumerationChunks.Case52
