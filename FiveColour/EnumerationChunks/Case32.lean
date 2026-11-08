module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case32
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11592891989185051536311, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487664061762293317802547158855163062708886045696, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119212782810451907588865244637068870851712639713533435255352529493426176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 39 0 (.split 42 0 (.split 35 0 (.split 34 0 (.step 57 (.step 9 (.close 11))) (.step 9 (.step 52 (.step 15 (.close 20))))) (.step 29 (.step 53 (.step 20 (.step 13 (.step 15 (.step 20 (.close 52)))))))) (.step 62 (.step 9 (.step 39 (.close 13))))) (.split 42 0 (.split 35 0 (.split 34 0 (.step 27 (.step 57 (.step 19 (.step 38 (.close 42))))) (.step 38 (.step 9 (.step 17 (.step 15 (.step 19 (.close 20))))))) (.step 38 (.step 9 (.close 42)))) (.step 38 (.step 43 (.step 9 (.step 24 (.step 19 (.close 42)))))))) (.split 34 0 (.split 35 0 (.step 53 (.step 68 (.step 9 (.close 33)))) (.step 42 (.step 29 (.step 33 (.step 13 (.close 38)))))) (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 15 (.step 17 (.close 20)))))) (.step 38 (.close 9))) (.step 38 (.step 15 (.step 43 (.step 9 (.step 33 (.close 37))))))))) (.split 30 0 (.split 42 0 (.split 34 0 (.split 35 0 (.step 27 (.step 7 (.step 24 (.close 29)))) (.step 42 (.step 9 (.close 29)))) (.split 43 0 (.step 29 (.close 7)) (.step 7 (.step 9 (.close 11))))) (.split 43 0 (.split 34 0 (.step 29 (.close 7)) (.step 43 (.step 7 (.step 15 (.close 17))))) (.step 9 (.step 7 (.close 11))))) (.split 35 0 (.split 43 0 (.split 49 0 (.split 51 0 (.step 29 (.step 7 (.close 19))) (.step 7 (.step 24 (.close 19)))) (.step 53 (.step 43 (.step 20 (.close 27))))) (.step 7 (.step 9 (.step 7 (.close 11))))) (.step 42 (.step 7 (.close 15)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989002138654166870315303761317853260273393074176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 68 (.step 38 (.step 42 (.close 52)))) (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38))))))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 53 (.step 20 (.close 9)))) (.step 43 (.step 11 (.close 19)))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19))))))) (.split 30 0 (.split 35 0 (.split 39 0 (.split 43 0 (.step 68 (.step 27 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 27 (.close 7))) (.step 43 (.close 27))) (.step 7 (.close 27)))) (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 61 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 42 (.step 24 (.close 9)))) (.step 24 (.step 19 (.close 20))))) (.step 17 (.step 24 (.step 20 (.close 19))))) (.step 24 (.split 34 0 (.split 35 0 (.step 25 (.step 11 (.close 20))) (.step 19 (.step 24 (.close 20)))) (.step 17 (.step 24 (.step 20 (.close 19))))))) (.step 7 (.close 27)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450503775985069788518988594034136279929325617152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.step 11 (.step 53 (.step 24 (.step 19 (.close 42)))))) (.step 42 (.step 38 (.close 9)))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 38 (.close 9)))) (.split 34 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.step 38 (.step 11 (.close 17))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 49 0 (.step 68 (.step 27 (.close 7))) (.step 53 (.step 17 (.close 27)))) (.step 7 (.step 11 (.close 9)))) (.step 43 (.close 27))) (.step 7 (.close 27)))) (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 24 (.close 19))))) (.step 7 (.close 27)))) (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 20 (.close 9)))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 20 (.step 11 (.step 19 (.close 15))))))) (.step 7 (.close 27))) (.split 24 0 (.split 34 0 (.split 39 0 (.step 24 (.step 19 (.step 20 (.step 9 (.close 13))))) (.step 11 (.close 19))) (.step 24 (.step 19 (.step 20 (.close 11))))) (.split 35 0 (.split 39 0 (.step 7 (.step 19 (.close 20))) (.step 11 (.step 19 (.close 7)))) (.step 7 (.step 19 (.close 24))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119212782810451907588865244638462667426620803659879417647393052087549952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 57 (.close 19)))) (.step 42 (.step 27 (.step 52 (.step 20 (.step 19 (.close 38))))))) (.split 35 0 (.step 52 (.close 17)) (.split 39 0 (.step 52 (.step 15 (.close 17))) (.step 17 (.step 29 (.close 38)))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 42 (.close 13))) (.step 42 (.close 13))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.step 15 (.close 17)))) (.step 13 (.step 38 (.step 24 (.step 33 (.step 9 (.close 37))))))) (.step 38 (.step 9 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.close 7)) (.step 42 (.step 15 (.step 9 (.step 27 (.close 7)))))) (.split 35 0 (.step 52 (.close 17)) (.step 17 (.step 29 (.close 7))))) (.split 35 0 (.split 43 0 (.split 49 0 (.split 34 0 (.step 42 (.step 67 (.step 7 (.close 15)))) (.step 17 (.close 7))) (.step 17 (.step 7 (.close 19)))) (.step 11 (.close 7))) (.step 42 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989003532450741778479250107300245300795987197952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 61 (.step 43 (.step 42 (.step 13 (.step 15 (.close 19))))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24)))))) (.step 11 (.split 39 0 (.step 17 (.step 61 (.step 43 (.step 52 (.step 24 (.close 27)))))) (.step 27 (.step 7 (.step 17 (.close 19))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 74 (.split 72 0 (.step 61 (.step 7 (.step 13 (.close 19)))) (.step 24 (.step 20 (.step 7 (.close 19)))))) (.step 20 (.step 7 (.step 13 (.close 19))))) (.step 24 (.step 25 (.step 19 (.close 20))))) (.step 20 (.step 7 (.step 13 (.step 20 (.close 24))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940016528320451919740928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 35 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.step 15 (.close 20))))))) (.step 53 (.step 11 (.close 13)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 42 (.close 13))))) (.step 24 (.step 42 (.step 13 (.close 17))))) (.step 11 (.split 39 0 (.step 17 (.step 42 (.step 29 (.close 7)))) (.step 27 (.step 7 (.step 17 (.close 19))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 67 (.split 30 0 (.step 24 (.step 19 (.step 7 (.close 20)))) (.step 7 (.step 13 (.step 19 (.close 20)))))) (.step 19 (.step 7 (.step 13 (.close 20))))) (.step 24 (.step 19 (.step 25 (.close 20))))) (.step 19 (.step 7 (.step 13 (.close 24)))))))) (.split 22 0 (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 67 (.step 61 (.step 19 (.step 20 (.step 7 (.close 15)))))) (.step 19 (.step 7 (.step 13 (.close 20))))) (.step 24 (.step 19 (.step 20 (.close 7))))) (.step 19 (.step 7 (.step 13 (.close 20))))))) (.split 24 0 (.step 25 (.step 11 (.step 17 (.step 19 (.step 13 (.close 20)))))) (.step 11 (.step 17 (.step 19 (.step 7 (.step 15 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940016528320451919740928⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 67 (.step 24 (.step 15 (.close 13))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.close 20)))))) (.step 13 (.step 20 (.close 24)))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24)))))) (.step 11 (.split 39 0 (.step 17 (.split 42 0 (.split 59 0 (.step 43 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 19))))) (.step 27 (.step 7 (.close 15)))) (.step 7 (.step 24 (.step 15 (.close 19)))))) (.step 27 (.step 7 (.step 17 (.close 19))))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940016528320451919740928⟩
def references : Fin 4 → Box := ![Part0.root, Part1.root, Part2.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 30 0 (.split 39 0 (.split 34 0 (.step 62 (.step 9 (.step 20 (.close 13)))) (.step 43 (.step 15 (.step 9 (.close 13))))) (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38)))))) (.step 24 (.step 38 (.step 24 (.close 19)))))) (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 20 (.step 13 (.close 24))))))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19))))))) (.split 30 0 (.split 39 0 (.split 42 0 (.step 62 (.step 43 (.step 11 (.close 27)))) (.step 7 (.close 29))) (.split 35 0 (.step 27 (.close 7)) (.step 11 (.step 42 (.close 7))))) (.step 7 (.close 27)))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604503852411325511810907857737819975716944939658749411328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 34 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.split 63 0 (.split 39 0 (.step 57 (.step 13 (.close 17))) (.step 38 (.step 57 (.step 13 (.close 17))))) (.step 15 (.step 17 (.close 38)))) (.step 38 (.step 15 (.step 53 (.step 20 (.step 13 (.close 17)))))))) (.split 35 0 (.step 53 (.step 9 (.step 38 (.step 15 (.step 13 (.close 20)))))) (.split 39 0 (.split 43 0 (.step 38 (.close 13)) (.step 9 (.close 11))) (.step 9 (.close 38))))) (.split 39 0 (.split 42 0 (.step 62 (.split 43 0 (.step 66 (.close 24)) (.step 9 (.close 11)))) (.step 43 (.step 37 (.step 24 (.close 33))))) (.step 43 (.step 27 (.step 17 (.step 24 (.step 38 (.step 24 (.close 15))))))))) (.step 15 (.split 35 0 (.step 43 (.step 9 (.step 52 (.step 43 (.close 15))))) (.step 15 (.step 24 (.close 37)))))) (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 29 (.close 27))) (.step 62 (.step 9 (.step 17 (.step 24 (.close 15)))))) (.split 35 0 (.split 36 0 (.step 52 (.step 43 (.step 9 (.step 15 (.step 7 (.close 19)))))) (.step 9 (.step 29 (.close 7)))) (.step 9 (.step 29 (.close 7))))) (.split 34 0 (.step 53 (.step 9 (.step 43 (.step 42 (.step 17 (.step 7 (.close 15))))))) (.step 9 (.step 24 (.step 15 (.close 7))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989002138655496098311088677190757067333673418752⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 42 0 (.step 9 (.step 66 (.step 24 (.close 38)))) (.step 43 (.step 15 (.step 17 (.step 19 (.step 24 (.close 33))))))) (.step 43 (.step 27 (.step 17 (.step 38 (.step 24 (.close 15))))))) (.step 15 (.close 43))) (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 9 (.step 39 (.step 13 (.close 15))))) (.step 38 (.step 9 (.close 13)))) (.step 15 (.step 13 (.step 24 (.step 9 (.close 15)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.step 27 (.close 7)) (.step 17 (.step 7 (.close 24)))) (.step 17 (.step 29 (.close 7)))) (.step 17 (.step 24 (.step 7 (.close 15))))) (.step 17 (.step 24 (.close 27))))) (.step 17 (.split 24 0 (.step 24 (.step 9 (.step 15 (.close 19)))) (.step 24 (.step 7 (.step 24 (.close 27)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450503775986399016514773509907040086989605961728⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.step 53 (.step 9 (.step 17 (.step 24 (.close 15))))) (.step 9 (.step 24 (.step 15 (.step 24 (.close 13)))))) (.step 53 (.close 15))) (.step 15 (.step 38 (.step 9 (.step 17 (.step 15 (.close 19))))))) (.step 24 (.split 34 0 (.step 53 (.close 15)) (.step 15 (.step 13 (.step 24 (.step 9 (.close 15)))))))) (.split 30 0 (.split 34 0 (.step 53 (.step 27 (.close 7))) (.step 17 (.step 24 (.step 7 (.close 15))))) (.step 17 (.step 24 (.close 27))))) (.step 17 (.split 24 0 (.step 24 (.step 9 (.step 15 (.close 19)))) (.step 24 (.step 7 (.step 24 (.close 27))))))) (.split 22 0 (.step 17 (.split 24 0 (.step 24 (.step 9 (.step 15 (.close 19)))) (.step 24 (.step 7 (.step 24 (.close 27)))))) (.step 24 (.step 7 (.close 19)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119212782810451907588865244637068870851713907364133663484754026196631552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 43 (.step 33 (.close 38))))) (.split 42 0 (.step 52 (.step 43 (.step 11 (.step 19 (.close 38))))) (.step 43 (.step 11 (.step 13 (.close 19)))))) (.step 15 (.split 35 0 (.step 52 (.close 17)) (.step 15 (.close 17))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.split 42 0 (.step 42 (.step 33 (.step 9 (.step 13 (.close 24))))) (.step 33 (.close 24)))) (.split 36 0 (.step 42 (.step 29 (.step 33 (.step 13 (.close 38))))) (.step 33 (.step 24 (.close 13))))) (.step 15 (.split 35 0 (.split 36 0 (.step 52 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 15 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 43 0 (.split 50 0 (.split 35 0 (.split 51 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 19)))) (.step 29 (.close 7))) (.step 52 (.step 29 (.close 7)))) (.step 7 (.step 9 (.step 7 (.close 11))))) (.step 7 (.step 15 (.step 7 (.close 17))))) (.step 7 (.step 27 (.step 19 (.close 24)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989002138654166871582954361546082661770096279552⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 13 (.close 20)))))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 70 (.step 24 (.step 11 (.step 25 (.close 13)))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))))) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 33 (.step 20 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))) (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 9 (.close 24))))) (.step 24 (.step 19 (.step 13 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450503775985069789786639194262365681426028822528⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.step 20 (.close 24))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.close 19))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))) (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 24 (.close 19))))) (.step 24 (.close 19)))))) (.split 22 0 (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.step 9 (.close 24))))) (.step 24 (.close 19))))) (.split 24 0 (.step 25 (.step 17 (.step 19 (.step 11 (.step 13 (.close 20)))))) (.step 7 (.close 19)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644697950585540244757721948622946304⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 15 (.step 11 (.step 13 (.close 17)))) (.step 17 (.step 13 (.close 11)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.split 49 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15))) (.step 15 (.step 13 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 11 (.step 17 (.close 13))))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.split 30 0 (.split 35 0 (.split 36 0 (.split 17 0 (.split 34 0 (.split 43 0 (.split 50 0 (.step 17 (.close 7)) (.step 27 (.step 7 (.close 15)))) (.step 11 (.close 7))) (.step 17 (.close 7))) (.step 11 (.step 17 (.close 7)))) (.step 17 (.step 7 (.close 15)))) (.step 17 (.step 15 (.step 7 (.close 17))))) (.step 17 (.step 7 (.close 15))))) (.step 17 (.split 17 0 (.step 17 (.split 24 0 (.step 15 (.step 17 (.close 13))) (.step 7 (.step 15 (.close 17))))) (.step 17 (.close 13)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456117661529008903290880⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 15 (.step 11 (.close 13))))) (.step 24 (.step 15 (.step 17 (.close 13))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 9 (.step 24 (.step 15 (.step 17 (.close 7)))))) (.step 9 (.step 17 (.step 15 (.step 7 (.close 17)))))) (.step 9 (.step 15 (.close 7)))) (.step 17 (.step 9 (.step 15 (.close 7)))))) (.step 17 (.split 24 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.close 7))))) (.step 17 (.split 17 0 (.step 17 (.split 24 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.close 7)))) (.step 17 (.close 13))))) (.step 17 (.close 15)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604503852411325511809578629742035059845194054103075913728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 34 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.step 9 (.step 11 (.close 7))) (.step 9 (.step 7 (.close 11))))) (.split 35 0 (.step 53 (.step 9 (.close 7))) (.split 39 0 (.split 43 0 (.step 38 (.close 7)) (.step 7 (.close 9))) (.step 9 (.close 38))))) (.split 39 0 (.split 42 0 (.step 62 (.split 43 0 (.step 68 (.step 9 (.close 7))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 43 (.step 27 (.step 11 (.close 7)))))) (.step 15 (.split 35 0 (.split 22 0 (.step 9 (.step 52 (.step 43 (.close 7)))) (.step 7 (.close 9))) (.split 39 0 (.step 29 (.step 38 (.split 36 0 (.step 9 (.close 7)) (.step 7 (.close 9))))) (.step 9 (.step 7 (.close 11))))))) (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 29 (.step 7 (.step 9 (.close 11))))) (.step 62 (.step 9 (.close 11)))) (.split 35 0 (.split 36 0 (.step 52 (.step 43 (.close 9))) (.step 9 (.step 7 (.close 11)))) (.step 9 (.close 11)))) (.split 34 0 (.step 53 (.step 9 (.step 24 (.step 27 (.close 7))))) (.step 9 (.step 7 (.close 11)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1393796574908163946345983544962028274712576, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940017681241956526587904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 15 (.split 42 0 (.step 27 (.step 11 (.close 7))) (.step 9 (.step 11 (.close 7))))) (.step 24 (.step 11 (.close 7)))) (.split 36 0 (.split 42 0 (.split 22 0 (.step 15 (.step 9 (.step 7 (.close 11)))) (.step 11 (.close 7))) (.step 15 (.step 24 (.close 9)))) (.step 15 (.step 29 (.step 38 (.step 24 (.step 9 (.close 7)))))))) (.split 35 0 (.split 36 0 (.step 24 (.step 9 (.step 11 (.close 7)))) (.step 15 (.step 7 (.step 9 (.close 11))))) (.step 15 (.step 29 (.step 38 (.step 43 (.step 11 (.step 7 (.close 9))))))))) (.split 17 0 (.step 15 (.step 24 (.split 34 0 (.split 35 0 (.step 53 (.step 27 (.step 24 (.close 9)))) (.step 38 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))))) (.step 11 (.close 7)))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 17 0 (.step 52 (.step 11 (.close 9))) (.step 11 (.close 7))) (.step 11 (.close 9))) (.step 11 (.close 9))) (.step 11 (.step 7 (.close 9))))) (.split 17 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 7)) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940017681241956526587904⟩
def references : Fin 2 → Box := ![Part16.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 42 0 (.step 9 (.step 11 (.close 7))) (.step 7 (.close 9))) (.step 43 (.step 27 (.step 11 (.close 7))))) (.step 7 (.step 15 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.close 7)) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.split 30 0 (.step 24 (.split 24 0 (.step 7 (.step 9 (.close 11))) (.step 11 (.close 7)))) (.step 7 (.close 9)))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.step 27 (.step 11 (.close 7))) (.step 7 (.close 9))) (.step 53 (.close 7))) (.step 7 (.step 15 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 34 0 (.step 53 (.step 11 (.step 7 (.close 9)))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.split 30 0 (.step 24 (.split 24 0 (.step 7 (.step 9 (.close 11))) (.step 11 (.close 7)))) (.step 7 (.close 9)))) (.split 22 0 (.split 30 0 (.step 24 (.split 24 0 (.step 7 (.step 9 (.close 11))) (.step 11 (.close 7)))) (.step 7 (.close 9))) (.step 24 (.step 7 (.close 11))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1329227995784915874056728565960933376, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450503775986399016514773509908193008494212808704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 22 0 (.split 36 0 (.split 49 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 11))) (.step 9 (.close 7))) (.split 39 0 (.split 36 0 (.split 42 0 (.step 62 (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 62 (.step 9 (.step 7 (.step 9 (.close 11))))))) (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 7 (.close 11))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 9 (.close 7)))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.close 7)) (.step 9 (.close 7))) (.step 15 (.close 7))) (.step 9 (.step 7 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.step 9 (.split 22 0 (.step 9 (.close 7)) (.step 7 (.close 9)))) (.step 24 (.step 9 (.close 7)))) (.step 29 (.step 57 (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 29 (.step 15 (.close 7))))) (.split 30 0 (.split 34 0 (.split 39 0 (.split 58 0 (.step 9 (.step 7 (.close 11))) (.split 16 0 (.step 9 (.step 7 (.close 11))) (.step 11 (.close 9)))) (.split 58 0 (.split 16 0 (.step 9 (.step 7 (.close 11))) (.step 11 (.close 9))) (.step 27 (.close 9)))) (.step 9 (.close 11))) (.step 29 (.close 9)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1267650600229382323002383794176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644697950585540245910643453229793280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 34 0 (.split 35 0 (.split 17 0 (.split 22 0 (.split 39 0 (.split 42 0 (.step 52 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 52 (.step 43 (.step 27 (.step 11 (.close 7)))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.split 17 0 (.split 36 0 (.split 22 0 (.split 39 0 (.split 30 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 9 (.close 38))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.close 15))) (.split 35 0 (.split 17 0 (.step 52 (.split 22 0 (.split 34 0 (.step 52 (.step 9 (.step 27 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 11)))) (.step 24 (.close 11))) (.step 29 (.step 7 (.close 9))))) (.split 17 0 (.split 24 0 (.step 7 (.step 9 (.close 11))) (.step 24 (.step 11 (.close 7)))) (.step 7 (.close 11)))) (.split 16 0 (.split 17 0 (.split 30 0 (.step 15 (.step 7 (.close 11))) (.step 15 (.step 7 (.close 11)))) (.step 24 (.step 7 (.close 11)))) (.step 24 (.close 17)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def references : Fin 3 → Box := ![Part18.root, Part19.root, Part20.root]
def proof : Chunks.Proof 3 := (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 24 0 (.split 30 0 (.split 36 0 (.split 63 0 (.split 16 0 (.step 15 (.step 7 (.close 11))) (.split 34 0 (.split 39 0 (.step 15 (.step 7 (.close 11))) (.step 11 (.close 7))) (.step 7 (.close 9)))) (.step 15 (.close 11))) (.step 15 (.close 7))) (.split 34 0 (.split 36 0 (.split 39 0 (.step 15 (.close 7)) (.step 11 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.step 29 (.close 9)) (.step 11 (.close 9))))))) (.split 12 0 (.reuse 2) (.run (.split 14 0 (.split 24 0 (.split 30 0 (.split 36 0 (.split 63 0 (.split 16 0 (.step 9 (.step 15 (.close 7))) (.split 35 0 (.step 24 (.step 9 (.close 7))) (.step 7 (.close 9)))) (.step 15 (.close 7))) (.step 15 (.close 7))) (.split 34 0 (.split 36 0 (.split 39 0 (.split 49 0 (.split 42 0 (.split 43 0 (.step 15 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 15 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 16 0 (.step 29 (.close 9)) (.step 11 (.step 7 (.close 9))))) (.step 15 (.step 7 (.step 9 (.close 11))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def references : Fin 4 → Box := ![Part7.root, Part10.root, Part15.root, Part21.root]
def proof : Chunks.Proof 4 := (.split 6 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 24 0 (.step 15 (.split 34 0 (.split 35 0 (.split 22 0 (.step 52 (.split 30 0 (.step 9 (.step 15 (.close 17))) (.step 24 (.step 9 (.close 15))))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 24 (.step 15 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 22 0 (.step 15 (.step 9 (.step 17 (.step 7 (.close 15))))) (.step 17 (.close 7))) (.step 17 (.step 9 (.step 15 (.close 17))))) (.step 17 (.step 9 (.step 15 (.close 7)))))) (.step 17 (.step 15 (.step 17 (.step 13 (.step 7 (.step 9 (.close 15)))))))) (.step 17 (.split 17 0 (.step 17 (.step 15 (.step 17 (.step 13 (.step 7 (.step 9 (.close 15))))))) (.step 17 (.close 11)))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part10.excludes
  · exact Part15.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part22

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part22.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case32

namespace FiveColour.Packed.EnumerationChunks.Projected.Case32
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 276 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 276 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 276 0).upper i := by decide +kernel
lemma budget_model : (⟨11592891989185051536311, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487664061762293317802547158855163062708886045696, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 276), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11592891989185051536311, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487664061762293317802547158855163062708886045696, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 276) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 276 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 276 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 276) (Archive.root 276) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 276 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 276 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case32

namespace FiveColour.Packed.EnumerationChunks.Case32
def root : Box := Archive.root 276
def families : Fin 78 → List Cut := Enumeration.families 276
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case32.original_covered points
end FiveColour.Packed.EnumerationChunks.Case32
