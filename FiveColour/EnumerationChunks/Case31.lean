module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case31
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11592891989185001204471, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634596862352413225127988347882672294734774404096, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780162777158844713765706750419802674778878991862545798477872938275045376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 39 0 (.split 42 0 (.split 35 0 (.split 34 0 (.step 57 (.step 9 (.close 11))) (.step 9 (.step 52 (.step 15 (.close 20))))) (.step 29 (.step 53 (.step 20 (.step 13 (.step 15 (.step 20 (.close 52)))))))) (.step 62 (.step 9 (.step 39 (.close 13))))) (.split 42 0 (.split 35 0 (.split 34 0 (.step 27 (.step 57 (.step 19 (.step 38 (.close 42))))) (.step 38 (.step 9 (.step 17 (.step 15 (.step 19 (.close 20))))))) (.step 38 (.step 9 (.close 42)))) (.step 38 (.step 43 (.step 9 (.step 24 (.step 19 (.close 42)))))))) (.split 34 0 (.split 35 0 (.step 53 (.step 68 (.step 9 (.close 33)))) (.step 42 (.step 29 (.step 33 (.step 13 (.close 38)))))) (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 15 (.step 17 (.close 20)))))) (.step 38 (.close 9))) (.step 38 (.step 15 (.step 43 (.step 9 (.step 33 (.close 37))))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 9 (.step 27 (.step 7 (.close 29)))) (.step 29 (.step 7 (.step 9 (.close 27))))) (.step 29 (.step 7 (.close 9)))) (.split 35 0 (.split 36 0 (.step 15 (.step 9 (.step 29 (.close 7)))) (.step 7 (.close 29))) (.step 29 (.close 7)))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 53 (.step 9 (.step 24 (.step 27 (.close 7))))) (.step 38 (.close 7))) (.step 7 (.step 27 (.close 29)))) (.step 7 (.step 29 (.close 7)))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494784872458094036667452773681075780682174693376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 68 (.step 38 (.step 42 (.close 52)))) (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38))))))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 53 (.step 20 (.close 9)))) (.step 43 (.step 11 (.close 19)))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 29 (.close 7))) (.split 36 0 (.step 27 (.close 29)) (.step 7 (.close 27)))) (.step 7 (.step 29 (.close 7)))) (.step 7 (.close 27)))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 61 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 42 (.step 24 (.close 9)))) (.step 24 (.step 19 (.close 20))))) (.step 17 (.step 24 (.step 20 (.close 19))))) (.step 24 (.split 34 0 (.split 35 0 (.step 25 (.step 11 (.close 20))) (.step 19 (.step 24 (.close 20)))) (.step 17 (.step 24 (.step 20 (.close 19))))))) (.step 7 (.close 27)))))
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956286509788996954871137606397358800338107236352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.step 11 (.step 53 (.step 24 (.step 19 (.close 42)))))) (.step 42 (.step 38 (.close 9)))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 38 (.close 9)))) (.split 34 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.step 38 (.step 11 (.close 17))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 27 (.step 29 (.close 7))) (.step 7 (.close 27))) (.step 7 (.step 29 (.close 7)))) (.step 7 (.close 27)))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 24 (.close 19))))) (.step 7 (.close 27)))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 20 (.close 9)))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 20 (.step 11 (.step 19 (.close 15))))))) (.step 7 (.close 27))) (.split 26 0 (.split 34 0 (.split 39 0 (.step 24 (.step 19 (.step 20 (.step 9 (.close 13))))) (.step 11 (.close 19))) (.step 24 (.step 19 (.step 20 (.close 11))))) (.step 24 (.step 29 (.close 19)))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956286509788996954871137606397358800338107236352⟩
def references : Fin 3 → Box := ![Part0.root, Part1.root, Part2.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 39 0 (.split 34 0 (.step 62 (.step 9 (.step 20 (.close 13)))) (.step 43 (.step 15 (.step 9 (.close 13))))) (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38)))))) (.step 24 (.step 38 (.step 24 (.close 19)))))) (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 20 (.step 13 (.close 24))))))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19))))))) (.split 34 0 (.split 35 0 (.split 30 0 (.step 27 (.step 29 (.close 7))) (.step 7 (.step 24 (.close 27)))) (.step 75 (.step 27 (.close 7)))) (.step 7 (.step 29 (.close 7))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780162777158844713765706750421196471353787155808891780869913460869169152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 57 (.close 19)))) (.step 42 (.step 27 (.step 52 (.step 20 (.step 19 (.close 38))))))) (.split 35 0 (.step 52 (.close 17)) (.split 39 0 (.step 52 (.step 15 (.close 17))) (.step 17 (.step 29 (.close 38)))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 42 (.close 13))) (.step 42 (.close 13))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.step 15 (.close 17)))) (.step 13 (.step 38 (.step 24 (.step 33 (.step 9 (.close 37))))))) (.step 38 (.step 9 (.close 17)))))) (.split 34 0 (.split 30 0 (.split 35 0 (.step 27 (.step 15 (.close 29))) (.split 36 0 (.step 27 (.step 15 (.close 29))) (.step 29 (.step 7 (.close 17))))) (.split 35 0 (.split 36 0 (.step 27 (.step 15 (.step 29 (.close 7)))) (.step 38 (.step 7 (.step 15 (.close 24))))) (.step 38 (.close 7)))) (.split 39 0 (.split 35 0 (.split 43 0 (.step 43 (.step 29 (.close 7))) (.step 7 (.close 9))) (.step 29 (.close 7))) (.step 11 (.step 17 (.step 38 (.step 27 (.step 7 (.step 15 (.close 17)))))))))))
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
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494786266254668944831399119663467821204768817152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 61 (.step 43 (.step 42 (.step 13 (.step 15 (.close 19))))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24)))))) (.step 11 (.step 74 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 17 (.close 27))) (.step 43 (.step 27 (.close 7)))) (.step 7 (.close 17))) (.step 7 (.step 17 (.step 24 (.close 19)))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 74 (.step 24 (.step 74 (.step 43 (.step 13 (.close 15)))))) (.step 24 (.step 20 (.close 13)))) (.step 24 (.step 13 (.step 7 (.close 20)))))))))
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
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903585571863035083952379750840860701360128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 35 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.step 15 (.close 20))))))) (.step 53 (.step 11 (.close 13)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 42 (.close 13))))) (.step 24 (.step 42 (.step 13 (.close 17))))) (.step 11 (.step 67 (.step 38 (.step 24 (.step 15 (.close 7))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 24 (.step 19 (.step 43 (.step 13 (.close 20)))))) (.step 24 (.step 19 (.close 13)))) (.step 24 (.step 13 (.step 7 (.close 19)))))))) (.split 22 0 (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 24 (.step 19 (.step 20 (.close 7))))) (.step 24 (.step 19 (.close 13)))) (.step 24 (.step 13 (.step 7 (.close 19))))))) (.split 26 0 (.step 25 (.step 11 (.step 17 (.step 19 (.step 13 (.close 20)))))) (.step 11 (.step 17 (.step 19 (.step 7 (.step 15 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929571175587451509467240083921714619356113870583094593283889032473964858676932872124426197401600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 22 0 (.split 39 0 (.split 42 0 (.step 9 (.split 35 0 (.step 66 (.step 20 (.step 24 (.close 53)))) (.step 15 (.step 53 (.step 17 (.close 20)))))) (.step 62 (.step 29 (.split 36 0 (.step 15 (.step 24 (.step 17 (.close 13)))) (.step 37 (.step 20 (.step 19 (.step 33 (.close 38))))))))) (.split 42 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 72 0 (.step 27 (.step 17 (.step 19 (.close 20)))) (.step 9 (.step 38 (.step 17 (.close 20))))) (.step 9 (.step 17 (.step 38 (.step 19 (.close 42)))))) (.step 9 (.step 15 (.step 17 (.step 19 (.close 38)))))) (.step 9 (.step 38 (.close 13)))) (.step 9 (.step 38 (.step 24 (.step 15 (.step 43 (.close 17)))))))) (.split 39 0 (.split 42 0 (.step 62 (.split 43 0 (.step 17 (.step 24 (.close 15))) (.step 9 (.close 11)))) (.step 43 (.step 66 (.step 24 (.close 33))))) (.step 62 (.step 9 (.step 17 (.step 19 (.step 15 (.close 20)))))))) (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20))))) (.step 24 (.step 9 (.step 15 (.step 13 (.close 19)))))) (.step 43 (.close 15))) (.split 36 0 (.split 42 0 (.step 15 (.step 9 (.step 13 (.close 19)))) (.step 15 (.step 19 (.close 20)))) (.step 15 (.step 20 (.step 19 (.close 37))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494784872459423264663237689553979587742455037952⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 26 0 (.split 30 0 (.reuse 0) (.run (.split 34 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 53 (.step 9 (.step 38 (.step 15 (.step 13 (.close 20)))))) (.split 39 0 (.split 43 0 (.step 38 (.close 13)) (.step 9 (.close 11))) (.step 9 (.close 38)))) (.step 24 (.split 35 0 (.step 24 (.step 9 (.step 43 (.close 15)))) (.step 38 (.step 9 (.close 13)))))) (.step 24 (.split 35 0 (.step 24 (.step 9 (.step 39 (.step 13 (.close 15))))) (.step 38 (.step 9 (.close 13)))))) (.split 17 0 (.step 15 (.step 38 (.step 43 (.step 9 (.step 13 (.close 15)))))) (.step 24 (.step 9 (.step 13 (.close 15)))))))) (.run (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.step 15 (.step 29 (.step 13 (.step 17 (.close 27))))) (.step 38 (.step 15 (.step 29 (.close 7)))))) (.step 27 (.step 15 (.step 9 (.step 27 (.close 7)))))) (.step 57 (.step 29 (.close 7)))) (.split 22 0 (.split 30 0 (.step 29 (.step 7 (.step 9 (.step 15 (.step 17 (.close 27)))))) (.step 29 (.step 7 (.close 17)))) (.step 29 (.step 7 (.close 17))))) (.step 15 (.step 24 (.step 27 (.close 29))))) (.split 22 0 (.split 34 0 (.split 35 0 (.split 30 0 (.split 36 0 (.step 9 (.step 27 (.close 7))) (.step 29 (.close 7))) (.step 24 (.step 27 (.step 7 (.step 15 (.close 17)))))) (.step 29 (.step 7 (.close 17)))) (.step 15 (.step 7 (.close 19)))) (.step 75 (.step 7 (.step 15 (.step 17 (.close 19)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956286509790326182866922522270262607398387580928⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 22 0 (.split 35 0 (.split 42 0 (.step 53 (.step 9 (.step 17 (.step 24 (.close 15))))) (.step 9 (.step 24 (.step 15 (.step 24 (.close 13)))))) (.step 53 (.close 15))) (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))) (.step 43 (.step 38 (.step 24 (.close 15))))) (.step 24 (.split 34 0 (.step 53 (.close 15)) (.step 15 (.step 13 (.step 24 (.step 9 (.close 15)))))))) (.split 22 0 (.split 34 0 (.split 35 0 (.split 30 0 (.split 36 0 (.step 9 (.step 27 (.close 7))) (.step 29 (.close 7))) (.step 24 (.step 27 (.step 7 (.step 15 (.close 17)))))) (.step 29 (.step 7 (.close 17)))) (.step 15 (.step 7 (.close 19)))) (.step 38 (.step 7 (.step 17 (.close 24)))))) (.split 22 0 (.split 34 0 (.step 17 (.step 24 (.split 36 0 (.step 24 (.step 9 (.step 38 (.step 20 (.step 7 (.step 15 (.close 19))))))) (.step 24 (.close 7))))) (.step 24 (.step 7 (.step 13 (.close 15))))) (.step 24 (.step 17 (.step 24 (.close 19))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901091030868868252654647920981704704⟩
def references : Fin 5 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root, Part9.root]
def proof : Chunks.Proof 5 := (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 26 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 67 (.step 24 (.step 15 (.close 13))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.close 20)))))) (.step 13 (.step 20 (.close 24)))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24)))))) (.step 11 (.split 30 0 (.step 75 (.split 34 0 (.split 35 0 (.step 24 (.step 17 (.close 27))) (.step 43 (.step 27 (.close 7)))) (.step 17 (.step 7 (.close 15))))) (.step 24 (.step 17 (.close 29)))))))) (.reuse 2)) (.reuse 3))) (.split 14 0 (.reuse 4) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 26 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 52 (.split 30 0 (.step 9 (.step 15 (.close 17))) (.step 24 (.step 9 (.close 15))))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 24 (.step 15 (.close 17))))) (.step 15 (.step 17 (.step 7 (.step 17 (.close 29))))))) (.split 22 0 (.step 15 (.step 17 (.step 13 (.step 7 (.step 9 (.close 15)))))) (.step 17 (.close 7)))) (.split 17 0 (.split 22 0 (.step 15 (.step 17 (.step 13 (.step 7 (.step 9 (.close 15)))))) (.step 17 (.close 7))) (.step 17 (.step 7 (.close 13))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780162777158844713765706750419802674778880259513146026707274434978250752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 43 (.step 33 (.close 38))))) (.split 42 0 (.step 52 (.step 43 (.step 11 (.step 19 (.close 38))))) (.step 43 (.step 11 (.step 13 (.close 19)))))) (.step 15 (.split 35 0 (.step 52 (.close 17)) (.step 15 (.close 17))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.split 42 0 (.step 42 (.step 33 (.step 9 (.step 13 (.close 24))))) (.step 33 (.close 24)))) (.split 36 0 (.step 42 (.step 29 (.step 33 (.step 13 (.close 38))))) (.step 33 (.step 24 (.close 13))))) (.step 15 (.split 35 0 (.split 36 0 (.step 52 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 15 (.close 17)))))) (.split 34 0 (.split 35 0 (.split 30 0 (.split 39 0 (.step 52 (.step 7 (.step 9 (.close 20)))) (.step 27 (.step 9 (.step 29 (.close 7))))) (.step 7 (.step 24 (.close 29)))) (.split 30 0 (.split 36 0 (.split 39 0 (.step 29 (.close 7)) (.step 27 (.step 9 (.close 29)))) (.step 7 (.step 27 (.close 29)))) (.step 7 (.step 27 (.close 29))))) (.step 7 (.step 15 (.step 7 (.close 17)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494784872458094037935103373909305182178877898752⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 13 (.close 20)))))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 70 (.step 24 (.step 11 (.step 25 (.close 13)))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))))) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 33 (.step 20 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))) (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 9 (.close 24))))) (.step 24 (.step 19 (.step 13 (.close 20))))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956286509788996956138788206625588201834810441728⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.step 20 (.close 24))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.close 19))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 7 (.close 27))) (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 24 (.close 19))))) (.step 24 (.close 19)))))) (.split 22 0 (.step 7 (.step 17 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.step 9 (.close 24))))) (.step 24 (.close 19))))) (.split 30 0 (.step 17 (.split 35 0 (.step 25 (.step 11 (.step 19 (.step 7 (.close 13))))) (.step 7 (.step 19 (.close 9))))) (.step 7 (.step 19 (.step 13 (.step 20 (.step 15 (.step 9 (.close 24))))))))))))
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
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298519468480884049417684910080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 26 0 (.split 17 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 15 (.step 11 (.close 13))))) (.step 24 (.step 15 (.step 17 (.close 13))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.split 30 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.close 7)) (.step 9 (.step 17 (.close 15)))) (.step 15 (.step 7 (.close 17)))) (.step 15 (.step 17 (.close 7)))) (.step 15 (.step 7 (.close 17))))) (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.step 17 (.step 29 (.step 13 (.close 15))))) (.step 17 (.step 7 (.close 13)))) (.step 17 (.close 7))) (.step 17 (.step 7 (.close 13))))) (.split 16 0 (.split 30 0 (.step 15 (.step 7 (.step 11 (.close 13)))) (.step 15 (.step 11 (.close 13)))) (.step 17 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578005567743895544151599136906785469385345401479969636352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 9 (.split 35 0 (.split 36 0 (.step 9 (.close 11)) (.step 9 (.close 7))) (.step 9 (.close 7)))) (.step 42 (.step 27 (.step 9 (.step 7 (.close 11)))))) (.split 35 0 (.step 9 (.split 36 0 (.step 17 (.step 9 (.close 7))) (.step 7 (.step 9 (.close 11))))) (.split 36 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 29 (.step 38 (.step 43 (.close 15))))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 53 (.step 7 (.close 9))) (.step 42 (.close 7))) (.step 42 (.close 7))) (.step 7 (.step 38 (.step 7 (.close 9)))))) (.split 30 0 (.split 43 0 (.split 49 0 (.split 39 0 (.split 36 0 (.split 54 0 (.step 11 (.close 7)) (.step 9 (.close 11))) (.step 74 (.step 15 (.step 7 (.close 9))))) (.step 9 (.step 11 (.close 7)))) (.step 17 (.close 9))) (.step 11 (.step 7 (.close 9)))) (.split 43 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 52 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 42 (.step 7 (.close 11)))) (.step 17 (.close 7))) (.step 11 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410680693917109639410080704258131627115475308159019515904⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.split 26 0 (.reuse 0) (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 11 (.step 7 (.close 9)))) (.step 29 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.split 14 0 (.split 30 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7)))) (.split 14 0 (.split 30 0 (.step 29 (.step 7 (.close 9))) (.step 29 (.step 7 (.close 9)))) (.step 11 (.close 29)))) (.split 14 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.step 17 (.step 11 (.step 9 (.close 11)))))) (.step 11 (.step 17 (.close 29))))))) (.run (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 39 0 (.split 34 0 (.split 35 0 (.step 9 (.step 11 (.close 7))) (.step 24 (.step 9 (.close 7)))) (.step 7 (.step 17 (.step 11 (.step 7 (.close 15)))))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.split 35 0 (.split 49 0 (.split 50 0 (.split 14 0 (.step 7 (.close 9)) (.step 11 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.step 11 (.step 29 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903585571863035085161305570455489876066304⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 34 0 (.split 39 0 (.step 74 (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 7 (.step 17 (.step 11 (.step 7 (.close 15)))))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.split 35 0 (.split 49 0 (.split 50 0 (.split 14 0 (.step 7 (.close 9)) (.step 11 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 11 (.close 7))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 34 0 (.split 39 0 (.split 35 0 (.step 9 (.step 11 (.close 7))) (.step 24 (.step 9 (.close 7)))) (.step 11 (.close 7))) (.step 7 (.step 17 (.step 11 (.step 7 (.close 15)))))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.split 35 0 (.split 49 0 (.step 67 (.close 7)) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 11 (.close 7))) (.split 22 0 (.step 11 (.close 7)) (.split 35 0 (.step 25 (.step 11 (.close 7))) (.step 7 (.close 11)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1267651809154049016126951653376, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 39 0 (.step 52 (.step 7 (.close 9))) (.split 42 0 (.step 27 (.step 42 (.step 52 (.step 7 (.close 9))))) (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 9 (.step 42 (.step 9 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 15 (.step 7 (.step 9 (.close 11)))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 27 (.step 9 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 29 (.step 7 (.close 9)))) (.step 7 (.step 15 (.close 11)))) (.step 7 (.step 24 (.close 11)))) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.step 7 (.step 11 (.close 7)))) (.step 17 (.step 15 (.step 17 (.step 66 (.step 7 (.close 9))))))) (.split 26 0 (.step 17 (.step 9 (.step 15 (.step 17 (.close 7))))) (.step 66 (.step 17 (.step 9 (.close 7)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 7 (.close 11))) (.step 17 (.step 11 (.close 7)))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 9 (.step 24 (.step 9 (.close 15))))) (.split 17 0 (.step 9 (.step 24 (.split 34 0 (.split 35 0 (.step 9 (.step 7 (.close 11))) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 15))))))) (.step 17 (.step 24 (.close 7))))) (.step 9 (.step 29 (.step 7 (.close 11))))) (.split 17 0 (.split 22 0 (.step 9 (.step 17 (.step 24 (.split 26 0 (.step 24 (.close 9)) (.step 9 (.step 7 (.close 11))))))) (.step 17 (.step 24 (.close 7)))) (.step 17 (.step 24 (.step 7 (.close 11)))))) (.split 26 0 (.step 17 (.step 9 (.step 15 (.step 9 (.step 17 (.close 7)))))) (.step 66 (.step 11 (.step 9 (.close 7)))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def references : Fin 4 → Box := ![Part10.root, Part13.root, Part14.root, Part19.root]
def proof : Chunks.Proof 4 := (.split 8 0 (.split 10 0 (.reuse 0) (.split 12 0 (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 26 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 15 (.step 11 (.step 13 (.close 17)))) (.step 17 (.step 13 (.close 11)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.split 49 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15))) (.step 15 (.step 13 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 11 (.step 17 (.close 13))))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.split 17 0 (.step 15 (.step 17 (.close 7))) (.step 17 (.step 7 (.close 15))))) (.step 17 (.split 17 0 (.step 17 (.step 15 (.step 17 (.step 66 (.step 7 (.close 13)))))) (.step 17 (.close 13))))))) (.reuse 2))) (.reuse 3))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part20.excludes
end FiveColour.Packed.EnumerationChunks.Case31
