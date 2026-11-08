module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case51
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146442049494837159539922807610671104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929571175587451509467240083920029622689416954099350228214104388088293483533177370409622017409024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 39 0 (.split 42 0 (.split 35 0 (.split 63 0 (.step 57 (.step 9 (.close 11))) (.step 52 (.step 57 (.step 9 (.close 11))))) (.step 53 (.step 9 (.step 54 (.step 52 (.step 20 (.close 57))))))) (.step 62 (.step 9 (.step 39 (.close 13))))) (.split 42 0 (.split 35 0 (.split 63 0 (.split 64 0 (.step 57 (.step 9 (.step 11 (.close 27)))) (.step 27 (.step 42 (.step 20 (.step 24 (.close 38)))))) (.step 27 (.step 52 (.step 57 (.step 19 (.step 38 (.close 42))))))) (.step 42 (.step 9 (.close 38)))) (.step 62 (.step 38 (.step 29 (.step 43 (.step 19 (.close 42)))))))) (.split 35 0 (.split 39 0 (.split 42 0 (.step 52 (.step 29 (.step 57 (.close 15)))) (.step 15 (.step 52 (.step 43 (.step 9 (.step 33 (.close 39))))))) (.split 42 0 (.split 43 0 (.step 38 (.split 51 0 (.step 17 (.step 15 (.step 19 (.step 20 (.close 39))))) (.step 43 (.step 13 (.step 17 (.close 19)))))) (.step 9 (.step 27 (.step 9 (.close 11))))) (.step 43 (.step 15 (.step 24 (.step 17 (.close 27))))))) (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 29 (.step 38 (.step 24 (.step 33 (.close 39))))))) (.step 38 (.close 9))) (.split 42 0 (.step 43 (.step 15 (.step 9 (.step 38 (.step 33 (.close 37)))))) (.step 29 (.step 38 (.step 37 (.step 39 (.close 19))))))))))
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
def root : Box := ⟨1684996666696914987166688442938726917102321526408785780070049382400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910582593293751145845159440885919526397176446976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 42 0 (.step 62 (.step 27 (.step 20 (.step 13 (.close 19))))) (.step 68 (.step 29 (.step 33 (.step 38 (.step 24 (.step 13 (.step 24 (.close 39))))))))) (.split 42 0 (.step 42 (.step 27 (.step 62 (.step 13 (.close 19))))) (.step 43 (.step 11 (.step 19 (.step 13 (.close 20))))))) (.split 35 0 (.split 36 0 (.step 43 (.step 62 (.step 9 (.step 17 (.step 15 (.close 19)))))) (.step 43 (.close 15))) (.step 43 (.step 38 (.step 66 (.step 39 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 53 (.step 62 (.step 9 (.close 13)))) (.step 68 (.step 33 (.step 24 (.step 9 (.close 39)))))) (.step 24 (.step 42 (.close 19)))) (.split 36 0 (.step 42 (.close 19)) (.step 33 (.step 19 (.step 24 (.close 20)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 68 (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 17 (.step 24 (.step 19 (.close 20))))) (.step 38 (.step 43 (.step 15 (.step 24 (.close 25)))))) (.step 33 (.close 38))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910582593293751145845159440885919526397176446976⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 22 0 (.split 30 0 (.reuse 0) (.run (.split 34 0 (.split 35 0 (.split 39 0 (.step 53 (.step 68 (.step 9 (.close 39)))) (.split 42 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.step 43 (.step 27 (.step 24 (.close 19)))))) (.split 39 0 (.split 43 0 (.split 50 0 (.step 38 (.step 13 (.close 19))) (.step 53 (.step 13 (.step 19 (.close 24))))) (.split 36 0 (.step 42 (.step 9 (.close 29))) (.step 29 (.close 9)))) (.step 42 (.step 9 (.step 13 (.close 24)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 53 (.step 43 (.step 9 (.step 13 (.step 15 (.close 37)))))) (.step 43 (.step 27 (.step 17 (.step 19 (.close 20)))))) (.split 43 0 (.step 38 (.step 57 (.step 43 (.step 15 (.step 33 (.close 37)))))) (.step 15 (.step 29 (.step 33 (.step 17 (.step 20 (.step 37 (.close 43))))))))) (.split 36 0 (.split 42 0 (.step 42 (.step 15 (.step 9 (.step 33 (.step 37 (.close 38)))))) (.step 29 (.step 33 (.close 38)))) (.step 29 (.close 38))))))) (.reuse 1))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578007064321570777199612469316106615950945874003124813824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 68 (.step 27 (.step 61 (.step 13 (.step 24 (.close 39)))))) (.split 43 0 (.split 49 0 (.step 67 (.step 20 (.close 24))) (.step 61 (.step 67 (.close 24)))) (.step 27 (.step 9 (.close 11))))) (.split 36 0 (.step 42 (.step 53 (.step 43 (.step 9 (.step 24 (.step 39 (.close 52))))))) (.step 43 (.step 38 (.step 24 (.step 13 (.step 33 (.close 39)))))))) (.split 35 0 (.split 36 0 (.step 43 (.close 68)) (.step 43 (.close 15))) (.step 43 (.step 38 (.step 66 (.step 39 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 42 (.step 53 (.step 20 (.step 9 (.close 11))))) (.step 43 (.close 24))) (.split 39 0 (.step 68 (.step 33 (.step 24 (.step 9 (.close 39))))) (.step 24 (.step 19 (.close 20))))) (.split 36 0 (.step 42 (.close 19)) (.step 33 (.step 19 (.step 24 (.close 20)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 68 (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 17 (.step 24 (.step 19 (.close 20))))) (.step 38 (.step 43 (.step 15 (.step 24 (.close 25)))))) (.step 33 (.close 38))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920556372084230624654064048844273602202546053108989952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 68 (.step 27 (.step 53 (.step 24 (.step 20 (.step 39 (.close 42))))))) (.split 43 0 (.split 49 0 (.step 67 (.close 20)) (.step 53 (.step 68 (.close 42)))) (.step 27 (.step 9 (.close 11))))) (.split 39 0 (.step 53 (.step 11 (.step 13 (.step 19 (.close 24))))) (.step 42 (.step 9 (.step 13 (.close 24)))))) (.split 35 0 (.split 36 0 (.step 43 (.close 68)) (.step 43 (.close 15))) (.step 43 (.close 38)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.split 39 0 (.step 53 (.step 11 (.step 13 (.step 19 (.close 24))))) (.step 24 (.close 19)))) (.split 36 0 (.step 42 (.close 19)) (.step 33 (.step 19 (.step 13 (.step 19 (.close 24))))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 53 (.step 11 (.step 13 (.step 15 (.close 19))))) (.step 17 (.step 24 (.close 19)))) (.step 38 (.close 17))) (.step 33 (.close 38))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 53 (.step 11 (.step 24 (.close 13)))))) (.step 24 (.close 19))) (.split 36 0 (.split 39 0 (.step 53 (.step 11 (.step 13 (.close 19)))) (.step 11 (.step 24 (.step 42 (.close 19))))) (.step 24 (.step 38 (.close 19))))) (.step 24 (.step 17 (.step 67 (.step 38 (.step 24 (.close 20))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 19)) (.step 24 (.step 19 (.close 20)))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 25 (.step 11 (.step 19 (.close 15))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949760857469242304622112975076014673728032997376⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 53 (.step 11 (.close 20))))) (.step 24 (.close 19))) (.split 36 0 (.split 39 0 (.step 53 (.step 11 (.step 13 (.close 19)))) (.step 11 (.step 24 (.step 42 (.close 19))))) (.step 24 (.step 38 (.close 19))))) (.step 24 (.step 17 (.step 67 (.step 38 (.step 20 (.close 15))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 19)) (.step 24 (.step 19 (.close 20)))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 20 (.step 11 (.step 24 (.step 19 (.step 20 (.close 25)))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 61 (.step 24 (.step 25 (.step 11 (.step 13 (.close 19)))))) (.step 24 (.step 19 (.close 20)))) (.step 11 (.step 19 (.close 24)))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.close 19))) (.step 24 (.split 30 0 (.split 36 0 (.step 19 (.step 11 (.close 20))) (.step 20 (.step 19 (.close 25)))) (.step 19 (.step 20 (.step 11 (.close 15))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578005567743895544151599136906784260459525786850794930176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 30 0 (.split 39 0 (.split 35 0 (.step 52 (.split 36 0 (.step 27 (.step 54 (.step 53 (.step 20 (.close 57))))) (.step 57 (.step 68 (.close 43))))) (.split 36 0 (.step 15 (.step 42 (.step 52 (.step 9 (.step 38 (.step 20 (.step 24 (.close 57)))))))) (.step 57 (.step 42 (.step 15 (.step 43 (.step 9 (.step 24 (.close 17))))))))) (.split 35 0 (.split 42 0 (.step 27 (.step 42 (.step 52 (.step 38 (.step 20 (.step 24 (.close 54))))))) (.step 62 (.split 43 0 (.step 38 (.step 67 (.step 15 (.step 20 (.close 17))))) (.step 11 (.close 9))))) (.step 42 (.step 9 (.step 13 (.close 15)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 53 (.step 9 (.step 20 (.close 24))))) (.step 42 (.close 15))) (.split 39 0 (.step 68 (.step 13 (.step 24 (.step 33 (.step 9 (.close 37)))))) (.step 38 (.close 24)))) (.split 36 0 (.step 42 (.close 15)) (.step 38 (.step 9 (.step 17 (.close 19))))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 11 (.close 13))) (.step 52 (.step 13 (.close 17)))) (.split 30 0 (.split 39 0 (.step 52 (.step 15 (.close 17))) (.step 17 (.step 38 (.close 43)))) (.step 38 (.step 43 (.step 13 (.step 15 (.close 17))))))) (.split 39 0 (.split 43 0 (.split 36 0 (.split 42 0 (.step 52 (.step 13 (.step 15 (.close 17)))) (.step 38 (.step 37 (.close 17)))) (.step 38 (.step 37 (.close 17)))) (.step 15 (.step 29 (.close 9)))) (.step 17 (.close 38))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910583987090326054009105786868311566919770570752⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 24 (.step 20 (.close 53)))))) (.step 24 (.step 17 (.step 24 (.step 13 (.close 15)))))) (.split 36 0 (.step 62 (.step 11 (.step 17 (.step 67 (.step 15 (.step 20 (.close 24))))))) (.step 11 (.step 17 (.step 43 (.step 19 (.step 13 (.close 20)))))))) (.split 36 0 (.split 43 0 (.split 39 0 (.step 75 (.step 15 (.step 24 (.step 17 (.close 38))))) (.step 17 (.step 42 (.close 15)))) (.step 11 (.close 9))) (.step 24 (.step 74 (.step 17 (.step 19 (.close 13))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.close 17)) (.step 17 (.step 9 (.close 24)))) (.step 17 (.step 15 (.step 17 (.close 24))))) (.step 17 (.step 24 (.step 33 (.step 15 (.step 17 (.close 37)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 24 (.split 42 0 (.step 24 (.step 11 (.step 17 (.step 25 (.step 13 (.close 20)))))) (.step 13 (.close 24)))) (.step 11 (.step 17 (.step 19 (.step 24 (.close 25)))))) (.step 24 (.step 20 (.step 13 (.close 19))))) (.step 24 (.step 19 (.step 25 (.step 13 (.close 20)))))) (.step 24 (.split 35 0 (.step 17 (.step 13 (.close 20))) (.step 13 (.step 17 (.step 20 (.close 24))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578007064321572170996187377480052961933337914525718937600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 24 (.step 20 (.close 53)))))) (.step 24 (.step 17 (.step 24 (.step 13 (.close 15)))))) (.step 61 (.split 43 0 (.step 17 (.step 67 (.step 15 (.step 20 (.close 24))))) (.step 11 (.close 24))))) (.split 36 0 (.split 43 0 (.split 39 0 (.split 42 0 (.step 15 (.step 42 (.step 52 (.step 24 (.close 38))))) (.step 24 (.close 19))) (.step 17 (.step 42 (.close 15)))) (.step 11 (.close 9))) (.step 24 (.step 74 (.step 17 (.step 19 (.close 13))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.close 17)) (.step 17 (.step 9 (.close 24)))) (.step 17 (.step 15 (.step 17 (.close 24))))) (.step 17 (.step 24 (.step 33 (.step 15 (.step 17 (.close 37)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 61 (.step 24 (.step 11 (.step 17 (.step 13 (.close 19)))))))) (.step 24 (.close 20))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.split 35 0 (.step 17 (.step 13 (.close 20))) (.step 13 (.step 17 (.step 20 (.close 24)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920556372085624421228972212790619584594586575703113728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 52 (.step 24 (.close 11)))) (.split 42 0 (.step 42 (.step 15 (.close 24))) (.step 24 (.step 13 (.close 19))))) (.split 43 0 (.split 39 0 (.split 42 0 (.step 53 (.step 13 (.step 15 (.close 19)))) (.step 24 (.step 37 (.step 19 (.step 20 (.close 24)))))) (.step 17 (.step 42 (.step 13 (.step 15 (.close 24)))))) (.step 11 (.close 9)))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 42 (.step 15 (.step 17 (.close 9)))) (.step 17 (.step 9 (.close 24)))) (.step 17 (.step 15 (.step 17 (.close 24))))) (.step 17 (.step 24 (.step 33 (.step 15 (.step 17 (.close 37)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.close 13)) (.step 24 (.step 19 (.close 13)))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.step 38 (.step 11 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.close 19)))))) (.step 11 (.step 17 (.step 19 (.step 13 (.close 24)))))) (.step 11 (.step 17 (.step 20 (.step 13 (.step 19 (.close 24))))))) (.step 11 (.step 17 (.step 19 (.step 24 (.step 19 (.close 20))))))) (.step 17 (.close 9))) (.step 42 (.step 24 (.step 13 (.step 19 (.step 25 (.close 11)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251265817212786059321058406714250627121152⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.reuse 0) (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 11 (.step 17 (.step 25 (.step 13 (.close 19))))))) (.step 11 (.step 17 (.step 20 (.step 13 (.step 20 (.step 19 (.close 24)))))))) (.step 11 (.step 17 (.step 19 (.step 24 (.close 20)))))) (.step 17 (.close 9))) (.split 34 0 (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 74 (.step 13 (.step 20 (.close 19)))) (.step 13 (.step 20 (.step 19 (.close 24))))) (.step 24 (.step 13 (.step 20 (.close 19))))) (.step 13 (.step 20 (.step 24 (.close 19))))))) (.step 13 (.step 17 (.close 20)))))))) (.split 17 0 (.reuse 2) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 11 (.step 17 (.step 19 (.step 24 (.step 13 (.close 19)))))))) (.step 11 (.step 17 (.step 20 (.step 13 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 19 (.step 24 (.step 19 (.close 20))))))) (.step 17 (.close 9))) (.step 42 (.step 24 (.step 13 (.step 19 (.step 20 (.close 11))))))) (.split 35 0 (.split 39 0 (.split 30 0 (.split 34 0 (.step 11 (.step 17 (.step 19 (.step 20 (.step 13 (.close 24)))))) (.step 17 (.close 20))) (.step 19 (.step 13 (.step 20 (.step 11 (.step 17 (.close 24))))))) (.step 11 (.step 17 (.close 19)))) (.step 11 (.step 17 (.close 19))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251265817212786059321058406714250627121152⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part5.root, Part10.root]
def proof : Chunks.Proof 4 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 11 (.step 13 (.close 19))))) (.step 24 (.step 19 (.close 20)))) (.split 36 0 (.split 39 0 (.split 42 0 (.step 24 (.step 42 (.step 9 (.step 24 (.close 38))))) (.step 24 (.close 19))) (.step 11 (.step 24 (.step 42 (.close 20))))) (.step 24 (.step 74 (.step 19 (.step 13 (.close 20))))))) (.step 24 (.step 17 (.step 74 (.step 24 (.step 19 (.close 20))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 25 (.step 11 (.step 13 (.close 19)))))) (.step 24 (.close 20))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.step 33 (.step 20 (.step 11 (.step 24 (.step 20 (.step 19 (.step 20 (.close 25)))))))))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163441209373187393371376894067186671639643592973858879219551616927556080652362211429030078182503479666278400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 35 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 72 0 (.step 57 (.step 9 (.close 27))) (.step 9 (.step 57 (.close 17)))) (.step 9 (.step 53 (.step 57 (.close 17))))) (.step 9 (.step 15 (.step 17 (.step 38 (.step 42 (.close 53))))))) (.step 9 (.step 62 (.step 15 (.step 24 (.step 13 (.close 17))))))) (.split 36 0 (.step 9 (.step 53 (.step 15 (.split 51 0 (.step 38 (.step 17 (.close 24))) (.step 57 (.close 13)))))) (.step 57 (.step 9 (.step 15 (.step 38 (.step 13 (.close 20)))))))) (.split 39 0 (.split 35 0 (.step 62 (.split 42 0 (.step 9 (.step 17 (.step 24 (.close 15)))) (.step 24 (.step 9 (.step 15 (.step 13 (.step 20 (.close 24)))))))) (.split 36 0 (.step 62 (.split 42 0 (.step 9 (.step 15 (.step 17 (.step 19 (.step 24 (.close 38)))))) (.step 24 (.step 9 (.step 15 (.step 19 (.step 13 (.close 17)))))))) (.step 29 (.step 38 (.step 37 (.step 24 (.step 33 (.step 24 (.close 39))))))))) (.split 42 0 (.split 43 0 (.split 49 0 (.step 75 (.step 24 (.step 42 (.step 24 (.close 15))))) (.step 17 (.close 54))) (.step 24 (.step 9 (.close 27)))) (.step 17 (.step 24 (.step 33 (.close 38))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910582593295080373840944356758823333457456791552⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 30 0 (.split 34 0 (.reuse 0) (.run (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20))))) (.step 62 (.step 24 (.step 9 (.step 15 (.step 13 (.close 19))))))) (.step 57 (.step 43 (.close 15)))) (.split 36 0 (.split 42 0 (.step 15 (.step 9 (.step 17 (.close 19)))) (.step 15 (.step 19 (.step 24 (.close 38))))) (.step 15 (.step 24 (.step 37 (.close 38)))))))) (.run (.split 34 0 (.split 35 0 (.split 22 0 (.split 39 0 (.split 42 0 (.step 53 (.step 9 (.step 57 (.step 13 (.close 15))))) (.step 62 (.split 36 0 (.step 9 (.step 15 (.step 37 (.step 24 (.close 33))))) (.step 29 (.step 37 (.step 39 (.close 20))))))) (.split 42 0 (.step 53 (.step 43 (.step 42 (.step 9 (.step 13 (.close 15)))))) (.step 9 (.step 24 (.step 33 (.step 13 (.close 38))))))) (.step 24 (.split 36 0 (.step 43 (.step 42 (.step 24 (.step 9 (.step 43 (.step 15 (.close 17))))))) (.step 24 (.step 9 (.step 13 (.step 33 (.close 39)))))))) (.split 36 0 (.split 39 0 (.split 22 0 (.split 43 0 (.split 49 0 (.step 38 (.close 24)) (.step 15 (.step 42 (.step 37 (.close 38))))) (.step 9 (.close 11))) (.step 38 (.step 9 (.step 24 (.close 13))))) (.step 9 (.step 38 (.close 13)))) (.step 29 (.step 38 (.close 13))))) (.split 22 0 (.step 15 (.split 35 0 (.step 43 (.step 9 (.step 13 (.close 15)))) (.step 15 (.close 24)))) (.step 24 (.step 13 (.step 15 (.close 29))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1496577676626845917468569053617346715934736278093824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578007064321570777200941697311891531823849681063405158400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 68 (.split 63 0 (.split 64 0 (.step 61 (.close 9)) (.step 9 (.step 17 (.step 24 (.step 39 (.close 53)))))) (.step 9 (.step 15 (.step 17 (.step 20 (.close 24))))))) (.step 43 (.step 15 (.step 9 (.step 37 (.step 24 (.step 33 (.step 24 (.close 39))))))))) (.split 42 0 (.split 43 0 (.split 49 0 (.step 24 (.step 42 (.step 61 (.close 15)))) (.step 17 (.close 54))) (.step 24 (.step 9 (.close 27)))) (.step 17 (.step 24 (.close 33))))) (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 15 (.step 42 (.step 53 (.step 17 (.step 20 (.close 24))))))) (.step 29 (.step 38 (.step 24 (.step 15 (.step 24 (.step 13 (.close 17)))))))) (.step 17 (.step 38 (.step 9 (.close 24))))) (.step 29 (.step 38 (.step 37 (.step 24 (.step 33 (.step 24 (.close 39))))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 24 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20)))))) (.step 15 (.step 9 (.step 17 (.close 19))))) (.step 29 (.step 43 (.close 15)))) (.step 29 (.step 38 (.step 15 (.step 19 (.close 24))))))) (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 35 0 (.step 24 (.step 9 (.step 43 (.step 15 (.close 17))))) (.step 38 (.step 9 (.step 24 (.close 13))))) (.step 24 (.step 9 (.step 13 (.close 33))))) (.step 17 (.step 24 (.close 38)))) (.step 24 (.step 9 (.step 13 (.step 33 (.close 39)))))) (.step 24 (.step 13 (.step 15 (.close 29)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1461501637332232146199469748589186826717286629376, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920556372084230625983292044629189475106353113389334528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 68 (.step 53 (.step 9 (.step 17 (.step 24 (.close 15)))))) (.step 43 (.step 15 (.step 9 (.step 37 (.step 24 (.step 33 (.step 24 (.close 38))))))))) (.split 42 0 (.step 53 (.step 24 (.step 27 (.step 17 (.step 24 (.step 15 (.close 42))))))) (.step 17 (.step 24 (.close 33))))) (.split 36 0 (.step 53 (.close 15)) (.step 29 (.step 38 (.close 13))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 24 (.step 9 (.step 15 (.step 17 (.close 19))))) (.step 15 (.step 9 (.step 17 (.close 19))))) (.step 29 (.step 38 (.step 37 (.step 17 (.step 24 (.close 15))))))) (.step 29 (.step 38 (.close 13))))) (.split 34 0 (.split 36 0 (.step 53 (.step 15 (.close 19))) (.step 24 (.step 9 (.step 13 (.step 33 (.close 38)))))) (.step 24 (.step 13 (.step 15 (.close 29)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 62 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))) (.step 17 (.close 24))) (.step 17 (.step 24 (.close 38)))) (.step 17 (.step 24 (.close 38)))) (.step 24 (.step 13 (.close 15)))) (.step 24 (.step 17 (.step 24 (.close 19)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146440781844236931310521310907465728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 15 (.step 17 (.step 9 (.step 11 (.close 27))))) (.step 62 (.step 17 (.close 9)))) (.split 42 0 (.step 15 (.step 11 (.close 17))) (.step 15 (.step 13 (.close 17))))) (.split 36 0 (.split 42 0 (.step 15 (.step 11 (.close 17))) (.step 15 (.close 17))) (.step 15 (.close 17)))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 15 (.step 11 (.close 17))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 24 (.close 17)))) (.step 15 (.step 17 (.step 24 (.close 37)))))) (.split 22 0 (.step 15 (.split 34 0 (.split 35 0 (.step 53 (.step 42 (.step 13 (.step 9 (.close 15))))) (.step 15 (.close 17))) (.step 15 (.step 24 (.step 9 (.close 13)))))) (.step 24 (.close 17)))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.close 17)) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.close 15))) (.step 17 (.close 15))) (.step 24 (.step 52 (.step 15 (.step 13 (.close 24)))))) (.step 24 (.close 17))) (.step 17 (.close 13)))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.close 17)) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.close 15))) (.step 17 (.close 15))) (.step 24 (.step 38 (.step 17 (.close 15))))) (.step 24 (.close 17))) (.step 17 (.close 13))) (.step 17 (.step 13 (.close 15))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352365718032067578005567743894150355024230010488514705363147824904011776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 35 0 (.step 52 (.step 68 (.step 9 (.close 39)))) (.split 36 0 (.step 52 (.step 53 (.step 9 (.step 20 (.close 24))))) (.step 57 (.step 43 (.step 29 (.step 38 (.step 13 (.close 33)))))))) (.split 35 0 (.split 42 0 (.step 52 (.split 64 0 (.step 43 (.close 11)) (.step 24 (.step 27 (.step 19 (.step 20 (.step 19 (.close 38)))))))) (.step 43 (.step 27 (.step 24 (.close 19))))) (.split 36 0 (.step 42 (.step 9 (.close 38))) (.step 38 (.step 9 (.close 13)))))) (.step 15 (.split 35 0 (.split 36 0 (.step 52 (.close 17)) (.step 15 (.close 17))) (.step 15 (.step 17 (.close 33)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 53 (.step 9 (.step 20 (.close 24))))) (.split 42 0 (.step 42 (.step 52 (.step 24 (.step 9 (.close 11))))) (.step 38 (.step 13 (.step 11 (.step 19 (.step 24 (.close 27)))))))) (.split 39 0 (.split 42 0 (.step 52 (.step 53 (.step 9 (.close 20)))) (.step 13 (.step 33 (.step 39 (.step 9 (.close 20)))))) (.step 38 (.step 13 (.step 11 (.step 19 (.step 20 (.close 27)))))))) (.split 39 0 (.split 43 0 (.split 36 0 (.split 42 0 (.step 42 (.step 38 (.close 13))) (.step 33 (.close 38))) (.step 33 (.close 38))) (.step 33 (.step 9 (.step 33 (.close 9))))) (.step 38 (.step 24 (.step 13 (.close 27)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 11 (.close 13)))) (.step 17 (.step 15 (.step 13 (.close 27))))) (.step 15 (.close 17))) (.step 15 (.step 17 (.close 33)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922051488259220138339387686078742587961055568803659776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 19 (.close 20))))) (.step 43 (.step 13 (.step 11 (.close 19))))) (.split 39 0 (.step 68 (.step 13 (.step 24 (.step 9 (.close 39))))) (.step 24 (.step 13 (.close 19))))) (.split 36 0 (.split 39 0 (.step 68 (.step 11 (.step 13 (.close 19)))) (.step 24 (.step 38 (.step 19 (.close 20))))) (.step 43 (.step 13 (.step 19 (.close 24)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.close 15))) (.step 17 (.step 15 (.close 33))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 52 (.step 53 (.step 20 (.close 9)))) (.step 13 (.step 24 (.step 9 (.close 33))))) (.step 42 (.step 13 (.close 19)))) (.step 33 (.split 39 0 (.step 13 (.step 33 (.step 24 (.step 9 (.step 29 (.close 39)))))) (.step 20 (.step 13 (.step 9 (.close 24))))))) (.step 33 (.step 19 (.step 24 (.close 20))))) (.step 33 (.split 36 0 (.step 17 (.step 13 (.step 9 (.close 15)))) (.step 13 (.step 33 (.step 15 (.close 39)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 61 (.step 24 (.step 13 (.step 11 (.close 20))))) (.step 13 (.step 24 (.close 20)))) (.step 11 (.step 61 (.step 19 (.step 13 (.step 20 (.close 24))))))) (.step 24 (.close 20))) (.step 24 (.step 19 (.step 20 (.close 13))))) (.step 17 (.step 20 (.step 15 (.close 17)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922051488259220138339387686078742587961055568803659776⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 52 (.step 62 (.step 9 (.close 20)))) (.step 68 (.step 13 (.step 24 (.step 9 (.close 39)))))) (.step 24 (.split 43 0 (.split 36 0 (.step 42 (.step 24 (.step 13 (.close 19)))) (.step 24 (.step 13 (.close 19)))) (.step 11 (.step 13 (.step 9 (.close 20))))))) (.split 36 0 (.split 39 0 (.step 68 (.step 11 (.step 13 (.close 19)))) (.step 24 (.step 38 (.step 19 (.close 20))))) (.step 43 (.step 13 (.step 19 (.close 24)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.close 15))) (.step 17 (.step 15 (.close 33))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 52 (.step 53 (.step 24 (.close 11)))) (.step 13 (.step 24 (.step 9 (.close 33))))) (.step 42 (.step 13 (.close 19)))) (.step 33 (.split 39 0 (.step 13 (.step 33 (.step 24 (.step 9 (.step 29 (.close 39)))))) (.step 20 (.step 13 (.step 24 (.close 19))))))) (.step 33 (.step 19 (.step 24 (.close 20))))) (.step 33 (.split 36 0 (.step 17 (.step 13 (.step 9 (.close 15)))) (.step 13 (.step 33 (.step 15 (.step 39 (.close 15))))))))))) (.reuse 1))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920556372084230624654065316494873830431947549812195328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 13 (.step 11 (.close 19))))) (.split 39 0 (.step 68 (.step 13 (.step 24 (.step 9 (.close 38))))) (.step 24 (.step 13 (.close 19))))) (.split 36 0 (.split 39 0 (.step 53 (.step 11 (.step 13 (.close 19)))) (.step 24 (.step 38 (.step 19 (.close 20))))) (.step 38 (.step 9 (.step 13 (.close 19)))))) (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.close 15))) (.step 17 (.step 15 (.close 33))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 43 0 (.split 39 0 (.step 53 (.close 13)) (.step 42 (.close 13))) (.step 33 (.step 42 (.step 13 (.step 9 (.close 11)))))) (.step 33 (.step 38 (.step 13 (.step 11 (.close 19)))))) (.step 33 (.step 19 (.step 13 (.step 19 (.close 24)))))) (.step 33 (.step 38 (.step 13 (.step 11 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 43 0 (.split 49 0 (.step 25 (.step 19 (.close 13))) (.step 13 (.step 19 (.close 24)))) (.step 11 (.step 13 (.step 9 (.close 24))))) (.step 13 (.step 24 (.close 19)))) (.step 11 (.step 42 (.close 13)))) (.step 24 (.step 20 (.step 11 (.step 13 (.step 19 (.close 24))))))) (.step 24 (.close 19))) (.step 17 (.step 20 (.step 15 (.close 17)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922051488260613934914295850025088570353096091397783552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.split 34 0 (.split 35 0 (.split 39 0 (.split 43 0 (.step 66 (.step 15 (.close 17))) (.step 15 (.close 11))) (.split 36 0 (.step 42 (.step 15 (.step 11 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.step 15 (.step 17 (.close 13)))) (.step 15 (.step 17 (.close 33))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.split 43 0 (.step 68 (.step 17 (.close 13))) (.step 13 (.close 11)))) (.step 17 (.step 15 (.step 11 (.close 13))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 17 (.close 13)))) (.step 15 (.step 66 (.close 13))))) (.split 30 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 11 (.step 17 (.close 15)))) (.step 17 (.step 13 (.close 15)))) (.step 17 (.step 15 (.close 13)))) (.split 35 0 (.split 49 0 (.split 34 0 (.split 36 0 (.step 17 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 13 (.close 17)))))) (.split 22 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 11 (.step 17 (.close 15)))) (.step 17 (.step 13 (.close 15)))) (.step 17 (.step 15 (.close 13)))) (.split 35 0 (.split 49 0 (.split 34 0 (.split 36 0 (.step 17 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.step 17 (.step 11 (.close 13))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251265817214053709921286636115747330326528⟩
def references : Fin 3 → Box := ![Part19.root, Part20.root, Part21.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.reuse 0) (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 61 (.step 24 (.step 13 (.step 11 (.close 19))))) (.step 13 (.step 24 (.close 19)))) (.step 11 (.step 42 (.close 13)))) (.step 24 (.close 20))) (.step 24 (.close 19))) (.step 17 (.step 20 (.step 15 (.close 17))))) (.split 34 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 61 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 19 (.step 13 (.step 20 (.step 9 (.close 24)))))) (.step 11 (.step 19 (.close 13)))) (.step 19 (.step 13 (.close 20)))) (.step 19 (.step 13 (.step 20 (.close 24))))) (.step 19 (.step 9 (.step 13 (.close 20))))) (.step 17 (.close 20))))))) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 11 (.step 17 (.close 15)))) (.step 17 (.step 13 (.close 15)))) (.step 17 (.step 15 (.close 13)))) (.split 35 0 (.split 49 0 (.split 34 0 (.split 36 0 (.step 17 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.step 17 (.step 11 (.close 13)))) (.step 17 (.close 13))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922051488259220139668615681863658460864862629084004352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 15 (.step 11 (.step 13 (.close 17)))))) (.step 52 (.step 24 (.step 15 (.step 43 (.step 15 (.step 11 (.close 17)))))))) (.split 39 0 (.step 15 (.step 13 (.close 17))) (.step 17 (.step 9 (.step 15 (.close 17)))))) (.split 36 0 (.split 39 0 (.step 15 (.close 17)) (.step 9 (.step 17 (.step 15 (.close 17))))) (.step 15 (.step 17 (.close 24))))) (.split 22 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 15 (.step 13 (.step 9 (.close 17)))))) (.step 17 (.step 15 (.step 13 (.close 27))))) (.step 15 (.close 17))) (.step 15 (.step 17 (.close 33)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 17 (.close 13)) (.step 13 (.step 15 (.step 13 (.close 17))))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 13 (.step 15 (.step 13 (.close 17))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.step 15 (.close 24)))) (.step 15 (.step 9 (.close 17)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 17 (.close 13)) (.step 13 (.step 15 (.step 13 (.close 17))))) (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 13 (.step 15 (.step 13 (.close 17)))))) (.step 17 (.close 13)))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146442049494837159539922807610671104⟩
def references : Fin 7 → Box := ![Part11.root, Part13.root, Part14.root, Part15.root, Part16.root, Part22.root, Part23.root]
def proof : Chunks.Proof 7 := (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 1) (.split 22 0 (.reuse 2) (.run (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 62 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))) (.step 17 (.close 24))) (.step 17 (.step 24 (.close 38)))) (.step 17 (.step 24 (.close 38)))) (.step 24 (.step 13 (.close 15)))) (.step 24 (.step 17 (.step 24 (.close 19)))))))) (.split 17 0 (.reuse 3) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 43 0 (.step 17 (.step 24 (.step 38 (.step 15 (.close 20))))) (.step 24 (.close 9))) (.step 17 (.close 24))) (.step 17 (.step 24 (.close 38)))) (.step 17 (.step 24 (.close 38)))) (.step 24 (.step 13 (.close 15)))) (.step 24 (.step 17 (.step 24 (.close 19))))) (.step 24 (.step 17 (.step 24 (.close 19)))))))) (.reuse 4))) (.split 12 0 (.reuse 5) (.split 14 0 (.split 16 0 (.reuse 6) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 15 (.step 17 (.step 9 (.close 13)))) (.step 17 (.step 9 (.step 11 (.close 15))))) (.step 17 (.step 15 (.close 24)))) (.step 15 (.step 9 (.close 17)))) (.step 38 (.step 13 (.step 9 (.close 15))))) (.step 17 (.close 13))) (.step 17 (.step 13 (.close 15)))))) (.run (.split 16 0 (.split 17 0 (.split 30 0 (.step 15 (.step 11 (.close 17))) (.step 15 (.step 13 (.step 11 (.step 15 (.close 17)))))) (.step 17 (.close 13))) (.step 17 (.close 13)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part24

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part24.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case51

namespace FiveColour.Packed.EnumerationChunks.Projected.Case51
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 295 0 11 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 295 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 295 0).upper i := by decide +kernel
lemma budget_model : (⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 295), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 295) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 295 0 11).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 11)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 11 families = caseProblem 295 0 11 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 295) (Archive.root 295) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 295 0 11 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 295 0 11).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case51

namespace FiveColour.Packed.EnumerationChunks.Case51
def root : Box := Archive.root 295
def families : Fin 78 → List Cut := Enumeration.families 295
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case51.original_covered points
end FiveColour.Packed.EnumerationChunks.Case51
