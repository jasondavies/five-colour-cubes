module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case238
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146442049494837159539922807610671104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910582593293751145845159440885919526397176446976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 39 0 (.split 42 0 (.split 35 0 (.split 34 0 (.step 57 (.step 9 (.close 11))) (.step 9 (.step 52 (.step 15 (.close 20))))) (.step 29 (.step 53 (.step 20 (.step 13 (.step 15 (.step 20 (.close 52)))))))) (.step 62 (.step 9 (.step 39 (.close 13))))) (.split 42 0 (.split 35 0 (.split 34 0 (.step 27 (.step 57 (.step 19 (.step 38 (.close 42))))) (.step 38 (.step 9 (.step 17 (.step 15 (.step 19 (.close 20))))))) (.step 38 (.step 9 (.close 42)))) (.step 38 (.step 43 (.step 9 (.step 24 (.step 19 (.close 42)))))))) (.split 34 0 (.split 35 0 (.step 53 (.step 68 (.step 9 (.close 33)))) (.step 42 (.step 29 (.step 33 (.step 13 (.close 38)))))) (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 15 (.step 17 (.close 20)))))) (.step 38 (.close 9))) (.step 38 (.step 15 (.step 43 (.step 9 (.step 33 (.close 37))))))))) (.split 30 0 (.split 39 0 (.split 34 0 (.step 62 (.step 9 (.step 20 (.close 13)))) (.step 43 (.step 15 (.step 9 (.close 13))))) (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38)))))) (.step 24 (.step 38 (.step 24 (.close 19)))))) (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 20 (.step 13 (.close 24))))))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19)))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949760857469242304622112975076014673728032997376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.step 11 (.step 53 (.step 24 (.step 19 (.close 42)))))) (.step 42 (.step 38 (.close 9)))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 38 (.close 9)))) (.split 34 0 (.step 42 (.step 38 (.step 11 (.close 13)))) (.step 38 (.step 11 (.close 17))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 24 (.close 19)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.step 20 (.close 9)))) (.split 36 0 (.step 24 (.step 38 (.step 9 (.close 19)))) (.step 24 (.close 19)))) (.step 17 (.step 24 (.close 19)))) (.step 24 (.step 42 (.step 20 (.step 11 (.step 19 (.close 15))))))) (.split 34 0 (.split 39 0 (.step 24 (.step 19 (.step 20 (.step 9 (.close 13))))) (.step 11 (.close 19))) (.step 24 (.step 19 (.step 20 (.close 11))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910583987090326054009105786868311566919770570752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 57 (.close 19)))) (.step 42 (.step 27 (.step 52 (.step 20 (.step 19 (.close 38))))))) (.split 35 0 (.step 52 (.close 17)) (.split 39 0 (.step 52 (.step 15 (.close 17))) (.step 17 (.step 29 (.close 38)))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 42 (.close 13))) (.step 42 (.close 13))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.step 15 (.close 17)))) (.step 13 (.step 38 (.step 24 (.step 33 (.step 9 (.close 37))))))) (.step 38 (.step 9 (.close 17)))))) (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 67 (.step 24 (.step 15 (.close 13))))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.close 20)))))) (.step 13 (.step 20 (.close 24)))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251265817212786059321058406714250627121152⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 42 0 (.step 52 (.step 24 (.step 11 (.step 20 (.close 38))))) (.step 24 (.step 13 (.close 15)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 61 (.step 43 (.step 42 (.step 13 (.step 15 (.close 19))))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 19 (.step 24 (.step 13 (.close 20))))) (.step 13 (.step 17 (.close 24)))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 74 (.step 24 (.step 74 (.step 13 (.step 19 (.close 20)))))) (.step 24 (.step 20 (.close 13)))) (.step 13 (.step 20 (.close 24))))))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 34 0 (.split 35 0 (.step 42 (.step 24 (.step 11 (.step 17 (.step 13 (.step 15 (.close 20))))))) (.step 53 (.step 11 (.close 13)))) (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.step 11 (.step 17 (.step 42 (.close 13))))) (.step 24 (.step 42 (.step 13 (.close 17))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 19 (.step 24 (.step 13 (.step 19 (.close 20)))))) (.step 24 (.step 19 (.close 13)))) (.step 13 (.step 19 (.close 24))))))) (.split 22 0 (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 19 (.step 20 (.close 13)))) (.step 24 (.step 19 (.close 13)))) (.step 13 (.step 19 (.close 20)))))) (.step 25 (.step 11 (.step 17 (.step 19 (.step 13 (.close 20))))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929571175587451509467240083921714619356113870583094593283889032473964858676932872124426197401600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 22 0 (.split 39 0 (.split 42 0 (.step 9 (.split 35 0 (.step 66 (.step 20 (.step 24 (.close 53)))) (.step 15 (.step 53 (.step 17 (.close 20)))))) (.step 62 (.step 29 (.split 36 0 (.step 15 (.step 24 (.step 17 (.close 13)))) (.step 37 (.step 20 (.step 19 (.step 33 (.close 38))))))))) (.split 42 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 72 0 (.step 27 (.step 17 (.step 19 (.close 20)))) (.step 9 (.step 38 (.step 17 (.close 20))))) (.step 9 (.step 17 (.step 38 (.step 19 (.close 42)))))) (.step 9 (.step 15 (.step 17 (.step 19 (.close 38)))))) (.step 9 (.step 38 (.close 13)))) (.step 9 (.step 38 (.step 24 (.step 15 (.step 43 (.close 17)))))))) (.split 39 0 (.split 42 0 (.step 62 (.split 43 0 (.step 17 (.step 24 (.close 15))) (.step 9 (.close 11)))) (.step 43 (.step 66 (.step 24 (.close 33))))) (.step 62 (.step 9 (.step 17 (.step 19 (.step 15 (.close 20)))))))) (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20))))) (.step 24 (.step 9 (.step 15 (.step 13 (.close 19)))))) (.step 43 (.close 15))) (.split 36 0 (.split 42 0 (.step 15 (.step 9 (.step 13 (.close 19)))) (.step 15 (.step 19 (.close 20)))) (.step 15 (.step 20 (.step 19 (.close 37))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949760857470571532617897890948918480788313341952⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 30 0 (.reuse 0) (.run (.split 34 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 53 (.step 9 (.step 38 (.step 15 (.step 13 (.close 20)))))) (.split 39 0 (.split 43 0 (.step 38 (.close 13)) (.step 9 (.close 11))) (.step 9 (.close 38)))) (.step 24 (.split 35 0 (.step 24 (.step 9 (.step 43 (.close 15)))) (.step 38 (.step 9 (.close 13)))))) (.step 24 (.split 35 0 (.step 24 (.step 9 (.step 39 (.step 13 (.close 15))))) (.step 38 (.step 9 (.close 13)))))) (.split 17 0 (.step 15 (.step 38 (.step 43 (.step 9 (.step 13 (.close 15)))))) (.step 24 (.step 9 (.step 13 (.close 15)))))))) (.run (.split 17 0 (.split 30 0 (.split 34 0 (.split 22 0 (.split 35 0 (.split 42 0 (.step 53 (.step 9 (.step 17 (.step 24 (.close 15))))) (.step 9 (.step 24 (.step 15 (.step 24 (.close 13)))))) (.step 53 (.close 15))) (.step 17 (.step 24 (.step 9 (.step 15 (.close 19)))))) (.step 43 (.step 38 (.step 24 (.close 15))))) (.step 24 (.split 34 0 (.step 53 (.close 15)) (.step 15 (.step 13 (.step 24 (.step 9 (.close 15)))))))) (.split 22 0 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19))))) (.step 24 (.close 19))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146440781844236931310521310907465728⟩
def references : Fin 4 → Box := ![Part0.root, Part1.root, Part3.root, Part5.root]
def proof : Chunks.Proof 4 := (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 68 (.step 38 (.step 42 (.close 52)))) (.step 42 (.step 24 (.step 11 (.step 24 (.step 19 (.close 38))))))) (.split 35 0 (.step 43 (.step 11 (.close 17))) (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 53 (.step 20 (.close 9)))) (.step 43 (.step 11 (.close 19)))) (.step 42 (.close 19))) (.split 35 0 (.split 36 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 15 (.step 24 (.step 9 (.close 37)))))) (.step 33 (.step 15 (.step 17 (.close 19))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 61 (.step 24 (.step 11 (.close 13))))) (.split 36 0 (.step 24 (.step 42 (.step 24 (.close 9)))) (.step 24 (.step 19 (.close 20))))) (.step 17 (.step 24 (.step 20 (.close 19))))) (.step 24 (.split 34 0 (.split 35 0 (.step 25 (.step 11 (.close 20))) (.step 19 (.step 24 (.close 20)))) (.step 17 (.step 24 (.step 20 (.close 19)))))))))) (.reuse 1)) (.reuse 2)) (.split 14 0 (.reuse 3) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 34 0 (.split 35 0 (.split 22 0 (.step 52 (.split 30 0 (.step 9 (.step 15 (.close 17))) (.step 24 (.step 9 (.close 15))))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 24 (.step 15 (.close 17)))))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 17 (.split 17 0 (.step 17 (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 17 (.close 11))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part3.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274920554910582593293751147112810041114148927893879652352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 29 (.step 43 (.step 33 (.close 38))))) (.split 42 0 (.step 52 (.step 43 (.step 11 (.step 19 (.close 38))))) (.step 43 (.step 11 (.step 13 (.close 19)))))) (.step 15 (.split 35 0 (.step 52 (.close 17)) (.step 15 (.close 17))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.split 42 0 (.step 42 (.step 33 (.step 9 (.step 13 (.close 24))))) (.step 33 (.close 24)))) (.split 36 0 (.step 42 (.step 29 (.step 33 (.step 13 (.close 38))))) (.step 33 (.step 24 (.close 13))))) (.step 15 (.split 35 0 (.split 36 0 (.step 52 (.close 13)) (.step 13 (.step 15 (.close 17)))) (.step 15 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 13 (.close 20)))))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 70 (.step 24 (.step 11 (.step 25 (.close 13)))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949760857469242305889763575304244075224736202752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.step 20 (.close 24))))) (.step 13 (.step 33 (.step 24 (.close 9))))) (.step 33 (.close 19))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 17 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 24 (.close 19))))) (.step 24 (.close 19))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 61 (.step 24 (.step 13 (.step 11 (.close 19))))) (.step 13 (.step 24 (.close 19)))) (.step 11 (.step 19 (.step 13 (.close 20))))) (.step 24 (.close 20))) (.step 24 (.close 19))) (.step 17 (.close 20)))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251265817214053709921286636115747330326528⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 24 (.step 11 (.close 19)))) (.step 43 (.step 11 (.close 13)))) (.split 36 0 (.step 42 (.step 24 (.step 9 (.close 13)))) (.step 33 (.step 24 (.step 9 (.step 13 (.close 38))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 24 (.step 33 (.step 13 (.close 19))))) (.step 13 (.step 33 (.step 20 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 15 (.step 17 (.close 15)))))) (.step 17 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 25 (.step 11 (.close 13))))) (.step 13 (.step 20 (.step 9 (.close 24))))) (.step 24 (.step 19 (.step 13 (.close 20))))))))) (.reuse 1)) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 15 (.step 11 (.step 13 (.close 17)))) (.step 17 (.step 13 (.close 11)))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.split 49 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15))) (.step 15 (.step 13 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 11 (.step 17 (.close 13))))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.step 17 (.step 15 (.step 17 (.close 13))))) (.step 17 (.split 17 0 (.step 17 (.step 15 (.step 17 (.close 13)))) (.step 13 (.close 17)))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953326352367403028734274922052949762251267146442049494837159539922807610671104⟩
def references : Fin 2 → Box := ![Part6.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 15 (.step 11 (.close 13))))) (.step 24 (.step 15 (.step 17 (.close 13))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.close 17))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 17 (.split 17 0 (.step 17 (.step 15 (.step 17 (.step 9 (.close 13))))) (.step 17 (.close 13))))) (.step 17 (.close 15))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case238
