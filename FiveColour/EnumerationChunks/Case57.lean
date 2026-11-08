module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case57
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566053817933581204324352⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩]
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
def root : Box := ⟨1329227995784915872903807061354086400, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288766217298965825588532084501118976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 42 0 (.split 34 0 (.split 61 0 (.step 9 (.step 13 (.step 16 (.close 18)))) (.step 15 (.close 52))) (.step 15 (.close 9))) (.step 62 (.step 64 (.close 9)))) (.split 36 0 (.step 15 (.step 9 (.step 21 (.close 13)))) (.step 57 (.step 13 (.step 15 (.step 9 (.close 18))))))) (.split 36 0 (.step 53 (.step 15 (.step 9 (.step 13 (.close 18))))) (.step 13 (.step 71 (.step 9 (.step 15 (.close 33))))))) (.split 30 0 (.split 36 0 (.step 62 (.step 68 (.step 4 (.close 52)))) (.step 13 (.step 68 (.close 15)))) (.step 13 (.step 62 (.step 53 (.step 37 (.step 4 (.close 9)))))))) (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 54 (.step 4 (.step 9 (.close 52)))) (.step 13 (.step 62 (.step 4 (.step 15 (.step 4 (.close 39))))))) (.step 13 (.step 68 (.close 15)))) (.step 13 (.step 68 (.close 18)))) (.step 13 (.split 34 0 (.step 54 (.step 24 (.step 4 (.close 18)))) (.step 24 (.step 43 (.close 14))))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 53 (.step 68 (.step 4 (.close 52)))) (.step 13 (.step 68 (.close 15)))) (.step 13 (.step 53 (.close 4)))) (.step 13 (.step 53 (.split 34 0 (.step 53 (.step 62 (.step 18 (.step 14 (.close 20))))) (.step 24 (.step 43 (.close 14))))))) (.split 22 0 (.step 13 (.step 53 (.split 34 0 (.step 53 (.step 54 (.close 4))) (.step 24 (.step 43 (.close 14)))))) (.step 23 (.step 24 (.close 17)))))))
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288766217298965825588532084501118976⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.run (.split 22 0 (.split 42 0 (.split 17 0 (.split 36 0 (.split 16 0 (.split 30 0 (.split 34 0 (.step 53 (.close 9)) (.step 52 (.step 9 (.step 15 (.close 18))))) (.step 53 (.step 9 (.step 13 (.step 15 (.close 18)))))) (.step 53 (.step 4 (.step 13 (.close 52))))) (.step 54 (.split 16 0 (.split 30 0 (.step 18 (.step 9 (.close 13))) (.step 53 (.step 9 (.step 13 (.step 15 (.close 18)))))) (.step 53 (.step 4 (.close 13)))))) (.step 54 (.split 16 0 (.step 58 (.step 33 (.close 4))) (.step 53 (.step 4 (.close 13)))))) (.step 70 (.split 17 0 (.split 36 0 (.split 16 0 (.step 58 (.close 9)) (.step 53 (.step 4 (.close 13)))) (.step 54 (.split 49 0 (.step 53 (.step 4 (.step 9 (.close 15)))) (.step 13 (.step 43 (.step 18 (.step 9 (.close 16)))))))) (.step 54 (.step 48 (.step 23 (.close 9))))))) (.split 30 0 (.split 34 0 (.split 17 0 (.step 70 (.step 62 (.step 4 (.close 13)))) (.step 54 (.step 70 (.step 18 (.close 13))))) (.step 70 (.step 68 (.split 49 0 (.step 20 (.step 14 (.step 15 (.close 33)))) (.step 13 (.step 17 (.step 16 (.step 17 (.close 33))))))))) (.split 16 0 (.step 70 (.split 17 0 (.step 53 (.step 40 (.step 9 (.close 33)))) (.step 24 (.step 33 (.step 13 (.step 14 (.close 17))))))) (.step 33 (.split 17 0 (.step 24 (.step 33 (.step 53 (.step 14 (.close 20))))) (.split 34 0 (.step 53 (.close 20)) (.step 24 (.close 20))))))))) (.reuse 0))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1267650600228229401497776947200, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522245636211388939930912494398727523232622386843123772128346451948339200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 42 0 (.split 17 0 (.step 52 (.split 36 0 (.step 52 (.step 18 (.close 9))) (.step 54 (.step 52 (.step 9 (.close 18)))))) (.step 54 (.step 13 (.step 4 (.step 9 (.step 18 (.close 33))))))) (.step 70 (.split 17 0 (.step 52 (.split 35 0 (.step 71 (.step 13 (.step 15 (.close 16)))) (.step 13 (.step 33 (.step 9 (.close 15)))))) (.step 13 (.step 43 (.step 54 (.step 4 (.close 15)))))))) (.split 17 0 (.split 42 0 (.split 36 0 (.step 52 (.split 54 0 (.split 35 0 (.split 50 0 (.step 13 (.step 4 (.step 16 (.step 18 (.close 33))))) (.step 33 (.step 4 (.close 13)))) (.step 13 (.step 33 (.step 4 (.close 9))))) (.step 52 (.step 18 (.step 9 (.close 33)))))) (.step 13 (.step 54 (.step 38 (.step 43 (.step 16 (.step 4 (.close 33)))))))) (.step 13 (.step 68 (.step 70 (.step 33 (.step 15 (.step 16 (.close 38)))))))) (.step 13 (.split 35 0 (.step 54 (.step 24 (.step 14 (.step 23 (.close 25))))) (.step 24 (.close 19)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566053817933581204324352⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.split 22 0 (.reuse 1) (.run (.split 16 0 (.split 42 0 (.split 17 0 (.step 70 (.step 52 (.split 35 0 (.split 50 0 (.step 13 (.step 4 (.step 15 (.close 16)))) (.step 33 (.step 4 (.step 9 (.close 13))))) (.step 13 (.step 33 (.step 4 (.step 9 (.close 15)))))))) (.step 13 (.step 54 (.step 24 (.close 25))))) (.step 13 (.step 70 (.step 4 (.close 15))))) (.split 17 0 (.step 13 (.split 35 0 (.step 70 (.step 24 (.step 14 (.close 20)))) (.step 24 (.close 19)))) (.split 30 0 (.split 34 0 (.step 54 (.step 13 (.step 19 (.step 18 (.step 19 (.close 25)))))) (.step 13 (.step 17 (.step 14 (.close 20))))) (.step 13 (.step 19 (.step 20 (.step 17 (.close 24)))))))))) (.run (.split 16 0 (.split 34 0 (.split 22 0 (.split 42 0 (.step 52 (.split 30 0 (.step 15 (.step 4 (.close 18))) (.step 13 (.step 9 (.step 15 (.step 16 (.close 18))))))) (.step 13 (.step 62 (.step 13 (.step 9 (.step 15 (.close 16))))))) (.step 13 (.close 18))) (.step 13 (.step 52 (.close 15)))) (.step 13 (.step 52 (.step 53 (.step 13 (.close 4)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part3.excludes
end FiveColour.Packed.EnumerationChunks.Case57
