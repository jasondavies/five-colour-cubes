module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case243
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566053817933581204324352⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩]
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288766217298965825588532084501118976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 42 0 (.split 17 0 (.split 16 0 (.split 30 0 (.split 34 0 (.step 9 (.step 53 (.close 13))) (.step 15 (.step 9 (.step 16 (.close 18))))) (.step 53 (.step 9 (.step 15 (.step 13 (.close 18)))))) (.step 53 (.step 4 (.step 9 (.close 13))))) (.step 54 (.split 12 0 (.step 48 (.step 4 (.close 9))) (.step 13 (.step 4 (.step 9 (.close 14))))))) (.step 70 (.split 17 0 (.split 16 0 (.step 62 (.step 18 (.step 9 (.close 13)))) (.step 53 (.step 4 (.close 13)))) (.step 54 (.step 24 (.step 4 (.close 13))))))) (.split 30 0 (.split 34 0 (.split 17 0 (.step 70 (.step 62 (.close 4))) (.step 54 (.step 62 (.step 4 (.close 13))))) (.step 70 (.step 68 (.step 20 (.close 13))))) (.split 17 0 (.step 70 (.step 53 (.step 4 (.step 9 (.close 13))))) (.step 33 (.step 24 (.step 33 (.step 54 (.step 13 (.step 14 (.close 17)))))))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566053817933581204324352⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 22 0 (.split 17 0 (.split 36 0 (.step 52 (.split 54 0 (.split 16 0 (.step 52 (.step 9 (.close 18))) (.step 13 (.step 38 (.step 18 (.step 15 (.step 16 (.close 33))))))) (.step 52 (.step 18 (.step 9 (.close 33)))))) (.step 54 (.step 13 (.step 52 (.step 53 (.step 4 (.close 9))))))) (.step 54 (.step 13 (.step 24 (.step 4 (.step 9 (.close 15))))))) (.split 16 0 (.step 70 (.step 13 (.step 24 (.step 15 (.step 4 (.close 9)))))) (.step 13 (.split 35 0 (.step 70 (.step 24 (.step 14 (.close 19)))) (.step 24 (.close 19)))))) (.split 34 0 (.split 17 0 (.split 22 0 (.step 52 (.split 16 0 (.step 15 (.close 13)) (.step 13 (.close 4)))) (.step 13 (.step 4 (.close 18)))) (.step 13 (.step 4 (.close 18)))) (.step 13 (.step 15 (.close 13)))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case243
