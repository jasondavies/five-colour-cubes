module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case229
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566054970855085811171328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32016031753816174816183, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986200052311922515709018284938770805055030273, 0⟩]
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714805485858522247321208055636845899661087170463288767484949566054970855085811171328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 22 0 (.split 42 0 (.split 6 0 (.split 16 0 (.split 30 0 (.split 34 0 (.step 9 (.close 71)) (.step 15 (.close 39))) (.step 53 (.step 9 (.close 39)))) (.step 53 (.step 4 (.close 17)))) (.step 46 (.split 61 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))))) (.step 70 (.split 6 0 (.split 12 0 (.split 49 0 (.step 39 (.close 4)) (.step 13 (.step 39 (.close 4)))) (.step 13 (.step 43 (.close 18)))) (.step 7 (.close 9))))) (.split 30 0 (.split 34 0 (.split 17 0 (.step 62 (.step 68 (.step 4 (.close 24)))) (.step 7 (.step 54 (.step 4 (.close 24))))) (.step 7 (.step 68 (.step 70 (.close 20))))) (.step 7 (.step 70 (.step 33 (.step 24 (.close 4))))))) (.split 6 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 52 (.step 9 (.close 53))) (.step 54 (.step 13 (.step 15 (.close 53))))) (.step 70 (.step 13 (.step 15 (.close 43))))) (.step 54 (.step 13 (.step 54 (.step 24 (.close 4)))))) (.step 7 (.close 9)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case229
