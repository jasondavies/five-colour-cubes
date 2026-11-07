module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case147
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894694338784041077850061632276271769430463186721765578496247941925844636498116214784⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908392998381807266807, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699534968387178292612729254500242869083702273, 0⟩]
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
def root : Box := ⟨4294967296, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935468507708830564910555300649607096058471256779275641991190886353993728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 1 (.step 3 (.split 21 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 54 1 (.step 3 (.step 18 (.close 26))) (.step 9 (.step 31 (.step 26 (.close 57))))) (.step 18 (.close 29))) (.step 18 (.close 21))) (.step 26 (.split 16 0 (.step 26 (.step 3 (.step 18 (.close 31)))) (.step 18 (.close 12))))) (.step 53 (.split 54 1 (.split 16 0 (.split 17 0 (.step 9 (.step 21 (.step 3 (.step 18 (.close 26))))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 9 (.step 21 (.step 32 (.close 57))))))) (.step 52 (.split 54 1 (.split 16 0 (.split 17 0 (.step 9 (.step 31 (.step 12 (.step 3 (.step 18 (.close 26)))))) (.step 3 (.close 40))) (.step 3 (.close 40))) (.step 57 (.close 3))))) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 21 (.step 29 (.step 31 (.step 38 (.split 34 0 (.step 21 (.step 18 (.step 12 (.step 18 (.close 26))))) (.step 3 (.close 38)))))))) (.step 31 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.step 57 (.step 3 (.step 18 (.close 31))))))) (.step 12 (.step 21 (.step 22 (.step 9 (.step 15 (.step 3 (.step 18 (.step 31 (.step 15 (.split 35 1 (.split 50 1 (.step 18 (.close 15)) (.step 15 (.close 3))) (.step 15 (.close 3))))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071069493960511744270264372286555483209881573866190262853298150857341065702841827532594041426795804400280706049261587461738816319859172219655235601757634560⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 2 (.split 54 2 (.split 59 2 (.split 72 2 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 12 1 (.step 3 (.step 18 (.split 49 1 (.step 29 (.step 18 (.step 26 (.step 18 (.close 12))))) (.step 12 (.step 27 (.step 29 (.step 26 (.close 52)))))))) (.step 15 (.step 18 (.step 15 (.close 3)))))))) (.run (.step 29 (.step 31 (.step 38 (.split 12 1 (.step 3 (.step 18 (.step 75 (.step 18 (.close 12))))) (.step 15 (.close 18)))))))) (.run (.step 26 (.step 62 (.split 26 1 (.split 12 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 16 1 (.split 42 1 (.split 54 1 (.step 18 (.step 62 (.close 3))) (.step 22 (.step 26 (.step 57 (.close 3))))) (.step 31 (.close 12))) (.step 18 (.close 12))) (.step 31 (.close 12))) (.step 21 (.step 26 (.step 29 (.step 40 (.step 31 (.close 12))))))) (.step 15 (.close 31))) (.step 15 (.close 62))) (.step 26 (.step 27 (.step 29 (.close 62))))))))) (.run (.step 21 (.step 22 (.step 26 (.step 32 (.step 57 (.close 3)))))))) (.run (.step 3 (.step 21 (.step 57 (.step 62 (.split 72 2 (.split 26 1 (.split 12 1 (.split 21 1 (.split 34 1 (.step 53 (.split 36 1 (.split 42 1 (.split 54 1 (.step 18 (.step 53 (.step 3 (.close 29)))) (.step 53 (.close 31))) (.step 31 (.close 12))) (.step 31 (.close 12)))) (.step 31 (.close 52))) (.step 18 (.close 53))) (.step 15 (.close 53))) (.step 27 (.step 52 (.step 57 (.split 10 0 (.split 12 0 (.step 29 (.close 3)) (.step 12 (.step 15 (.step 29 (.close 3))))) (.step 3 (.close 29))))))) (.step 26 (.step 29 (.step 31 (.step 40 (.step 53 (.close 75)))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894694338784041077850061632276271769430463186721765578496247941925844636498116214784⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 12 2 (.step 18 (.split 21 2 (.split 35 2 (.split 49 2 (.reuse 0) (.run (.step 3 (.step 12 (.step 57 (.step 62 (.split 72 2 (.split 26 1 (.split 21 1 (.split 34 1 (.step 53 (.split 35 1 (.split 36 1 (.split 42 1 (.split 54 1 (.step 18 (.step 52 (.step 12 (.close 18)))) (.step 12 (.step 18 (.step 52 (.close 31))))) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 12 (.step 21 (.step 29 (.step 31 (.step 40 (.step 52 (.close 26))))))))) (.step 31 (.close 52))) (.step 18 (.close 52))) (.step 12 (.step 27 (.step 52 (.step 57 (.step 29 (.close 3))))))) (.step 26 (.step 29 (.step 31 (.step 38 (.step 40 (.step 52 (.close 57)))))))))))))) (.run (.step 21 (.step 29 (.step 38 (.step 57 (.step 62 (.split 49 2 (.split 59 1 (.split 12 1 (.step 3 (.step 18 (.step 38 (.step 3 (.close 18))))) (.step 15 (.close 18))) (.step 3 (.step 15 (.step 26 (.step 38 (.step 18 (.close 62))))))) (.step 12 (.step 40 (.step 52 (.step 57 (.step 38 (.close 3)))))))))))))) (.run (.step 3 (.step 18 (.step 29 (.step 31 (.step 57 (.step 18 (.step 9 (.step 15 (.step 57 (.step 62 (.step 75 (.split 50 2 (.split 35 1 (.split 49 1 (.step 24 (.split 59 1 (.step 24 (.step 18 (.step 24 (.close 29)))) (.step 3 (.step 18 (.close 12))))) (.step 18 (.close 52))) (.step 18 (.close 38))) (.step 18 (.close 53))))))))))))))))) (.run (.step 15 (.step 18 (.step 21 (.step 15 (.step 3 (.step 15 (.step 3 (.close 24))))))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case147
