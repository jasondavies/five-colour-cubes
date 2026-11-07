module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case156
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894686928090329889613554523733231213404360577442746977500149416640468130057819258880⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908392998381874375671, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449, 0⟩]
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
def root : Box := ⟨4294967296, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954774974593011969728447743257215999410176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 72 1 (.step 3 (.step 18 (.close 31))) (.step 26 (.step 3 (.close 12)))) (.step 18 (.close 57))) (.step 18 (.close 57))) (.split 16 0 (.split 17 0 (.step 26 (.step 3 (.step 18 (.close 31)))) (.step 3 (.close 62))) (.step 3 (.close 62)))) (.split 16 0 (.step 62 (.split 54 1 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.step 21 (.step 3 (.close 26)))) (.step 3 (.close 12))) (.step 3 (.close 26))) (.step 18 (.close 12))) (.step 57 (.close 3)))) (.step 3 (.close 21)))) (.split 16 0 (.step 52 (.split 54 1 (.split 17 0 (.split 21 0 (.step 52 (.step 12 (.step 3 (.close 26)))) (.step 12 (.close 18))) (.step 3 (.close 40))) (.step 57 (.close 3)))) (.step 3 (.step 21 (.step 12 (.close 18)))))) (.step 31 (.close 62))) (.step 31 (.close 57))) (.step 21 (.step 31 (.split 49 1 (.split 54 1 (.split 59 1 (.split 16 0 (.step 29 (.step 38 (.step 3 (.close 38)))) (.step 18 (.close 21))) (.step 21 (.step 26 (.close 31)))) (.step 57 (.close 3))) (.step 9 (.step 12 (.step 21 (.step 40 (.step 38 (.step 26 (.close 31))))))))))) (.step 31 (.close 52))) (.step 18 (.close 26))) (.step 18 (.step 31 (.step 57 (.step 3 (.split 49 1 (.step 18 (.close 31)) (.step 12 (.close 18)))))))) (.step 18 (.close 22))) (.step 18 (.close 21)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071062947179295951986524345907161828011577140582098176723719184274604873435241607489773086650104044048925848249790723062578196889247555163492622504405499904⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 54 2 (.split 59 2 (.split 72 2 (.split 12 1 (.reuse 0) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.step 9 (.step 15 (.step 3 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.step 15 (.split 50 1 (.step 18 (.step 12 (.step 3 (.close 15)))) (.step 12 (.step 15 (.close 3))))) (.step 26 (.step 3 (.close 15)))) (.step 15 (.close 31))) (.step 15 (.close 31))) (.step 15 (.close 3)))))))))))) (.run (.step 31 (.step 75 (.split 12 1 (.split 22 1 (.step 29 (.split 49 1 (.split 50 1 (.split 51 1 (.split 16 1 (.split 17 1 (.step 75 (.step 3 (.close 18))) (.step 18 (.close 22))) (.step 18 (.close 21))) (.step 3 (.close 57))) (.step 3 (.step 40 (.step 57 (.close 75))))) (.step 12 (.step 26 (.step 40 (.step 57 (.step 52 (.close 75)))))))) (.step 18 (.close 26))) (.step 15 (.close 75))))))) (.run (.step 26 (.step 62 (.split 12 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 54 1 (.split 12 0 (.step 18 (.split 16 0 (.step 62 (.close 3)) (.step 3 (.close 62)))) (.step 26 (.step 62 (.close 3)))) (.step 57 (.close 62))) (.step 31 (.close 57))) (.step 9 (.step 21 (.step 26 (.step 40 (.step 31 (.step 57 (.close 62)))))))) (.step 15 (.step 31 (.close 52)))) (.step 18 (.close 62))) (.step 15 (.close 62))))))) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.step 32 (.step 57 (.close 3)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071069500353852775317416462156066609826286168039319259031159067816894519015595737941762843196675594931271706958484533119360979013638101125461137468742959104⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 2 (.split 50 2 (.reuse 0) (.run (.step 57 (.step 62 (.split 72 2 (.split 12 1 (.split 21 1 (.split 34 1 (.split 36 1 (.step 53 (.split 42 1 (.split 17 1 (.split 54 1 (.split 72 1 (.split 12 0 (.step 18 (.step 53 (.close 3))) (.step 26 (.step 53 (.close 3)))) (.step 26 (.step 53 (.close 3)))) (.step 53 (.close 31))) (.step 18 (.close 22))) (.step 31 (.close 53)))) (.step 31 (.close 53))) (.step 15 (.step 31 (.close 52)))) (.step 18 (.close 53))) (.step 15 (.close 53))) (.step 21 (.step 26 (.step 31 (.step 40 (.step 57 (.split 12 0 (.step 53 (.close 31)) (.step 15 (.step 53 (.close 57)))))))))))))) (.run (.step 57 (.step 62 (.split 72 2 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.step 53 (.split 42 1 (.split 17 1 (.split 54 1 (.split 72 1 (.split 12 0 (.step 18 (.split 16 0 (.step 52 (.close 3)) (.step 3 (.close 52)))) (.step 12 (.step 3 (.step 18 (.close 15))))) (.step 12 (.step 26 (.step 52 (.close 3))))) (.step 12 (.step 26 (.step 52 (.close 31))))) (.step 18 (.close 22))) (.step 31 (.close 52)))) (.step 31 (.close 52))) (.step 12 (.step 31 (.step 55 (.step 52 (.step 26 (.step 52 (.close 38)))))))) (.step 31 (.close 52))) (.step 18 (.close 52))) (.step 12 (.step 26 (.step 31 (.step 38 (.step 40 (.step 57 (.step 52 (.close 75)))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894686928090329889613554523733231213404360577442746977500149416640468130057819258880⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 12 2 (.step 18 (.split 21 2 (.split 35 2 (.reuse 0) (.run (.step 21 (.step 31 (.step 57 (.step 75 (.split 49 2 (.split 59 2 (.split 12 1 (.split 16 1 (.step 29 (.split 49 1 (.split 54 1 (.step 3 (.step 18 (.step 38 (.step 3 (.close 18))))) (.step 38 (.close 57))) (.step 3 (.step 12 (.step 40 (.step 38 (.step 26 (.step 38 (.close 52))))))))) (.step 18 (.close 21))) (.step 15 (.close 38))) (.step 3 (.step 9 (.step 26 (.step 40 (.step 52 (.step 57 (.split 12 0 (.step 38 (.close 62)) (.step 12 (.step 15 (.step 38 (.close 57)))))))))))) (.step 12 (.step 40 (.step 52 (.step 57 (.split 36 0 (.step 52 (.close 26)) (.step 31 (.close 38)))))))))))))) (.run (.step 31 (.split 50 2 (.split 59 2 (.split 72 2 (.split 54 1 (.split 35 1 (.split 49 1 (.step 24 (.step 9 (.step 15 (.step 3 (.step 18 (.close 12)))))) (.step 3 (.step 12 (.step 18 (.close 52))))) (.step 15 (.step 18 (.close 38)))) (.step 24 (.close 57))) (.step 18 (.step 38 (.step 24 (.step 57 (.close 75)))))) (.step 15 (.step 18 (.step 57 (.close 62))))) (.step 18 (.step 53 (.step 24 (.close 57))))))))) (.run (.step 15 (.step 18 (.step 21 (.step 22 (.step 15 (.step 3 (.step 15 (.step 3 (.close 24)))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case156
