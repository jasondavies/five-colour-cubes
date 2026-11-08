module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case141
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138616295348838291474619014303080011166238158583507622542987956278234238226006016⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨18741817655939024337635, 5789228615351851010618494880448709935079879776571393911013839255768432665236912487960502774861810452465697322629129481734798338504805576798767767746958544377551056015095924842852531572048546471937896452059573376945140794368, 0⟩]
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
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260032287596181804130209080392603065240853251611617498908111372457741590451520073839784057896960⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 7 (.split 42 1 (.split 43 1 (.step 7 (.close 5)) (.step 7 (.close 3))) (.step 7 (.close 5)))) (.split 42 1 (.step 5 (.step 7 (.step 10 (.split 51 1 (.step 7 (.step 5 (.close 7))) (.step 3 (.close 7)))))) (.step 7 (.step 5 (.close 28))))) (.step 7 (.step 45 (.step 7 (.step 5 (.close 28)))))) (.step 7 (.step 45 (.split 74 1 (.step 37 (.step 7 (.step 5 (.close 28)))) (.step 5 (.step 7 (.step 5 (.step 28 (.close 37))))))))) (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 16 0 (.step 28 (.step 5 (.step 7 (.close 5)))) (.step 5 (.step 7 (.close 5)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 10)))) (.step 3 (.step 7 (.close 10)))) (.step 7 (.step 28 (.close 3)))) (.step 7 (.step 28 (.close 3)))) (.step 7 (.step 28 (.close 3))))) (.step 7 (.close 5))) (.step 7 (.step 5 (.step 8 (.step 5 (.close 28)))))) (.step 7 (.split 25 1 (.split 38 1 (.step 20 (.step 7 (.step 5 (.close 8)))) (.step 5 (.step 7 (.step 5 (.step 8 (.step 5 (.close 19))))))) (.step 5 (.step 7 (.step 5 (.step 8 (.step 19 (.step 5 (.close 28)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260032287596181804130209080392603065240853251611617500301907947365905538006428285494935826726912⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.split 14 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 5 (.step 7 (.split 42 1 (.step 7 (.step 27 (.split 51 1 (.step 7 (.step 5 (.close 7))) (.step 3 (.close 7))))) (.step 5 (.close 7))))) (.step 3 (.step 5 (.close 28)))) (.step 5 (.step 7 (.step 5 (.step 28 (.close 37)))))) (.step 5 (.step 7 (.step 29 (.step 5 (.close 37)))))) (.step 3 (.step 5 (.close 28)))) (.step 7 (.step 5 (.close 8)))) (.step 7 (.step 20 (.step 7 (.step 5 (.close 8)))))) (.step 7 (.step 19 (.step 7 (.step 5 (.close 8)))))))) (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.step 11 (.step 7 (.close 5))) (.step 3 (.step 5 (.close 8)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 5 (.close 7))) (.step 3 (.step 5 (.step 67 (.step 5 (.close 28)))))) (.step 5 (.step 7 (.step 5 (.step 29 (.step 5 (.step 39 (.step 5 (.close 11))))))))) (.step 5 (.step 7 (.step 29 (.step 5 (.step 37 (.step 5 (.close 11)))))))) (.step 3 (.step 5 (.step 29 (.split 14 1 (.step 5 (.close 28)) (.step 5 (.close 8))))))) (.step 7 (.step 8 (.step 7 (.close 11))))) (.step 7 (.step 8 (.step 7 (.close 11))))) (.step 7 (.step 8 (.close 11))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138616295348838291474619014303080011166238158583507622542987956278234238226006016⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 2 1 (.reuse 0) (.run (.step 3 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 5 (.step 3 (.step 5 (.step 28 (.step 37 (.close 39)))))) (.step 3 (.step 5 (.close 8)))) (.step 3 (.step 5 (.step 8 (.close 19))))) (.step 5 (.step 8 (.close 17)))) (.step 5 (.close 8)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part2.excludes
end FiveColour.Packed.EnumerationChunks.Case141
