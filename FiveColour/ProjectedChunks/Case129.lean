module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case129
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11042077284530345666400295095934218182855607339481135141560308214453581629174337143603411657620135526559279515809342077779379562293075826737592812950268498632624222848094986902060983433202727000067564190973361198727171⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨30666541081021128896446, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124037639541146111563493128984644470311576664498607971097082070547331612438551329471180924412418929488251918999356417, 0⟩]
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
def root : Box := ⟨3, 11042077284530345666400295095934218182855607339481135141560308214453581629174337143603411657620135526559279515809342077779379562293075826737592812950268498632624222848094986902060983433202727000067564190973361198727171⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 29 (.step 38 (.step 75 (.split 40 1 (.split 60 1 (.split 6 1 (.split 12 1 (.split 34 1 (.step 74 (.split 36 1 (.split 40 0 (.step 66 (.step 57 (.step 33 (.step 18 (.close 57))))) (.step 4 (.step 45 (.step 24 (.step 33 (.close 55)))))) (.step 39 (.close 6)))) (.step 37 (.close 39))) (.step 37 (.step 66 (.split 36 1 (.step 15 (.step 33 (.step 15 (.close 39)))) (.step 37 (.close 39)))))) (.step 9 (.split 34 1 (.split 36 1 (.split 63 1 (.split 64 1 (.split 42 1 (.step 47 (.step 9 (.close 15))) (.step 7 (.step 18 (.step 24 (.close 74))))) (.step 47 (.step 67 (.close 9)))) (.step 47 (.close 66))) (.step 7 (.step 18 (.close 39)))) (.step 7 (.step 18 (.close 37)))))) (.step 4 (.step 66 (.step 67 (.step 74 (.split 6 1 (.split 12 1 (.split 34 1 (.step 63 (.step 39 (.step 18 (.step 21 (.close 33))))) (.step 18 (.close 37))) (.step 15 (.close 18))) (.step 9 (.close 18)))))))) (.step 4 (.step 37 (.step 39 (.step 45 (.split 6 1 (.split 12 1 (.split 54 1 (.split 63 1 (.step 43 (.step 19 (.step 24 (.close 25)))) (.step 37 (.step 43 (.close 66)))) (.step 24 (.close 43))) (.step 15 (.close 24))) (.step 9 (.close 24))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case129
