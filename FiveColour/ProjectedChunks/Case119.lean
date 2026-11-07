module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case119
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230375543532174150625387156064302336309976247134027606030268685309285458998961134574761878735186269371551971539664993923018953571709018877526094323523971682310476412947901977915817984⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230375543532174150625387156064302336309976247134027606030268685309285458998961134574761878735186269371551971539664993923018953571709018877526094323523971682310476412947901977915817984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.step 3 (.step 7 (.close 46))) (.step 7 (.close 45))) (.step 7 (.close 39))) (.step 3 (.step 38 (.step 45 (.split 36 1 (.step 3 (.step 29 (.close 38))) (.step 29 (.close 39))))))) (.step 7 (.step 37 (.step 38 (.step 7 (.step 37 (.close 3))))))) (.step 3 (.step 29 (.close 3)))) (.split 26 1 (.step 7 (.close 18)) (.step 18 (.close 29)))) (.split 22 1 (.split 26 1 (.step 7 (.close 18)) (.step 18 (.close 29))) (.step 7 (.close 18)))) (.split 17 1 (.split 22 1 (.split 26 1 (.step 7 (.close 18)) (.step 18 (.close 29))) (.step 7 (.close 18))) (.step 18 (.step 7 (.close 19))))))
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
end FiveColour.Packed.ProjectedChunks.Case119
