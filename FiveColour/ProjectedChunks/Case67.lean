module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case67
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5521043902411107294593881026267861162954266424668942486879726167861545064022386483652928352373188539320306604199899017024744868354957540803369070922092748542494720303926633030048623604700811588304558675670378001467394⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨29191945437477171357596, 5521043902401079285245703114100180852279210293007498667362342662451989309891209519920913575728470360496566372743279221332644914408349027465516502697126662802532669500995196218211056214004383628402023813341810817762305, 0⟩]
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
def root : Box := ⟨2, 5521043902411107294593881026267861162954266424668942486879726167861545064022386483652928352373188539320306604199899017024744868354957540803369070922092748542494720303926633030048623604700811588304558675670378001467394⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 4 (.split 21 1 (.step 71 (.split 37 1 (.split 45 1 (.split 5 0 (.split 6 0 (.step 31 (.close 4)) (.step 4 (.close 15))) (.step 4 (.close 14))) (.step 4 (.close 18))) (.step 4 (.close 23)))) (.step 18 (.close 24)))))
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
end FiveColour.Packed.ProjectedChunks.Case67
