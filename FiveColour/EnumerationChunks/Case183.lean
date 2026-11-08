module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case183
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895700802803279209044463565250435826431802399782427750682958173030522736212200164190975978218718620474601171949370906567219166250139238367774664219721329030719744001651996983038050304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨37631355645286554598391, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969542117842042700880638937423209499416432818949836275778454799724524958750082049, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895700802803279209044463565250435826431802399782427750682958173030522736212200164190975978218718620474601171949370906567219166250139238367774664219721329030719744001651996983038050304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.close 7))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 10 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case183
