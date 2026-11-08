module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case80
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947850401401639604522231782625217913215901199891213875341479086515261368106100082095487989109359310237300585974685453283609583125069619183887332109860664515359872000825998491519025152⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 9⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947850401401639604522231782625217913215901199891213875341479086515261368106100082095487989109359310237300585974685453283609583125069619183887332109860664515359872000825998491519025152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.step 39 (.step 45 (.step 20 (.step 25 (.close 54))))) (.split 22 0 (.step 39 (.step 54 (.step 25 (.step 45 (.close 70))))) (.split 17 0 (.step 45 (.step 20 (.step 25 (.close 70)))) (.step 20 (.close 25))))))
theorem accepted : Fast.check 9 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 9 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 9 families root :=
  Fast.check_sound 9 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 9 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case80
