module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case71
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510728490837553873562786353657906403980233452264643311543525991831341231804033785833920434893103466315599146474004651586992199080845060955209186264820709222895434779542421504⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510728490837553873562786353657906403980233452264643311543525991831341231804033785833920434893103466315599146474004651586992199080845060955209186264820709222895434779542421504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 38 0 (.split 17 0 (.split 22 0 (.step 54 (.close 38)) (.step 45 (.step 14 (.step 17 (.step 20 (.close 39)))))) (.split 34 0 (.split 42 0 (.step 20 (.step 23 (.close 39))) (.split 22 0 (.step 39 (.close 23)) (.step 25 (.close 20)))) (.split 42 0 (.split 51 0 (.step 20 (.step 17 (.close 39))) (.step 39 (.close 20))) (.step 39 (.step 25 (.close 45)))))) (.step 33 (.split 17 0 (.split 51 0 (.step 45 (.close 5)) (.step 39 (.step 45 (.close 5)))) (.step 39 (.step 23 (.close 5)))))) (.step 33 (.split 17 0 (.split 51 0 (.step 45 (.close 4)) (.step 39 (.step 45 (.close 4)))) (.step 39 (.step 24 (.close 4)))))))
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
end FiveColour.Packed.EnumerationChunks.Case71
