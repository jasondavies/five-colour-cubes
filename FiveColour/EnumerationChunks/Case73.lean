module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case73
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510724716875129052021434112103325415711342535343422895103095152999653711524920626245062089790515471173127200915212874054809533952649712454753340311745527482971840715897700352⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨32908989162382549646327, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910785812665766745799411394960843444438804532254114131948159551483306040611339819323235465820198712900767369397249, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510724716875129052021434112103325415711342535343422895103095152999653711524920626245062089790515471173127200915212874054809533952649712454753340311745527482971840715897700352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 17 0 (.step 45 (.step 17 (.close 38))) (.split 34 0 (.step 20 (.step 24 (.close 39))) (.split 42 0 (.step 20 (.step 17 (.close 39))) (.step 39 (.step 17 (.step 24 (.close 25))))))) (.step 33 (.split 17 0 (.step 45 (.close 15)) (.step 39 (.step 15 (.step 17 (.close 19))))))))
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
end FiveColour.Packed.EnumerationChunks.Case73
