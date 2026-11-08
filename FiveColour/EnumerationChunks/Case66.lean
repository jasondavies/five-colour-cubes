module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case66
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453662941113829342651439877817257322135417574524641937045872157746694534288946432808933277465536114755911400920964114072031189935748241409746984106720047989867419204921619120128⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453662941113829342651439877817257322135417574524641937045872157746694534288946432808933277465536114755911400920964114072031189935748241409746984106720047989867419204921619120128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 0 (.split 38 0 (.split 50 0 (.split 22 0 (.step 39 (.step 14 (.close 38))) (.split 34 0 (.step 20 (.step 23 (.close 39))) (.split 36 0 (.step 25 (.step 14 (.close 43))) (.step 45 (.step 14 (.step 17 (.close 20))))))) (.step 33 (.step 43 (.step 45 (.step 17 (.close 19)))))) (.step 33 (.step 55 (.close 16)))) (.step 13 (.split 38 0 (.split 50 0 (.step 43 (.step 45 (.step 17 (.close 20)))) (.step 33 (.step 43 (.step 45 (.step 17 (.close 24)))))) (.step 33 (.step 43 (.close 16)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case66
