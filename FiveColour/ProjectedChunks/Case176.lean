module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case176
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 14696649931972027310843571465511426378529800594397885643846774004787226566457006452894916526441166105959274796878083024032763257889170649139427243860712026798093442278503856095699083516267738777836847104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨5368709120, 14696649931972027310843571465511426378529800594397885643846774004787226566457006452894916526441166105959274796878083024032763257889170649139427243860712026798093442278503856095699083516267738777836847104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 2 (.step 3 (.split 49 2 (.split 50 2 (.split 56 2 (.split 59 2 (.step 18 (.step 31 (.step 58 (.step 3 (.step 31 (.step 58 (.close 18))))))) (.step 58 (.split 16 1 (.split 17 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 56 1 (.step 62 (.step 3 (.step 31 (.close 18)))) (.step 31 (.close 62))) (.step 3 (.step 21 (.close 58)))) (.step 31 (.close 62))) (.step 31 (.close 52))) (.step 18 (.close 62))) (.step 18 (.close 53))))) (.step 18 (.step 58 (.split 49 1 (.split 59 1 (.split 38 1 (.step 31 (.step 3 (.step 5 (.close 58)))) (.step 28 (.step 32 (.close 41)))) (.step 31 (.close 58))) (.step 31 (.close 58)))))) (.step 32 (.step 58 (.step 53 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.step 62 (.split 42 1 (.split 56 1 (.step 53 (.step 3 (.step 18 (.close 31)))) (.step 31 (.close 53))) (.step 31 (.close 52)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 18 (.close 53))) (.step 18 (.close 53))) (.step 18 (.close 53))))))) (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 16 0 (.step 52 (.step 3 (.close 31))) (.step 3 (.close 52))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 31 (.step 52 (.close 58)))) (.step 31 (.close 52))) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 18 (.close 52)))))) (.step 32 (.step 58 (.split 49 1 (.step 41 (.step 3 (.step 18 (.split 59 1 (.step 28 (.step 41 (.step 3 (.close 31)))) (.step 3 (.close 41)))))) (.step 3 (.step 41 (.close 58))))))))
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
end FiveColour.Packed.ProjectedChunks.Case176
