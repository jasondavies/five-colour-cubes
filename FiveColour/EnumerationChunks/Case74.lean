module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case74
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5136856365239144160511821461895676803098098203906065863435968310709567554884586152995250217751349323138580355361835765296975865335368111197387003884827978599168176226223504222468253027787886623592165461196800⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨37033564156298044177399, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497705040614186417671967029225310810172032001, 0⟩]
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
def root : Box := ⟨1073741824, 5136856365239144160511821461895676803098098203906065863435968310709567554884586152995250217751349323138580355361835765296975865335368111197385318888161281682684431861153720907310577437560004025684421561548800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 0 (.split 42 0 (.split 10 0 (.split 16 0 (.step 53 (.step 13 (.close 52))) (.split 30 0 (.split 34 0 (.step 52 (.close 53)) (.step 48 (.step 13 (.step 33 (.close 63))))) (.step 53 (.close 33)))) (.split 34 0 (.split 16 0 (.step 52 (.close 33)) (.split 30 0 (.step 48 (.step 13 (.step 33 (.close 52)))) (.step 13 (.close 33)))) (.step 52 (.step 13 (.close 33))))) (.step 70 (.split 16 0 (.split 30 0 (.step 13 (.step 33 (.close 52))) (.split 10 0 (.step 33 (.close 13)) (.step 13 (.step 15 (.step 16 (.close 33)))))) (.split 30 0 (.split 34 0 (.step 13 (.close 33)) (.split 49 0 (.step 40 (.step 15 (.step 33 (.close 59)))) (.step 13 (.step 16 (.step 33 (.close 48)))))) (.step 33 (.step 13 (.step 38 (.close 39)))))))) (.step 54 (.split 42 0 (.split 16 0 (.split 30 0 (.step 13 (.step 33 (.close 52))) (.split 10 0 (.step 33 (.close 13)) (.step 13 (.step 15 (.step 16 (.close 33)))))) (.split 30 0 (.split 34 0 (.step 13 (.close 33)) (.split 49 0 (.step 40 (.step 15 (.step 33 (.close 63)))) (.step 13 (.step 16 (.step 33 (.close 48)))))) (.step 33 (.step 13 (.step 38 (.close 40)))))) (.step 70 (.split 49 0 (.split 61 0 (.step 33 (.step 15 (.step 16 (.close 38)))) (.step 13 (.step 33 (.step 15 (.step 37 (.close 40)))))) (.step 13 (.step 33 (.step 16 (.step 37 (.close 38)))))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5136856365239144160511821461895676803098098203906065863435968310709567554884586152995250217751349323138580355361835765296975865335368111197387003884827978599168176226223504222468253027787886623592165461196800⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.step 70 (.split 36 0 (.split 16 0 (.split 30 0 (.step 13 (.step 33 (.close 52))) (.split 10 0 (.step 33 (.close 13)) (.step 13 (.close 33)))) (.split 30 0 (.split 34 0 (.step 13 (.close 33)) (.split 49 0 (.step 23 (.step 33 (.step 35 (.close 56)))) (.step 13 (.step 33 (.step 42 (.close 48)))))) (.step 33 (.step 13 (.step 14 (.close 17)))))) (.step 54 (.split 49 0 (.split 61 0 (.step 33 (.close 14)) (.step 13 (.step 33 (.close 14)))) (.step 13 (.step 33 (.step 16 (.close 17)))))))))) (.run (.split 36 0 (.split 22 0 (.step 54 (.split 42 0 (.split 16 0 (.split 30 0 (.step 13 (.step 33 (.close 52))) (.split 10 0 (.step 33 (.close 13)) (.step 13 (.close 33)))) (.split 30 0 (.split 34 0 (.step 13 (.close 33)) (.split 49 0 (.step 23 (.step 33 (.step 35 (.close 63)))) (.step 13 (.step 33 (.step 42 (.close 48)))))) (.step 33 (.step 13 (.step 14 (.close 17)))))) (.step 70 (.split 49 0 (.split 61 0 (.step 33 (.close 14)) (.step 13 (.step 33 (.close 14)))) (.step 13 (.step 33 (.step 16 (.close 17)))))))) (.step 70 (.step 54 (.split 49 0 (.split 61 0 (.step 33 (.close 14)) (.step 13 (.step 33 (.close 14)))) (.step 13 (.step 33 (.close 17))))))) (.step 54 (.step 13 (.step 14 (.step 17 (.close 20))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 10 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case74
